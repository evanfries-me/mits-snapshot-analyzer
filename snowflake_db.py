"""
Snowflake connectivity for the MITS Snapshot Analyzer.

Credentials come from the .env file / environment. Everything here degrades
gracefully: if Snowflake isn't configured the app keeps working as an S3
browser, and the UI just hides the enrichment.

Read-only by design — `query()` refuses anything that isn't a single
SELECT/WITH/SHOW/DESCRIBE statement, and callers must use bind parameters
rather than string-formatted SQL.
"""

import os
import hashlib
import json
import threading
import time
from datetime import datetime, timezone

import boto3
from boto3.dynamodb.conditions import Key

try:
    import snowflake.connector
    from snowflake.connector import DictCursor
    _DRIVER = True
except ImportError:                                  # pragma: no cover
    _DRIVER = False


# ── Configuration ─────────────────────────────────────────────────────────────

ENV_KEYS = (
    'SNOWFLAKE_ACCOUNT', 'SNOWFLAKE_USER', 'SNOWFLAKE_PASSWORD',
    'SNOWFLAKE_AUTHENTICATOR', 'SNOWFLAKE_PRIVATE_KEY_PATH',
    'SNOWFLAKE_PRIVATE_KEY_PASSPHRASE', 'SNOWFLAKE_TOKEN',
    'SNOWFLAKE_ROLE', 'SNOWFLAKE_WAREHOUSE',
    'SNOWFLAKE_DATABASE', 'SNOWFLAKE_SCHEMA',
)

# Building metadata source, overridable without touching code.
BUILDING_TABLE = os.environ.get(
    'SNOWFLAKE_BUILDING_TABLE', 'fanscan_public.building_details')
# building_details carries ORGANIZATION_ID but no org name; this table supplies it.
ORG_TABLE = os.environ.get(
    'SNOWFLAKE_ORG_TABLE', 'fanscan_public.organization')
DYNAMODB_ROLLOUT_TABLE = os.environ.get('DYNAMODB_ROLLOUT_TABLE', 'tracked-rollouts')
DYNAMODB_REGION = os.environ.get('AWS_REGION', 'us-west-2')

# Applications launch state is sourced from the product tables rather than a
# denormalized flag on building_details.
APPLICATIONS_BUILDING_TABLE = os.environ.get(
    'SNOWFLAKE_APPLICATIONS_BUILDING_TABLE', 'ELISE.DA.STG_BUILDING_DETAILS')
APPLICATIONS_PRODUCT_TABLE = os.environ.get(
    'SNOWFLAKE_APPLICATIONS_PRODUCT_TABLE', 'ELISE.DA.STG_BUILDING_PRODUCT')
APPLICATIONS_ORG_TABLE = os.environ.get(
    'SNOWFLAKE_APPLICATIONS_ORG_TABLE', 'ELISE.DA.STG_ORGANIZATION')

# Columns worth returning for enrichment — building_details has 200+, and
# selecting them all for 500 results makes the payload needlessly large.
DETAIL_COLUMNS = ('BUILDING_NAME', 'ORGANIZATION_ID', 'ACTIVE', 'CITY',
                  'STATE', 'POSTAL_CODE', 'TOTAL_UNITS', 'SLUG',
                  'EXCLUDE_NOT_RENT_READY_UNITS')

# Fivetran soft-delete flag present on both tables.
_LIVE = 'COALESCE({alias}._FIVETRAN_DELETED, FALSE) = FALSE'

QUERY_TIMEOUT = int(os.environ.get('SNOWFLAKE_QUERY_TIMEOUT', '120'))

_conn = None
_lock = threading.Lock()
_dynamo_table = None
_dynamo_lock = threading.Lock()

# Reasons the last connection attempt failed, surfaced to the UI for debugging.
_last_error = None


def credential_error(message) -> bool:
    """Return True for configuration/auth failures, not ordinary outages."""
    text = str(message or '').lower()
    if 'not configured' in text or 'missing snowflake_' in text:
        return True
    markers = (
        'authentication', 'authenticator', 'invalid username', 'invalid password',
        'password is incorrect', 'login failed', 'programmatic access token',
        'access token', 'token is invalid', '250001', '390100', '390111',
        'not authorized', 'incorrect username',
    )
    return any(marker in text for marker in markers)


def _env(key, default=''):
    value = (os.environ.get(key) or default).strip()
    # Tolerate values that arrive still wrapped in quotes.
    if len(value) >= 2 and value[0] == value[-1] and value[0] in ('"', "'"):
        value = value[1:-1].strip()
    if not value and key == 'SNOWFLAKE_TOKEN':
        # Accept the more common SNOWFLAKE_ACCESS_TOKEN spelling too.
        return _env('SNOWFLAKE_ACCESS_TOKEN')
    return value


def configured() -> bool:
    """True when enough is set to attempt a connection."""
    if not _DRIVER:
        return False
    if not (_env('SNOWFLAKE_ACCOUNT') and _env('SNOWFLAKE_USER')):
        return False
    return bool(
        _env('SNOWFLAKE_PASSWORD')
        or _env('SNOWFLAKE_PRIVATE_KEY_PATH')
        or _env('SNOWFLAKE_TOKEN')
        or _env('SNOWFLAKE_AUTHENTICATOR')
    )


def missing_keys():
    """Which required settings are absent — for a helpful UI message."""
    if not _DRIVER:
        return ['snowflake-connector-python (not installed)']
    missing = []
    if not _env('SNOWFLAKE_ACCOUNT'):
        missing.append('SNOWFLAKE_ACCOUNT')
    if not _env('SNOWFLAKE_USER'):
        missing.append('SNOWFLAKE_USER')
    if not (_env('SNOWFLAKE_PASSWORD') or _env('SNOWFLAKE_PRIVATE_KEY_PATH')
            or _env('SNOWFLAKE_TOKEN') or _env('SNOWFLAKE_AUTHENTICATOR')):
        missing.append('SNOWFLAKE_PASSWORD (or _PRIVATE_KEY_PATH / _TOKEN / _AUTHENTICATOR)')
    return missing


def _private_key_bytes():
    """Load and decrypt a PEM private key for key-pair auth."""
    from cryptography.hazmat.backends import default_backend
    from cryptography.hazmat.primitives import serialization

    path = os.path.expanduser(_env('SNOWFLAKE_PRIVATE_KEY_PATH'))
    passphrase = _env('SNOWFLAKE_PRIVATE_KEY_PASSPHRASE') or None

    with open(path, 'rb') as fh:
        key = serialization.load_pem_private_key(
            fh.read(),
            password=passphrase.encode() if passphrase else None,
            backend=default_backend(),
        )
    return key.private_bytes(
        encoding=serialization.Encoding.DER,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    )


def _build_params():
    params = {
        'account': _env('SNOWFLAKE_ACCOUNT'),
        'user':    _env('SNOWFLAKE_USER'),
        'client_session_keep_alive': True,
        'network_timeout': QUERY_TIMEOUT,
    }
    for env_key, param in (
        ('SNOWFLAKE_ROLE', 'role'),
        ('SNOWFLAKE_WAREHOUSE', 'warehouse'),
        ('SNOWFLAKE_DATABASE', 'database'),
        ('SNOWFLAKE_SCHEMA', 'schema'),
    ):
        if _env(env_key):
            params[param] = _env(env_key)

    authenticator = _env('SNOWFLAKE_AUTHENTICATOR')
    token = _env('SNOWFLAKE_TOKEN')
    pat_aliases = ('programmatic_access_token', 'pat')

    if _env('SNOWFLAKE_PRIVATE_KEY_PATH'):
        params['private_key'] = _private_key_bytes()
    elif token:
        # A Programmatic Access Token is presented as a plain password with no
        # authenticator: setting authenticator=PROGRAMMATIC_ACCESS_TOKEN makes
        # this deployment reject it outright. Set SNOWFLAKE_AUTHENTICATOR=oauth
        # explicitly only for a true OAuth bearer token.
        if not authenticator or authenticator.lower() in pat_aliases:
            params['password'] = token
        else:
            params['token'] = token
            params['authenticator'] = authenticator
    elif authenticator:
        params['authenticator'] = authenticator
        if _env('SNOWFLAKE_PASSWORD'):
            params['password'] = _env('SNOWFLAKE_PASSWORD')
    else:
        params['password'] = _env('SNOWFLAKE_PASSWORD')

    return params


def _abandon(conn):
    """
    Close a connection without waiting for it. Snowflake's close() sends a
    session-termination request — a network call that can itself hang on the
    same flaky path that causes other stuck connections (seen in practice:
    TCP SYN_SENT that never resolves). A hung close() must never be able to
    block callers, so it runs in a fire-and-forget daemon thread instead.
    """
    if conn is None:
        return
    def _do_close():
        try:
            conn.close()
        except Exception:
            pass
    threading.Thread(target=_do_close, daemon=True).start()


def connect(force=False):
    """Lazily open (or reuse) the Snowflake connection."""
    global _conn, _last_error

    if not configured():
        raise RuntimeError('Snowflake is not configured: missing '
                           + ', '.join(missing_keys()))

    with _lock:
        if force and _conn is not None:
            _abandon(_conn)
            _conn = None

        if _conn is not None:
            try:
                if not _conn.is_closed():
                    return _conn
            except Exception:
                pass
            _conn = None

        try:
            _conn = snowflake.connector.connect(**_build_params())
            _last_error = None
        except Exception as e:
            _last_error = str(e)
            raise
        return _conn


def reset():
    """
    Drop the cached connection so new credentials take effect. Never blocks
    on a slow/stuck close() — connectivity trouble reaching Snowflake must
    not be able to hang /api/connect, which the whole app waits on at load.
    """
    global _conn
    with _lock:
        old, _conn = _conn, None
    _abandon(old)
    # Credential/config changes must not retain account-scoped filter data.
    try:
        _availability_filter_cache.clear()
    except NameError:
        pass


_READ_ONLY_PREFIXES = ('select', 'with', 'show', 'describe', 'desc', 'explain')


def _assert_read_only(sql: str):
    stripped = sql.strip().rstrip(';')
    if ';' in stripped:
        raise ValueError('Only a single statement may be executed')
    head = stripped.lstrip('(').lstrip().split(None, 1)
    if not head or head[0].lower() not in _READ_ONLY_PREFIXES:
        raise ValueError('Only read-only statements are permitted')


def query(sql: str, params=None, limit=None, timeout=None):
    """
    Run a read-only query and return a list of dicts.
    `params` must be a sequence/dict of bind values — never interpolate
    user input into `sql` directly.
    """
    _assert_read_only(sql)
    conn = connect()
    cur = conn.cursor(DictCursor)
    try:
        cur.execute(sql, params or None, timeout=timeout or QUERY_TIMEOUT)
        rows = cur.fetchmany(limit) if limit else cur.fetchall()
        return [dict(r) for r in rows]
    finally:
        cur.close()


# ── Building metadata (fanscan_public.building_details) ───────────────────────
# Column names are discovered at runtime rather than hardcoded, so the exact
# spelling in your warehouse doesn't have to be guessed.

_schema_cache = {'cols': None, 'map': None, 'ts': 0}
_SCHEMA_TTL = 600

# Candidate column names, most specific first.
_ID_CANDIDATES   = ('BUILDING_ID', 'ID', 'BUILDINGID', 'BLDG_ID')
_NAME_CANDIDATES = ('BUILDING_NAME', 'NAME', 'BUILDINGNAME', 'COMMUNITY_NAME')
_ORG_CANDIDATES  = ('ORGANIZATION_ID', 'ORG_ID', 'ORGANIZATIONID')
_ORGNAME_CANDIDATES = ('ORGANIZATION_NAME', 'ORG_NAME', 'ORGANIZATION',
                       'CLIENT_NAME', 'CUSTOMER_NAME')
_STUDENT_CANDIDATES = ('STUDENT_HOUSING', 'IS_STUDENT_HOUSING',
                       'STUDENTHOUSING', 'STUDENT_HOUSING_FLAG')
def _split_table(table: str):
    parts = [p.strip('"') for p in table.split('.')]
    if len(parts) == 3:
        return parts[0], parts[1], parts[2]
    if len(parts) == 2:
        return _env('SNOWFLAKE_DATABASE') or None, parts[0], parts[1]
    return _env('SNOWFLAKE_DATABASE') or None, _env('SNOWFLAKE_SCHEMA') or None, parts[0]


def columns(refresh=False):
    """Column names of the building table, uppercased."""
    if not refresh and _schema_cache['cols'] and \
       (time.time() - _schema_cache['ts']) < _SCHEMA_TTL:
        return _schema_cache['cols']

    db, schema, table = _split_table(BUILDING_TABLE)
    info = f'{db}.INFORMATION_SCHEMA.COLUMNS' if db else 'INFORMATION_SCHEMA.COLUMNS'
    sql = (f'SELECT COLUMN_NAME, DATA_TYPE FROM {info} '
           'WHERE UPPER(TABLE_NAME) = UPPER(%s)')
    binds = [table]
    if schema:
        sql += ' AND UPPER(TABLE_SCHEMA) = UPPER(%s)'
        binds.append(schema)
    sql += ' ORDER BY ORDINAL_POSITION'

    rows = query(sql, binds)
    cols = [r['COLUMN_NAME'].upper() for r in rows]
    _schema_cache.update(cols=cols, map=None, ts=time.time())
    return cols


def _pick(cols, candidates):
    for c in candidates:
        if c in cols:
            return c
    return None


def column_map(refresh=False):
    """Resolved {role: actual column} for id / name / org."""
    if not refresh and _schema_cache['map']:
        return _schema_cache['map']
    cols = columns(refresh)
    mapping = {
        'id':       _pick(cols, _ID_CANDIDATES),
        'name':     _pick(cols, _NAME_CANDIDATES),
        'org':      _pick(cols, _ORG_CANDIDATES),
        'org_name': _pick(cols, _ORGNAME_CANDIDATES),
    }
    _schema_cache['map'] = mapping
    return mapping


def _numeric_id(entity: str):
    """'building_10238' -> '10238'. Falls through unchanged if not prefixed."""
    if entity.lower().startswith('building_'):
        return entity.split('_', 1)[1]
    return entity


def lookup(entities):
    """
    Metadata for a batch of snapshot entity ids.
    Returns {entity_id: {row...}} keyed by the original 'building_NNN' form.
    """
    entities = [e for e in dict.fromkeys(entities) if e]
    if not entities:
        return {}

    cmap = column_map()
    id_col = cmap['id']
    if not id_col:
        raise RuntimeError(
            f'No building-id column found in {BUILDING_TABLE}; '
            f'saw {", ".join(columns()[:15])}')

    by_numeric = {}
    for e in entities:
        by_numeric.setdefault(str(_numeric_id(e)), e)

    cols = set(columns())
    select = [f'b.{id_col} AS ID']
    # DETAIL_COLUMNS is only a performance-minded baseline. The resolved
    # columns must also be selected when the warehouse uses an alternate
    # spelling such as NAME or ORG_ID; otherwise column_map() finds them but
    # lookup() silently returns no value for the export.
    selected = {id_col}
    for c in (*DETAIL_COLUMNS, cmap['name'], cmap['org'], cmap['org_name']):
        if c and c in cols and c not in selected:
            select.append(f'b.{c}')
            selected.add(c)

    org_col = cmap['org']
    join = ''
    if org_col and ORG_TABLE:
        select.append('o.NAME AS ORGANIZATION_NAME')
        join = (f' LEFT JOIN {ORG_TABLE} o ON b.{org_col} = o.ID '
                f'AND {_LIVE.format(alias="o")}')

    out = {}
    ids = list(by_numeric)
    CHUNK = 5000
    for i in range(0, len(ids), CHUNK):
        chunk = ids[i:i + CHUNK]
        placeholders = ', '.join(['%s'] * len(chunk))
        rows = query(
            f'SELECT {", ".join(select)} FROM {BUILDING_TABLE} b{join} '
            f'WHERE TO_VARCHAR(b.{id_col}) IN ({placeholders}) '
            f'AND {_LIVE.format(alias="b")}',
            chunk,
        )
        for row in rows:
            entity = by_numeric.get(str(row.get('ID')))
            if entity:
                out[entity] = row
    return out


_org_cache = {'rows': None, 'ts': 0}
_ORG_TTL = 900


def organizations(refresh=False):
    """
    Organizations that actually own buildings, with names resolved from the
    organization table. Cached — this aggregates a large table.
    """
    if not refresh and _org_cache['rows'] is not None and \
       (time.time() - _org_cache['ts']) < _ORG_TTL:
        return _org_cache['rows']

    cmap = column_map()
    id_col, org_col = cmap['id'], cmap['org']
    if not org_col:
        return []

    rows = query(
        f'SELECT TO_VARCHAR(b.{org_col}) AS VALUE, '
        f'MAX(o.NAME) AS LABEL, COUNT(DISTINCT b.{id_col}) AS N '
        f'FROM {BUILDING_TABLE} b '
        f'LEFT JOIN {ORG_TABLE} o ON b.{org_col} = o.ID '
        f'AND {_LIVE.format(alias="o")} '
        f'WHERE b.{org_col} IS NOT NULL AND {_LIVE.format(alias="b")} '
        f'GROUP BY 1 ORDER BY LOWER(MAX(o.NAME)) NULLS LAST, 1'
    )
    out = [{
        'value': r['VALUE'],
        'label': (f"{r['LABEL']} ({r['N']:,})" if r['LABEL']
                  else f"org {r['VALUE']} ({r['N']:,})"),
    } for r in rows]
    _org_cache.update(rows=out, ts=time.time())
    return out


def building_ids_for_org(org_value):
    """Entity ids belonging to one organization, in 'building_NNN' form."""
    cmap = column_map()
    id_col, org_col = cmap['id'], cmap['org']
    if not id_col or not org_col:
        return None   # can't filter — caller decides how to handle

    rows = query(
        f'SELECT DISTINCT TO_VARCHAR(b.{id_col}) AS ID FROM {BUILDING_TABLE} b '
        f'WHERE TO_VARCHAR(b.{org_col}) = %s AND {_LIVE.format(alias="b")}',
        [str(org_value)],
    )
    return {f'building_{r["ID"]}' for r in rows if r['ID'] is not None}


_availability_filter_cache = {}
_AVAILABILITY_FILTER_TTL = 5 * 60


def availability_filter_ids(exclude_students=False, exclude_applications=False):
    """Return building ids allowed by Availability Agent community filters.

    Student housing is read from the configured building-details table.
    Applications launch state comes from the normalized building-product
    tables: a community is live on Applications only when its product launch
    date is before now, its cancellation date is null, and the building and
    product rows are active/non-test/non-deleted as applicable.
    """
    if not exclude_students and not exclude_applications:
        return None, []

    cache_key = (bool(exclude_students), bool(exclude_applications))
    cached = _availability_filter_cache.get(cache_key)
    if cached and (time.time() - cached['ts']) < _AVAILABILITY_FILTER_TTL:
        allowed = cached['allowed']
        return (set(allowed) if allowed is not None else None,
                list(cached['notes']))

    cmap = column_map()
    id_col = cmap['id']
    if not id_col:
        return None, ['building-id column unavailable']
    cols = set(columns())

    def pick(candidates):
        return next((candidate for candidate in candidates if candidate in cols), None)

    student_col = pick(_STUDENT_CANDIDATES) if exclude_students else None
    unavailable = []
    if exclude_students and not student_col:
        unavailable.append('student housing filter unavailable')

    launched_applications = set()
    if exclude_applications:
        # Keep this query aligned with the source-of-truth definition used by
        # the Applications product. The org join/selected fields make the
        # provenance explicit even though the filter only needs building IDs.
        launched_rows = query(
            f'SELECT building.ID AS BUILDING_ID, '
            f'building.BUILDING_NAME, '
            f'building.ORGANIZATION_ID AS ORG_ID, '
            f'organization.NAME AS ORG_NAME, '
            f'building_product.LAUNCHED_DATE, '
            f'building_product.CANCELLATION_DATE, '
            f'CASE WHEN building_product.LAUNCHED_DATE IS NOT NULL '
            f'AND building_product.LAUNCHED_DATE < CURRENT_TIMESTAMP() '
            f'AND building_product.CANCELLATION_DATE IS NULL '
            f'THEN TRUE ELSE FALSE END AS IS_LAUNCHED_ON_APPLICATIONS '
            f'FROM {APPLICATIONS_BUILDING_TABLE} building '
            f'JOIN {APPLICATIONS_PRODUCT_TABLE} building_product '
            f'ON building_product.BUILDING_ID = building.ID '
            f'LEFT JOIN {APPLICATIONS_ORG_TABLE} organization '
            f'ON organization.ID = building.ORGANIZATION_ID '
            f"WHERE building_product.PRODUCT = 'Applications' "
            f'AND NOT COALESCE(building._FIVETRAN_DELETED, FALSE) '
            f'AND NOT COALESCE(building_product._FIVETRAN_DELETED, FALSE) '
            f'AND NOT COALESCE(building.IS_TEST, FALSE) '
            f'AND building.ACTIVE = 1 '
            f'AND building_product.LAUNCHED_DATE IS NOT NULL '
            f'AND building_product.LAUNCHED_DATE < CURRENT_TIMESTAMP() '
            f'AND building_product.CANCELLATION_DATE IS NULL'
        )
        launched_applications = {
            f'building_{r["BUILDING_ID"]}'
            for r in launched_rows
            if r.get('BUILDING_ID') is not None and
            str(r.get('IS_LAUNCHED_ON_APPLICATIONS', 'TRUE')).upper() == 'TRUE'
        }

    conditions = [_LIVE.format(alias='b')]
    truthy = "LOWER(TRIM(TO_VARCHAR(b.{col}))) IN ('true', '1', 'yes', 'y', 't')"
    if student_col:
        conditions.append(
            f"(b.{student_col} IS NULL OR NOT ({truthy.format(col=student_col)}))")
    if not student_col and not exclude_applications:
        _availability_filter_cache[cache_key] = {
            'allowed': None, 'notes': list(unavailable), 'ts': time.time(),
        }
        return None, unavailable

    rows = query(
        f'SELECT TO_VARCHAR(b.{id_col}) AS ID FROM {BUILDING_TABLE} b '
        f'WHERE {" AND ".join(conditions)}',
    )
    allowed = {f'building_{r["ID"]}' for r in rows if r.get('ID') is not None}
    if exclude_applications:
        allowed -= launched_applications
    _availability_filter_cache[cache_key] = {
        'allowed': set(allowed), 'notes': list(unavailable), 'ts': time.time(),
    }
    return allowed, unavailable


def _dynamodb_rollouts_table():
    global _dynamo_table
    if _dynamo_table is None:
        with _dynamo_lock:
            if _dynamo_table is None:
                _dynamo_table = boto3.resource(
                    'dynamodb', region_name=DYNAMODB_REGION).Table(DYNAMODB_ROLLOUT_TABLE)
    return _dynamo_table


def _dynamo_bool(value, default=False):
    if isinstance(value, bool):
        return value
    if value is None:
        return default
    return str(value).strip().casefold() in ('true', '1', 'yes', 'y', 'enabled')


def _dynamo_ids(value):
    if value is None:
        return set()
    values = value if isinstance(value, (list, tuple, set)) else [value]
    return {str(_numeric_id(str(item))).strip() for item in values if str(item).strip()}


def _percentage_enabled(percentage, seed):
    try:
        percentage = float(percentage)
    except (TypeError, ValueError):
        percentage = 100.0
    if percentage <= 0:
        return False
    if percentage >= 100:
        return True
    digest = hashlib.sha256(seed.encode('utf-8')).hexdigest()
    bucket = int(digest[:12], 16) / float(16 ** 12)
    return bucket * 100 < percentage


def _current_dynamo_rollout(rollout_name):
    table = _dynamodb_rollouts_table()
    items = []
    request = {'KeyConditionExpression': Key('PK').eq(rollout_name)}
    while True:
        response = table.query(**request)
        items.extend(response.get('Items') or [])
        last_key = response.get('LastEvaluatedKey')
        if not last_key:
            break
        request['ExclusiveStartKey'] = last_key

    active = [item for item in items if _dynamo_bool(item.get('is_active'), True)]
    current = next((item for item in active if item.get('SK') == 'CURRENT'), None)
    if current is None and active:
        current = max(active, key=lambda item: str(
            item.get('version') or item.get('updated_at') or item.get('SK') or ''))
    if current is None:
        return None

    raw_rules = current.get('rollout_rules') or '[]'
    if isinstance(raw_rules, str):
        rules = json.loads(raw_rules)
    else:
        rules = raw_rules
    if not isinstance(rules, list):
        raise ValueError(f'Invalid rollout_rules for {rollout_name}')
    return {
        'default': _dynamo_bool(current.get('default'), False),
        'rules': rules,
    }


def _evaluate_dynamo_rollout(config, rollout_name, entity, org_id):
    if not config:
        return None
    building_id = str(_numeric_id(entity))
    org_id = str(org_id).strip() if org_id is not None and str(org_id).strip() else None
    rules = config.get('rules') or []

    # A building-specific rule is more specific than an organization rule.
    for rule_type, target_id, allow_key, deny_key in (
        ('building', building_id, 'allow_building_ids', 'deny_building_ids'),
        ('org', org_id, 'allow_org_ids', 'deny_org_ids'),
    ):
        if not target_id:
            continue
        for rule in rules:
            if str(rule.get('rule_type', '')).casefold() != rule_type:
                continue
            if target_id in _dynamo_ids(rule.get(deny_key)):
                return False
            if target_id in _dynamo_ids(rule.get(allow_key)):
                rule_id = str(rule.get('rule_id') or rule_type)
                return _percentage_enabled(
                    rule.get('percentage', 100),
                    f'{rollout_name}:{rule_id}:{target_id}')

    for rule in rules:
        if str(rule.get('rule_type', '')).casefold() == 'default':
            rule_id = str(rule.get('rule_id') or 'default')
            return _percentage_enabled(
                rule.get('percentage', 100), f'{rollout_name}:{rule_id}:{building_id}')
    return bool(config.get('default', False))


def rollout_variants(entities, rollout_names, target_times=None, org_ids=None):
    """Resolve current tracked-rollout values from DynamoDB.

    ``org_ids`` maps snapshot entities to their Snowflake organization IDs.
    DynamoDB stores the current rollout configuration in ``SK=CURRENT``;
    ``rollout_rules`` may target either a building or an organization. The
    historical ``target_times`` argument is retained for call compatibility,
    but DynamoDB evaluation uses the current configuration at run time.
    """
    del target_times
    entities = [e for e in dict.fromkeys(entities) if e]
    rollout_names = [n for n in dict.fromkeys(rollout_names) if n]
    org_ids = org_ids or {}
    if not entities or not rollout_names:
        return {}

    configs = {name: _current_dynamo_rollout(name) for name in rollout_names}
    return {
        entity: {
            name: ('enabled' if _evaluate_dynamo_rollout(
                configs[name], name, entity, org_ids.get(entity)) else 'disabled')
            for name in rollout_names
            if configs[name] is not None
        }
        for entity in entities
    }


def health():
    """Connection status for the UI — never raises."""
    if not _DRIVER:
        return {'state': 'unavailable',
                'error': 'snowflake-connector-python is not installed'}
    if not configured():
        return {
            'state': 'unconfigured',
            'missing': missing_keys(),
            'account': _env('SNOWFLAKE_ACCOUNT'),
            'user': _env('SNOWFLAKE_USER'),
            # This is only a presence flag; the token itself is never returned.
            'hasAccessToken': bool(_env('SNOWFLAKE_TOKEN')),
        }

    started = time.time()
    try:
        row = query(
            'SELECT CURRENT_ACCOUNT() AS ACCOUNT, CURRENT_USER() AS USER, '
            'CURRENT_ROLE() AS ROLE, CURRENT_WAREHOUSE() AS WAREHOUSE, '
            'CURRENT_DATABASE() AS DATABASE, CURRENT_SCHEMA() AS SCHEMA'
        )[0]
        return {
            'state':     'ready',
            'account':   row.get('ACCOUNT'),
            'user':      row.get('USER'),
            'role':      row.get('ROLE'),
            'warehouse': row.get('WAREHOUSE'),
            'database':  row.get('DATABASE'),
            'schema':    row.get('SCHEMA'),
            'elapsed':   round(time.time() - started, 2),
        }
    except Exception as e:
        message = str(e)
        return {'state': 'error', 'error': message,
                'credentialIssue': credential_error(message)}
