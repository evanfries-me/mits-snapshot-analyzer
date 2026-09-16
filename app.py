"""
MITS Snapshot Analyzer — S3 snapshot browser + search
Path format: elise-mits/{source_type}/{entity_id}/snapshot-{time_created}/{file_name}.{content_type}.gz

Explore mode: browse the tree. At the entity level the latest snapshot is auto-selected.
Search  mode: find an exact string inside one file across every building's latest snapshot.

Search is backed by a persistent on-disk index (one per integration) that maps each
building to its latest snapshot + file list. Building the index is the expensive part
(~2 S3 calls per building); once built, a search only pays one GET per building.

Connects via .env file or AWS environment variables.
"""

from flask import Flask, request, jsonify, send_from_directory
from flask_cors import CORS
from concurrent.futures import (ProcessPoolExecutor, ThreadPoolExecutor,
                                TimeoutError as FutureTimeoutError, wait,
                                FIRST_COMPLETED)
from datetime import date, datetime, timedelta, timezone
from botocore.config import Config
from botocore.exceptions import ClientError
from dotenv import load_dotenv
import snowflake_db
import boto3
import csv
import gzip as gzip_module
import hashlib
import json
import os
import re
import threading
import time
import urllib.parse
import uuid
import xml.etree.ElementTree as ET

load_dotenv()

app = Flask(__name__, static_folder='static', static_url_path='')
CORS(app)

REGION    = 'us-west-2'
BUCKET    = 'elise-snapshots'
ROOT      = 'elise-mits/'
PAGE_SIZE = 1000    # S3 max items per API call (hard limit)
DYNAMIC_PRICING_BUCKET = os.environ.get(
    'DYNAMIC_PRICING_BUCKET', 'elise-dynamic-pricing')
DYNAMIC_PRICING_MAX_COMMUNITIES = 5000
DYNAMIC_PRICING_WORKERS = 16
DYNAMIC_PRICING_VALIDATION_WORKERS = min(12, os.cpu_count() or 4)

INDEX_DIR     = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'index')
INDEX_WORKERS = 64  # parallel LISTs while indexing
SEARCH_WORKERS = 48 # parallel GETs while searching
SAMPLE_SIZE   = 150 # buildings sampled to populate the file-name dropdown
RESULT_CAP    = 500 # max matches returned to the client
SNIPPET_PAD   = 70  # chars of context on each side of a match
ENRICH_TIMEOUT = 20 # seconds before Snowflake enrichment is abandoned
AVAILABILITY_INDEX_MAX_AGE = 24 * 60 * 60
ENV_PATH        = os.path.join(os.path.dirname(os.path.abspath(__file__)), '.env')

EXPORT_DIR      = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'exports')
EXPORT_MAX_AGE  = 24 * 60 * 60  # exports older than this are swept on the next fields job
CSV_ROW_CAP     = 200_000       # this feature exists for bulk export, so the cap is generous
FIELDS_PREVIEW  = 20            # rows echoed inline for on-screen confidence before download
HISTORY_PATH    = os.path.join(EXPORT_DIR, 'history.json')
HISTORY_MAX     = 100
AVAILABILITY_RULES_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                       'availability_agent_rules.json')

# Snapshot timestamps sort lexicographically, so StartAfter can seek near the end
# of a building's snapshot list instead of paging through thousands of them.
# Tried in order; the first cutoff that yields a snapshot wins.
CUTOFF_DAYS = (2, 30, 365)

_connected = False
_availability_rules_cache = None
_availability_rules_cache_mtime = None

# ── Shared boto3 client ───────────────────────────────────────────────────────
_BOTO_CONFIG = Config(
    max_pool_connections=max(INDEX_WORKERS, SEARCH_WORKERS) + 8,
    retries={'max_attempts': 3, 'mode': 'standard'},
    connect_timeout=5,
    read_timeout=30,
)
_client = None
_client_lock = threading.Lock()


def s3():
    global _client
    if _client is None:
        with _client_lock:
            if _client is None:
                _client = boto3.client('s3', region_name=REGION, config=_BOTO_CONFIG)
    return _client


# ── Directory-listing cache (Explore mode) ────────────────────────────────────
_cache: dict = {}
CACHE_TTL = 60


def _cache_get(prefix: str, token: str = ''):
    entry = _cache.get((prefix, token))
    if entry and (time.time() - entry['ts']) < CACHE_TTL:
        return entry['data']
    return None


def _cache_set(prefix: str, token: str, data: dict):
    _cache[(prefix, token)] = {'data': data, 'ts': time.time()}
    if len(_cache) > 300:
        cutoff = time.time() - CACHE_TTL
        for k in [k for k, v in _cache.items() if v['ts'] < cutoff]:
            del _cache[k]


# ── Path helpers ──────────────────────────────────────────────────────────────

def _depth(prefix: str) -> int:
    """Segments after ROOT. ROOT itself = 0, source_type = 1, entity = 2, snapshot = 3."""
    return len([p for p in prefix[len(ROOT):].rstrip('/').split('/') if p])


def _safe_integration(name: str):
    """Reject anything that could escape the integration level."""
    if not isinstance(name, str) or not name or '/' in name or name in ('.', '..'):
        return None
    return name


def _allowed_related_integrations(primary: str) -> set:
    """Integrations that may provide related files for a primary source."""
    allowed = {'UnitEditor'}
    if primary:
        allowed.add(primary)
    if primary == 'RentCafe':
        allowed.add('Voyager')
    return allowed


_VOYAGER_CANONICAL_FILES = ('AllUnits_Login', 'AvailableUnits_Login')
_VOYAGER_INTEGRATIONS = {
    'Voyager', 'YardiVoyager', 'PricingAvailsSourceType.YardiVoyager',
}

# The legacy Voyager root is empty. Current Voyager snapshots live in
# YardiVoyager; the indexer removes buildings represented in RentCafe's current
# index, because those are RentCafe-priced communities where Voyager is only a
# secondary source.
_AVAILABILITY_SOURCE_INTEGRATIONS = {
    'Voyager': 'YardiVoyager',
}


def _availability_source_integration(integration: str) -> str:
    return _AVAILABILITY_SOURCE_INTEGRATIONS.get(integration, integration)


def _availability_index_exclusions(integration: str, window_end) -> set:
    """Current primary-source communities excluded from virtual integrations."""
    if integration != 'Voyager':
        return set()
    rentcafe = _index_load('RentCafe') or {}
    cutoff = window_end - timedelta(hours=24)
    excluded = set()
    for entity, entity_data in (rentcafe.get('entities') or {}).items():
        try:
            if cutoff < _snapshot_dt(entity_data[0]) <= window_end:
                excluded.add(entity)
        except (TypeError, ValueError, IndexError):
            continue
    return excluded

# Several integrations append a property/external ID between the logical file
# name and its content extension. Keep the rule shape-based rather than tied to
# today's integration list so newly-added integrations with the same convention
# are consolidated automatically. Five digits avoids treating ordinary version
# suffixes such as `_2` as external IDs; UUID and long-hex forms cover ResMan
# and other opaque identifiers.
_EXTERNAL_ID_FILE_RE = re.compile(
    r'^(?P<base>.+)_(?:'
    r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}'
    r'|\d{5,}'
    r'|[0-9a-f]{24,}'
    r')\.(?:json|xml|csv|txt)(?:\.gz)?$',
    re.IGNORECASE,
)


def _canonical_file_name(integration: str, file_name: str) -> str:
    """Collapse per-property filename variants to one stable logical name."""
    if integration in _VOYAGER_INTEGRATIONS:
        for base in _VOYAGER_CANONICAL_FILES:
            if file_name == base or file_name.startswith(base + '_') or file_name.startswith(base + '.'):
                return base
    external_id_match = _EXTERNAL_ID_FILE_RE.fullmatch(file_name)
    if external_id_match:
        return external_id_match.group('base')
    return file_name


def _file_variant(files, integration: str, requested: str):
    """Pick one actual indexed filename matching a requested display name."""
    matches = sorted(f for f in files if _canonical_file_name(integration, f) == requested)
    return matches[0] if matches else None


def _display_file_names(integration: str, names) -> list:
    return sorted({_canonical_file_name(integration, name) for name in names})


def _latest_snapshot_prefix(entity_prefix: str):
    """Lexicographically greatest snapshot-* prefix under entity_prefix, or None."""
    client = s3()
    kwargs = {'Bucket': BUCKET, 'Delimiter': '/', 'Prefix': entity_prefix}
    latest = None
    while True:
        resp = client.list_objects_v2(**kwargs)
        for cp in resp.get('CommonPrefixes', []):
            if cp['Prefix'] > (latest or ''):
                latest = cp['Prefix']
        if not resp.get('IsTruncated'):
            break
        kwargs['ContinuationToken'] = resp['NextContinuationToken']
    return latest


# ── "As of" date selection for search ─────────────────────────────────────────
# Snapshot names are ISO timestamps ("snapshot-2026-08-19T15:55:41.157032Z"),
# so a search can be pinned to "the latest snapshot at or before this instant"
# instead of always using the newest one.

def _parse_cutoff(raw: str):
    """
    Parse a user-supplied 'as of' value into a UTC-aware datetime, or None if
    `raw` is blank. Accepts a bare ISO datetime (e.g. from a datetime-local
    input, treated as UTC) or a full snapshot-viewer URL — only its
    reference_time query parameter is used; every other parameter is ignored.
    Raises ValueError with a user-facing message if unparseable.
    """
    raw = (raw or '').strip()
    if not raw:
        return None

    if raw.lower().startswith(('http://', 'https://')):
        qs = urllib.parse.parse_qs(urllib.parse.urlparse(raw).query)
        values = qs.get('reference_time')
        if not values or not values[0]:
            raise ValueError('That link has no reference_time parameter')
        raw = values[0]

    try:
        dt = datetime.fromisoformat(raw.replace('Z', '+00:00'))
    except ValueError:
        raise ValueError(f'Could not parse "{raw}" as a datetime')

    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)


def _parse_result_limit(raw):
    """Return an optional positive whole-number result cap."""
    if raw in (None, ''):
        return None
    if isinstance(raw, bool):
        raise ValueError('limit must be a positive integer')
    if isinstance(raw, int):
        value = raw
    elif isinstance(raw, str) and re.fullmatch(r'[1-9]\d*', raw.strip()):
        value = int(raw.strip())
    else:
        raise ValueError('limit must be a positive integer')
    if value <= 0 or value > CSV_ROW_CAP:
        raise ValueError(f'limit must be between 1 and {CSV_ROW_CAP:,}')
    return value


def _snapshot_dt(snapshot_name: str):
    """'snapshot-2026-08-19T15:55:41.157032Z' -> UTC-aware datetime."""
    iso = snapshot_name[len('snapshot-'):] if snapshot_name.startswith('snapshot-') else snapshot_name
    dt = datetime.fromisoformat(iso.replace('Z', '+00:00'))
    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)


def _snapshot_prefix_before(entity_prefix: str, cutoff: datetime,
                            lookback_hours: int = 24):
    """
    Latest snapshot-* prefix in the window ending at `cutoff`, or None when no
    snapshot exists within `lookback_hours` before it. CommonPrefixes sort in
    chronological order because snapshot names use ISO timestamps.
    """
    client = s3()
    lower_bound = cutoff - timedelta(hours=lookback_hours)
    kwargs = {'Bucket': BUCKET, 'Delimiter': '/', 'Prefix': entity_prefix, 'MaxKeys': PAGE_SIZE}
    # Seek immediately before the lower boundary so dated searches do not
    # traverse a building's full snapshot history.
    seek = (lower_bound - timedelta(microseconds=1)).astimezone(timezone.utc)
    kwargs['StartAfter'] = (
        f'{entity_prefix}snapshot-'
        f'{seek.isoformat(timespec="microseconds").replace("+00:00", "Z")}')
    best_name, best_prefix = None, None
    while True:
        resp = client.list_objects_v2(**kwargs)
        for cp in resp.get('CommonPrefixes', []):
            name = cp['Prefix'][len(entity_prefix):].rstrip('/')
            try:
                ts = _snapshot_dt(name)
            except Exception:
                continue
            if lower_bound <= ts <= cutoff:
                if best_name is None or name > best_name:
                    best_name, best_prefix = name, cp['Prefix']
            elif ts > cutoff:
                return best_prefix
        if not resp.get('IsTruncated'):
            break
        kwargs['ContinuationToken'] = resp['NextContinuationToken']
    return best_prefix


def _snapshot_prefix_nearest(entity_prefix: str, reference: datetime,
                             max_skew_minutes: int = 15):
    """Return the snapshot closest to ``reference`` within a small sync skew.

    Related integration snapshots from the same logical sync can finish a few
    seconds after the primary snapshot. Latest-mode cross-integration joins
    may use that near-future snapshot; explicit as-of searches continue using
    the strict at-or-before resolver above.
    """
    client = s3()
    lower_bound = reference - timedelta(minutes=max_skew_minutes)
    upper_bound = reference + timedelta(minutes=max_skew_minutes)
    seek = (lower_bound - timedelta(microseconds=1)).astimezone(timezone.utc)
    kwargs = {
        'Bucket': BUCKET,
        'Delimiter': '/',
        'Prefix': entity_prefix,
        'MaxKeys': PAGE_SIZE,
        'StartAfter': (
            f'{entity_prefix}snapshot-'
            f'{seek.isoformat(timespec="microseconds").replace("+00:00", "Z")}'),
    }
    best_prefix = None
    best_rank = None
    while True:
        response = client.list_objects_v2(**kwargs)
        for common_prefix in response.get('CommonPrefixes', []):
            name = common_prefix['Prefix'][len(entity_prefix):].rstrip('/')
            try:
                timestamp = _snapshot_dt(name)
            except (TypeError, ValueError):
                continue
            if timestamp > upper_bound:
                return best_prefix
            if timestamp < lower_bound:
                continue
            rank = (abs((timestamp - reference).total_seconds()),
                    timestamp > reference, timestamp)
            if best_rank is None or rank < best_rank:
                best_rank = rank
                best_prefix = common_prefix['Prefix']
        if not response.get('IsTruncated'):
            break
        kwargs['ContinuationToken'] = response['NextContinuationToken']
    return best_prefix


# ── Building discovery ────────────────────────────────────────────────────────

def _cutoff_stamps():
    now = datetime.now(timezone.utc)
    return [(now - timedelta(days=d)).strftime('%Y-%m-%dT%H:%M:%S') for d in CUTOFF_DAYS]


def _list_buildings(integration: str):
    """All entity ids under an integration. ~1 call per 1000 buildings."""
    prefix = f'{ROOT}{integration}/'
    client = s3()
    kwargs = {'Bucket': BUCKET, 'Delimiter': '/', 'Prefix': prefix, 'MaxKeys': PAGE_SIZE}
    out = []
    while True:
        resp = client.list_objects_v2(**kwargs)
        out += [cp['Prefix'][len(prefix):].rstrip('/') for cp in resp.get('CommonPrefixes', [])]
        if not resp.get('IsTruncated'):
            break
        kwargs['ContinuationToken'] = resp['NextContinuationToken']
    return out


def _latest_snapshot_seeked(entity_prefix: str, stamps, full_fallback=True):
    """
    Find a building's latest snapshot, seeking with StartAfter so we read only the
    tail of its snapshot list. Falls back to progressively wider windows, then to
    a full listing. Returns the snapshot name, or None.
    """
    client = s3()
    attempts = list(stamps) + ([None] if full_fallback else [])

    for stamp in attempts:
        kwargs = {'Bucket': BUCKET, 'Delimiter': '/', 'Prefix': entity_prefix,
                  'MaxKeys': PAGE_SIZE}
        if stamp:
            kwargs['StartAfter'] = f'{entity_prefix}snapshot-{stamp}'

        latest = None
        while True:
            resp = client.list_objects_v2(**kwargs)
            for cp in resp.get('CommonPrefixes', []):
                name = cp['Prefix'][len(entity_prefix):].rstrip('/')
                if latest is None or name > latest:
                    latest = name
            if not resp.get('IsTruncated'):
                break
            kwargs['ContinuationToken'] = resp['NextContinuationToken']

        if latest:
            return latest
    return None


def _snapshot_files(entity_prefix: str, snapshot: str):
    """File names inside one snapshot folder. Normally 1 call."""
    prefix = f'{entity_prefix}{snapshot}/'
    client = s3()
    kwargs = {'Bucket': BUCKET, 'Prefix': prefix, 'MaxKeys': PAGE_SIZE}
    names = []
    while True:
        resp = client.list_objects_v2(**kwargs)
        for obj in resp.get('Contents', []):
            name = obj['Key'][len(prefix):]
            if name and '/' not in name:
                names.append(name)
        if not resp.get('IsTruncated'):
            break
        kwargs['ContinuationToken'] = resp['NextContinuationToken']
    return names


def _discover(integration: str, entity: str, stamps, full_fallback=True):
    """(entity, snapshot, [file names]) for one building, or None."""
    entity_prefix = f'{ROOT}{integration}/{entity}/'
    snapshot = _latest_snapshot_seeked(entity_prefix, stamps, full_fallback)
    if not snapshot:
        return None
    return (entity, snapshot, _snapshot_files(entity_prefix, snapshot))


# ── Index persistence ─────────────────────────────────────────────────────────
# Stored gzipped as {"entities": {entity: [snapshot, [file names]]}} — the full S3
# key is reconstructed from integration/entity/snapshot/file, so it isn't stored.

def _index_path(integration: str) -> str:
    return os.path.join(INDEX_DIR, f'{integration}.json.gz')


def _index_load(integration: str):
    path = _index_path(integration)
    if not os.path.exists(path):
        return None
    try:
        with gzip_module.open(path, 'rt', encoding='utf-8') as fh:
            return json.load(fh)
    except Exception:
        return None


def _index_write(integration: str, payload: dict):
    """Atomically replace one compressed index payload."""
    os.makedirs(INDEX_DIR, exist_ok=True)
    tmp = _index_path(integration) + '.tmp'
    with gzip_module.open(tmp, 'wt', encoding='utf-8') as fh:
        json.dump(payload, fh)
    os.replace(tmp, _index_path(integration))
    return payload


def _index_save(integration: str, entities: dict, stats: dict):
    return _index_write(integration, {
        'integration': integration,
        'builtAt':     time.time(),
        'entities':    entities,
        'stats':       stats,
    })


def _index_meta(integration: str):
    """Index summary without decoding the whole payload into a response."""
    data = _index_load(integration)
    if not data:
        return {'state': 'none'}
    return {
        'state':     'ready',
        'buildings': len(data.get('entities', {})),
        'builtAt':   data.get('builtAt'),
        'filteredAt': data.get('filteredAt'),
        'stats':     data.get('stats', {}),
    }


def _availability_index_freshness(integration: str):
    """Return whether an Availability Agent index exists and is under 24h old."""
    meta = _index_meta(integration)
    built_at = meta.get('builtAt')
    if meta.get('state') != 'ready' or not isinstance(built_at, (int, float)):
        return 'missing', meta
    age = max(0, time.time() - built_at)
    meta['ageSeconds'] = age
    return ('fresh' if age <= AVAILABILITY_INDEX_MAX_AGE else 'stale'), meta


# ── Background jobs ───────────────────────────────────────────────────────────
_jobs: dict = {}
_jobs_lock = threading.Lock()
_history_lock = threading.Lock()


def _history_read():
    try:
        with open(HISTORY_PATH, 'r', encoding='utf-8') as fh:
            data = json.load(fh)
        return data if isinstance(data, list) else []
    except (OSError, ValueError, TypeError):
        return []


def _history_write(entries):
    os.makedirs(EXPORT_DIR, exist_ok=True)
    tmp = HISTORY_PATH + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as fh:
        json.dump(entries, fh, ensure_ascii=False, indent=2)
    os.replace(tmp, HISTORY_PATH)


def _history_record(job_id, kind, result, details=None):
    if not result or kind not in (
            'fields', 'availability', 'dynamic_pricing_validation'):
        return
    now = time.time()
    with _history_lock:
        entries = _history_read()
        previous = next((entry for entry in entries if entry.get('id') == job_id), {})
        is_validation = kind == 'dynamic_pricing_validation'
        entry = {
            'id': job_id,
            'kind': kind,
            'name': previous.get('name') or '',
            'integration': result.get('integration', ''),
            'createdAt': datetime.fromtimestamp(now, timezone.utc).isoformat(),
            'created': now,
            'favorite': bool(previous.get('favorite')),
            'rowCount': (result.get('matricesTested', 0)
                         if is_validation else result.get('rowCount', 0)),
            'fields': result.get('fields') or [],
            'csvFields': result.get('csvFields') or result.get('fields') or [],
            'fileName': result.get('fileName'),
            'details': details or {},
            'downloadUrl': (None if is_validation
                            else f'/api/search/csv/{job_id}'),
            'resultUrl': (f'/api/dynamic-pricing/validation/{job_id}'
                          if is_validation else None),
        }
        entries = [entry] + [item for item in entries if item.get('id') != job_id]
        entries.sort(key=lambda item: float(item.get('created') or 0), reverse=True)
        entries = entries[:HISTORY_MAX]
        _history_write(entries)


def _history_entries():
    with _history_lock:
        entries = _history_read()
    for entry in entries:
        extension = (
            '.json' if entry.get('kind') == 'dynamic_pricing_validation'
            else '.csv')
        entry['available'] = os.path.exists(os.path.join(
            EXPORT_DIR, f'{entry.get("id", "")}{extension}'))
    return entries


def _job_new(kind: str, integration: str, total: int = 0) -> str:
    job_id = uuid.uuid4().hex[:12]
    with _jobs_lock:
        _jobs[job_id] = {
            'id': job_id, 'kind': kind, 'integration': integration,
            'status': 'running', 'done': 0, 'total': total,
            'started': time.time(), 'finished': None,
            'error': None, 'result': None, 'note': '',
            'stopRequested': False,
        }
        # keep the map small
        if len(_jobs) > 25:
            oldest = sorted(_jobs.values(), key=lambda j: j['started'])
            for j in oldest[:len(_jobs) - 25]:
                if j['status'] != 'running':
                    _jobs.pop(j['id'], None)
    return job_id


def _job_update(job_id: str, **fields):
    with _jobs_lock:
        job = _jobs.get(job_id)
        if job:
            job.update(fields)


def _job_get(job_id: str):
    with _jobs_lock:
        job = _jobs.get(job_id)
        return dict(job) if job else None


def _job_stop_requested(job_id: str) -> bool:
    job = _job_get(job_id)
    return bool(job and job.get('stopRequested'))


def _running_job_for(kind: str, integration: str):
    with _jobs_lock:
        for job in _jobs.values():
            if job['kind'] == kind and job['integration'] == integration \
               and job['status'] == 'running':
                return job['id']
    return None


def _run_index_job(job_id: str, integration: str, sample_percent: int = 100,
                   reference_time=None):
    try:
        source_integration = _availability_source_integration(integration)
        discovered_buildings = _list_buildings(source_integration)
        window_end = reference_time or datetime.now(timezone.utc)
        excluded_entities = _availability_index_exclusions(integration, window_end)
        all_buildings = [entity for entity in discovered_buildings
                         if entity not in excluded_entities]
        sample_size = (len(all_buildings) * sample_percent + 99) // 100
        if all_buildings and sample_size == 0:
            sample_size = 1
        buildings = sorted(
            all_buildings,
            key=lambda entity: hashlib.sha256(
                f'{source_integration}:{entity}'.encode('utf-8')).digest())[:sample_size]
        recent_cutoff = window_end - timedelta(hours=24)
        window_label = (f'the 24 hours before {window_end.isoformat()}'
                        if reference_time else 'the past 24 hours')
        _job_update(job_id, total=len(buildings),
                    note=(f'Finding snapshots created in {window_label} · '
                          f'{sample_percent}% sample ({len(buildings):,} of '
                          f'{len(all_buildings):,} eligible buildings)…'))

        # Seek directly to the 24-hour boundary and deliberately avoid the
        # historical fallback. A building with no snapshot after this point
        # does not belong in a newly-built index.
        stamps = [recent_cutoff.strftime('%Y-%m-%dT%H:%M:%S')]
        entities = {}
        excluded = 0
        lock     = threading.Lock()
        counter  = {'n': 0}

        def work(entity):
            nonlocal excluded
            try:
                if reference_time:
                    entity_prefix = f'{ROOT}{source_integration}/{entity}/'
                    snapshot_prefix = _snapshot_prefix_before(
                        entity_prefix, reference_time)
                    if snapshot_prefix:
                        snapshot = snapshot_prefix[len(entity_prefix):].rstrip('/')
                        found = (entity, snapshot,
                                 _snapshot_files(entity_prefix, snapshot))
                    else:
                        found = None
                else:
                    found = _discover(source_integration, entity, stamps,
                                      full_fallback=False)
            except Exception:
                found = None
            with lock:
                counter['n'] += 1
                if counter['n'] % 25 == 0:
                    _job_update(job_id, done=counter['n'])
                try:
                    is_recent = bool(
                        found and recent_cutoff < _snapshot_dt(found[1]) <= window_end)
                except (TypeError, ValueError):
                    is_recent = False
                if is_recent:
                    entities[found[0]] = [found[1], found[2]]
                else:
                    excluded += 1

        if buildings:
            with ThreadPoolExecutor(max_workers=INDEX_WORKERS) as pool:
                list(pool.map(work, buildings))

        _job_update(job_id, done=len(buildings), note='Saving index…')
        payload = _index_save(integration, entities, {
            'buildings': len(all_buildings),
            'discoveredBuildings': len(discovered_buildings),
            'excludedRentCafeSecondary': len(excluded_entities),
            'sourceIntegration': source_integration,
            'samplePercent': sample_percent,
            'sampledBuildings': len(buildings),
            'referenceTime': reference_time.isoformat() if reference_time else None,
            'indexed':   len(entities),
            'excludedOutside24Hours': excluded,
            'seconds':   round(time.time() - _job_get(job_id)['started'], 1),
        })
        _job_update(job_id, status='done', finished=time.time(),
                    result={'buildings': len(entities),
                            'samplePercent': sample_percent,
                            'excludedRentCafeSecondary': len(excluded_entities),
                            'sourceIntegration': source_integration,
                            'sampledBuildings': len(buildings),
                            'referenceTime': reference_time.isoformat() if reference_time else None,
                            'excludedOutside24Hours': excluded,
                            'builtAt': payload['builtAt']})
    except Exception as e:
        _job_update(job_id, status='error', error=str(e), finished=time.time())


def _run_companion_index_job(job_id: str, primary_integration: str,
                             companion_integration: str):
    """Build a 24h companion index for only the primary index's buildings."""
    try:
        _job_update(job_id, note=f'Loading {primary_integration} building scope…')
        primary_data = _index_load(primary_integration)
        if not isinstance(primary_data, dict):
            raise RuntimeError(
                f'No index for {primary_integration}; build its index first')
        primary_entities = primary_data.get('entities') or {}
        cutoff = datetime.now(timezone.utc) - timedelta(hours=24)
        candidates = []
        for entity, entity_data in primary_entities.items():
            try:
                if _snapshot_dt(entity_data[0]) > cutoff:
                    candidates.append(entity)
            except (TypeError, ValueError, IndexError):
                pass
        candidates.sort()
        _job_update(
            job_id, total=len(candidates),
            note=(f'Finding {companion_integration} snapshots for '
                  f'{len(candidates):,} {primary_integration} buildings…'))

        stamps = [cutoff.strftime('%Y-%m-%dT%H:%M:%S')]
        entities = {}
        unavailable = 0
        counter = {'n': 0}
        lock = threading.Lock()

        def work(entity):
            nonlocal unavailable
            try:
                found = _discover(companion_integration, entity, stamps,
                                  full_fallback=False)
            except Exception:
                found = None
            try:
                is_recent = bool(found and _snapshot_dt(found[1]) > cutoff)
            except (TypeError, ValueError):
                is_recent = False
            with lock:
                counter['n'] += 1
                if is_recent:
                    entities[found[0]] = [found[1], found[2]]
                else:
                    unavailable += 1
                if counter['n'] % 25 == 0:
                    _job_update(
                        job_id, done=counter['n'],
                        note=(f'Indexed {len(entities):,} companion buildings · '
                              f'{unavailable:,} without a recent Voyager sync'))

        if candidates:
            with ThreadPoolExecutor(max_workers=INDEX_WORKERS) as pool:
                list(pool.map(work, candidates))

        _job_update(job_id, done=len(candidates), note='Saving companion index…')
        payload = _index_save(companion_integration, entities, {
            'companionFor': primary_integration,
            'candidateBuildings': len(candidates),
            'indexed': len(entities),
            'unavailableWithin24Hours': unavailable,
            'seconds': round(time.time() - _job_get(job_id)['started'], 1),
        })
        _job_update(job_id, status='done', finished=time.time(), result={
            'integration': companion_integration,
            'companionFor': primary_integration,
            'buildings': len(entities),
            'unavailableWithin24Hours': unavailable,
            'builtAt': payload['builtAt'],
        })
    except Exception as e:
        _job_update(job_id, status='error', error=str(e), finished=time.time())


def _snippet(text: str, index: int, needle_len: int) -> str:
    start = max(0, index - SNIPPET_PAD)
    end   = min(len(text), index + needle_len + SNIPPET_PAD)
    frag  = re.sub(r'\s+', ' ', text[start:end]).strip()
    return ('…' if start > 0 else '') + frag + ('…' if end < len(text) else '')


# ── Fields mode: extract named field values into CSV rows ─────────────────────
#
# There's no schema database yet (each integration's file structure isn't
# recorded anywhere), so a requested field is matched purely by name rather
# than by a known position in a known object shape. Two strategies, tried
# in order:
#
#  1. If the file parses as JSON (true for every snapshot file seen so far),
#     walk the parsed tree. Whenever a dict directly contains one of the
#     requested keys, that dict IS "the object" — its sibling keys are
#     naturally the same record, so multiple requested fields land in one
#     row with no separate alignment step. This is stronger than blind
#     top-to-bottom pairing: two fields at different places in the file
#     (e.g. one field present on some units, absent on others) can't get
#     silently cross-matched, because rows are anchored to a single dict.
#  2. Otherwise (XML, or JSON that fails to parse), fall back to regex
#     key-value matching per field and zip the per-field value lists by
#     position — the literal "read top-to-bottom, same row" behavior.
#     This is the fallback the schema-free approach can't improve on
#     without knowing the format's structure.

def _extract_json_rows(node, fields: list, rows: list):
    """
    Recursively collect one row per dict that has ANY of `fields` as a direct
    key (blank for the fields it doesn't have) — walking in the document's own
    order, which for a JSON array of records is exactly record order.
    Appends into `rows` in place so a single call handles an entire document.
    """
    if isinstance(node, dict):
        if any(f in node for f in fields):
            rows.append({f: node.get(f, None) for f in fields})
        for v in node.values():
            if isinstance(v, (dict, list)):
                _extract_json_rows(v, fields, rows)
    elif isinstance(node, list):
        for item in node:
            if isinstance(item, (dict, list)):
                _extract_json_rows(item, fields, rows)


# JSON value token: quoted string (with escapes) | number | true|false|null.
_JSON_VALUE_RE = r'"(?:\\.|[^"\\])*"|-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?|true|false|null'


def _field_patterns(field: str):
    """Key-value shapes tried for one field name, most to least JSON-like."""
    esc = re.escape(field)
    return [
        re.compile(r'"' + esc + r'"\s*:\s*(' + _JSON_VALUE_RE + r')'),   # "Field": value
        re.compile(r'<' + esc + r'>(.*?)</' + esc + r'>', re.DOTALL),    # <Field>value</Field>
        re.compile(esc + r'\s*=\s*"([^"]*)"'),                          # Field="value"
    ]


def _coerce_value(raw: str):
    """A regex-captured fragment: unwrap a JSON token, else use it verbatim."""
    try:
        return json.loads(raw)
    except (json.JSONDecodeError, TypeError):
        return raw


def _extract_text_rows(body: str, fields: list):
    """
    Fallback for content that isn't valid JSON: match each field independently
    via regex, then zip the resulting value lists by position. This is the
    "assume top-to-bottom, same row" behavior — the best available without
    any structural information about the format.
    """
    per_field = {}
    for f in fields:
        values = []
        for pattern in _field_patterns(f):
            found = pattern.findall(body)
            if found:
                values = [_coerce_value(v) for v in found]
                break
        per_field[f] = values

    max_len = max((len(v) for v in per_field.values()), default=0)
    return [
        {f: (per_field[f][i] if i < len(per_field[f]) else None) for f in fields}
        for i in range(max_len)
    ]


def _extract_rows(body: str, fields: list):
    """Try the structural JSON approach first; fall back to positional regex."""
    try:
        parsed = json.loads(body)
    except json.JSONDecodeError:
        return _extract_text_rows(body, fields)
    rows = []
    _extract_json_rows(parsed, fields, rows)
    return rows


def _csv_cell(value):
    """Render an extracted value (possibly non-scalar) as CSV-safe text."""
    if value is None:
        return ''
    if isinstance(value, bool):
        return 'true' if value else 'false'
    if isinstance(value, (dict, list)):
        return json.dumps(value)
    return str(value)


def _strip_building_prefix(entity: str) -> str:
    """'building_10238' -> '10238'. Falls through unchanged if not prefixed."""
    if entity.lower().startswith('building_'):
        return entity.split('_', 1)[1]
    return entity


def _snapshot_link(entity: str, snapshot: str, org_id) -> str:
    """Build the snapshot-viewer URL for one exported building/snapshot."""
    if not org_id or not entity or not snapshot:
        return ''
    try:
        reference_time = _snapshot_dt(snapshot).astimezone(timezone.utc).isoformat(
            timespec='milliseconds').replace('+00:00', 'Z')
    except (TypeError, ValueError):
        return ''
    query = urllib.parse.urlencode([
        ('tab', 'mits'),
        ('org_id', _csv_cell(org_id)),
        ('building_id', _strip_building_prefix(entity)),
        ('reference_time', reference_time),
        ('num_before', '1'),
        ('num_after', '1'),
        ('gc_search_mode', 'mc_id'),
    ])
    return f'https://app.meetelise.com/tools/snapshot-viewer?{query}'


# ── Field schema inference ──────────────────────────────────────────────────
#
# There's no declared schema anywhere, so one is inferred by sampling real
# files and walking their JSON structure. The key correctness problem: object
# identity has to be a STRUCTURAL PATH ("units[]", "units[].building"), not
# "any dict that happens to have this key" — otherwise a field named `id`
# occurring on a listing, its building, and its neighborhood all look like
# the same thing.
#
# That runs into a second problem on real data: some containers are keyed by
# a per-record identifier rather than a fixed field name (AppFolio's
# units.json.gz is `{"<property-uuid>": [...]}` — one random UUID key per
# file, never the same key twice). Naively including that UUID as a literal
# path segment would mean every building gets its own path and nothing ever
# groups. This is only detectable by comparing MULTIPLE sampled files: a real
# field name recurs across files; a per-file identifier never does. Detecting
# that is the reason schema inference needs a sample of files, not just one.

SCHEMA_SAMPLE_SIZE = 30   # files fetched (real GETs, not just listings) to infer a schema
SCHEMA_CACHE_TTL    = 600
_schema_cache: dict = {}   # (integration, filename) -> {'data': {...}, 'ts': ...}


def _walk_json(node, path: tuple, visit):
    """
    Depth-first walk calling visit(path, dict_instance) for every dict
    encountered. `path` uses '[]' for list traversal and the literal key name
    for dict traversal — no wildcarding here; only comparing paths ACROSS
    multiple files (in _detect_dynamic_parents) can tell a real field name
    from a per-file identifier, so a single walk can't decide that itself.
    """
    if isinstance(node, dict):
        visit(path, node)
        for k, v in node.items():
            if isinstance(v, (dict, list)):
                _walk_json(v, path + (k,), visit)
    elif isinstance(node, list):
        for item in node:
            if isinstance(item, (dict, list)):
                    _walk_json(item, path + ('[]',), visit)


def _xml_name(tag: str) -> str:
    """Return an XML element/attribute's local name without its namespace."""
    return tag.rsplit('}', 1)[-1].split(':')[-1]


def _xml_value(element):
    """Convert an XML element to the dict/list/scalar shape used by JSON paths.

    Attributes are prefixed with ``@`` so they cannot collide with child tags,
    and mixed-content text is exposed as ``#text``. Repeated sibling tags
    become lists, which gives MITS records such as Floorplan and ILS_Unit the
    same stable ``[]`` path semantics as JSON arrays.
    """
    children = list(element)
    attributes = {f'@{_xml_name(key)}': value for key, value in element.attrib.items()}
    text = (element.text or '').strip()

    if not children:
        if not attributes:
            return text
        if text:
            attributes['#text'] = text
        return attributes

    result = dict(attributes)
    grouped = {}
    for child in children:
        grouped.setdefault(_xml_name(child.tag), []).append(_xml_value(child))
    for name, values in grouped.items():
        result[name] = values if len(values) > 1 else values[0]
    if text:
        result['#text'] = text
    return result


def _parse_structured_body(body: str):
    """Parse JSON or XML into one common tree; return (tree, format)."""
    try:
        return json.loads(body), 'json'
    except (json.JSONDecodeError, TypeError):
        pass
    try:
        root = ET.fromstring(body)
    except (ET.ParseError, TypeError):
        return None, None
    return {_xml_name(root.tag): _xml_value(root)}, 'xml'


def _detect_dynamic_parents(walks: list):
    """
    walks: [(file_index, path_tuple, dict_instance), ...] across every sampled
    file. Returns the set of paths at which a dict's OWN keys are per-file
    identifiers rather than real field names — i.e. paths where descending
    one level further via a literal key should instead wildcard.

    Signal: for every dict occurring at a given path, look at every distinct
    key it actually has (across however many files/instances land at that
    same path), and how many DIFFERENT files each key appeared in. A real
    field name (e.g. "building") recurs — every file's dict at that path has
    it. A per-file identifier (a UUID, a numeric id) is by definition
    different in every file, so it's normally seen in exactly one file.

    Requiring literally ZERO keys to ever recur turns out too brittle on real
    data: e.g. AppFolio's per-unit CustomFields are keyed by a custom-field-
    definition UUID that's usually unique per property, but a shared config
    across a couple of properties in the same portfolio can make one or two
    keys coincidentally recur — which shouldn't be enough to call the whole
    container "a fixed set of fields". So the bar is proportional: at least 2
    distinct keys, and fewer than 30% of them ever recur across files.

    Concretely, this is what catches AppFolio's units.json.gz shape —
    {"<one-property-uuid-per-file>": [...]} — where the root dict (path=())
    has exactly one key, and that key is a different UUID in every sampled
    file.
    """
    key_to_files = {}   # dict_path -> {key_name: {file_index, ...}}
    for file_idx, path, d in walks:
        if not isinstance(d, dict):
            continue
        bucket = key_to_files.setdefault(path, {})
        for k in d.keys():
            bucket.setdefault(k, set()).add(file_idx)

    dynamic = set()
    for path, keys in key_to_files.items():
        if len(keys) < 2:
            continue
        recurring = sum(1 for files in keys.values() if len(files) > 1)
        if recurring / len(keys) < 0.3:
            dynamic.add(path)
    return dynamic


def _rewrite_path(path: tuple, dynamic_parents: set) -> tuple:
    """
    Substitute '*' for any literal-key segment whose immediate parent is in
    `dynamic_parents`. Used identically at schema-build time and at
    extraction time, so what the dropdown showed is exactly what a search
    matches against.

    The parent check MUST use the prefix already rewritten so far (`out`),
    not the original literal prefix (`path[:i]`) — dynamic_parents entries
    are themselves expressed with earlier wildcards already applied (e.g.
    ('*', '[]')), so checking against the still-literal prefix (e.g.
    ('f9d53f3b-...', '[]')) would never match and silently skip every
    substitution below the first dynamic level.
    """
    out = []
    for seg in path:
        if seg != '[]' and tuple(out) in dynamic_parents:
            out.append('*')
        else:
            out.append(seg)
    return tuple(out)


def _path_to_str(path: tuple) -> str:
    return '.'.join(path)


def _str_to_path(s: str) -> tuple:
    return tuple(s.split('.')) if s else ()


def _humanize_path(path: tuple) -> str:
    if not path:
        return 'top level'
    parts = ['item' if seg == '[]' else '(any key)' if seg == '*' else seg for seg in path]
    return ' › '.join(parts)


def _infer_dynamic_parents(walks: list, max_iterations: int = 6) -> set:
    """
    Fixed-point wrapper around _detect_dynamic_parents. One pass isn't enough:
    a nested dynamic container (e.g. AppFolio's per-unit "CustomFields", keyed
    by custom-field-definition UUID) sits BELOW an outer per-file identifier
    (the property UUID). Until that outer identifier is collapsed to a
    wildcard, every path below it is still scoped to a single file, so cross-
    file comparison of the nested level is structurally impossible — it looks
    dynamic-or-not at random depending on how many array items one file
    happens to have, not on whether it actually varies across files.

    Each iteration rewrites the raw walks with the current best-known dynamic
    set, then re-runs detection on top of that; newly-found dynamic paths are
    only ever added, never removed, so this converges (bounded by path depth,
    which is small in practice — the iteration cap is a generous backstop).
    """
    dynamic = set()
    for _ in range(max_iterations):
        rewritten = [(fi, _rewrite_path(p, dynamic), d) for fi, p, d in walks]
        newly_found = _detect_dynamic_parents(rewritten) - dynamic
        if not newly_found:
            break
        dynamic |= newly_found
    return dynamic


def _array_item_fields(items: list) -> set:
    """Known paths within one array item, stopping at nested arrays.

    Nested dicts are flattened with dotted paths. A nested list is retained as
    a JSON-valued leaf here; it can be expanded separately when its containing
    object type is selected.
    """
    fields = set()

    def visit(value, prefix=()):
        if isinstance(value, dict):
            for key, child in value.items():
                child_path = prefix + (key,)
                if isinstance(child, dict):
                    visit(child, child_path)
                else:
                    fields.add(child_path)
        elif prefix:
            fields.add(prefix)

    for item in items:
        if isinstance(item, dict):
            visit(item)
        else:
            fields.add(('value',))
    return fields


def _arrays_below_object(d: dict):
    """Yield arrays reachable from an object without crossing another array."""
    found = []

    def visit(value, prefix=()):
        if not isinstance(value, dict):
            return
        for key, child in value.items():
            child_path = prefix + (key,)
            if isinstance(child, list):
                found.append((child_path, child))
            elif isinstance(child, dict):
                visit(child, child_path)

    visit(d)
    return found


def build_field_schema(bodies: list) -> dict:
    """
    bodies: raw (already decompressed) file contents from a sample of
    buildings for one integration+filename. Returns the object types found —
    each a structural path with the scalar fields seen directly on it — plus
    the dynamic-parent set extraction needs to match consistently later.
    """
    walks = []
    parsed_count = 0
    formats = set()
    for file_idx, body in enumerate(bodies):
        doc, body_format = _parse_structured_body(body)
        if doc is None:
            continue
        parsed_count += 1
        formats.add(body_format)
        _walk_json(doc, (), lambda path, d, fi=file_idx: walks.append((fi, path, d)))

    if parsed_count == 0:
        return {'objectTypes': [], 'dynamicParents': [], 'jsonCompatible': False,
                'structuredCompatible': False, 'format': None}

    dynamic_parents = _infer_dynamic_parents(walks)

    groups = {}   # rewritten_path -> sampled field inventory + occurrence metadata
    for file_idx, path, d in walks:
        rp = _rewrite_path(path, dynamic_parents)
        g = groups.setdefault(rp, {
            'fields': {}, 'objectFields': set(), 'arrays': {},
            'count': 0, 'files': set(),
        })
        g['count'] += 1
        g['files'].add(file_idx)
        for k, v in d.items():
            g['objectFields'].add(k)
            if not isinstance(v, (dict, list)) and k not in g['fields']:
                g['fields'][k] = _csv_cell(v)   # scalars only — nested values are their own object type
        for array_path, items in _arrays_below_object(d):
            array = g['arrays'].setdefault(array_path, {
                'fields': set(), 'seen': 0, 'single': 0, 'multiple': 0,
            })
            array['seen'] += 1
            if len(items) == 1:
                array['single'] += 1
            elif len(items) > 1:
                array['multiple'] += 1
            array['fields'].update(_array_item_fields(items))

    object_types = [
        {
            'path':   _path_to_str(path),
            'label':  _humanize_path(path),
            'count':  g['count'],
            'files':  len(g['files']),
            'fields': [{'name': k, 'sample': v} for k, v in sorted(g['fields'].items())],
            # Whole-object extraction includes every direct property. Nested
            # dict/list values are preserved as JSON cells by _csv_cell,
            # while the individual-field dropdown remains scalar-only.
            'objectFields': [{'name': k} for k in sorted(g['objectFields'])],
            'arrays': [
                {
                    'path': '.'.join(array_path),
                    'label': ' › '.join(array_path),
                    'fields': [{'path': '.'.join(field_path)}
                               for field_path in sorted(array['fields'])],
                    'seen': array['seen'],
                    'single': array['single'],
                    'multiple': array['multiple'],
                }
                for array_path, array in sorted(g['arrays'].items())
            ],
        }
        for path, g in groups.items() if g['objectFields']
    ]
    object_types.sort(key=lambda o: -o['count'])

    return {
        'objectTypes':     object_types,
        'dynamicParents':  [_path_to_str(p) for p in dynamic_parents],
        # jsonCompatible remains true for backward compatibility with older
        # clients where it means "has a navigable structured schema".
        'jsonCompatible':  True,
        'structuredCompatible': True,
        'format':           next(iter(formats)) if len(formats) == 1 else 'mixed',
        'filesParsed':     parsed_count,
    }


def _get_field_schema(integration: str, file_name: str, refresh: bool = False):
    file_name = _canonical_file_name(integration, file_name)
    key = (integration, file_name)
    entry = _schema_cache.get(key)
    if not refresh and entry and (time.time() - entry['ts']) < SCHEMA_CACHE_TTL:
        return entry['data']

    data = _index_load(integration)
    if not data:
        raise RuntimeError('No index for this integration')
    entities = data.get('entities', {})
    candidates = [e for e, (snap, files) in entities.items()
                  if _file_variant(files, integration, file_name)]
    if not candidates:
        schema = {'objectTypes': [], 'dynamicParents': [], 'jsonCompatible': False,
                  'sampleSize': 0, 'filesParsed': 0}
        _schema_cache[key] = {'data': schema, 'ts': time.time()}
        return schema

    step   = max(1, len(candidates) // SCHEMA_SAMPLE_SIZE)
    sample = candidates[::step][:SCHEMA_SAMPLE_SIZE]

    bodies = []
    lock = threading.Lock()

    def fetch(entity):
        snapshot, files = entities[entity]
        actual_file = _file_variant(files, integration, file_name)
        if not actual_file:
            return
        s3_key = f'{ROOT}{integration}/{entity}/{snapshot}/{actual_file}'
        try:
            text = _fetch_text(s3_key)
        except Exception:
            return
        with lock:
            bodies.append(text)

    with ThreadPoolExecutor(max_workers=min(INDEX_WORKERS, len(sample))) as pool:
        list(pool.map(fetch, sample))

    schema = build_field_schema(bodies)
    schema['sampleSize'] = len(sample)
    _schema_cache[key] = {'data': schema, 'ts': time.time()}
    return schema


def _normalize_field_specs(raw_specs: list) -> list:
    """
    Accepts a list of plain strings (manually typed — today's original
    behavior, matched by name wherever it occurs) or {'name','path'} dicts
    (picked from the schema dropdown — matched only at that exact structural
    path) and returns a deduplicated, ordered list of {'name','path','column'}.

    'column' is the CSV/preview header. It's just `name` unless the SAME name
    is requested from more than one path (e.g. "id" from both a listing and
    its building) — then each gets a disambiguated header so two different
    things never collide under one column.
    """
    specs, seen = [], set()
    for item in raw_specs:
        if isinstance(item, str):
            name, path = item.strip(), None
        elif isinstance(item, dict):
            name = (item.get('name') or '').strip()
            path = item.get('path')
            path = path.strip() if isinstance(path, str) and path.strip() else None
        else:
            continue
        if not name or (name, path) in seen:
            continue
        seen.add((name, path))
        specs.append({'name': name, 'path': path})

    paths_per_name = {}
    for s in specs:
        paths_per_name.setdefault(s['name'], set()).add(s['path'])
    for s in specs:
        if len(paths_per_name[s['name']]) == 1:
            s['column'] = s['name']
        else:
            label = _humanize_path(_str_to_path(s['path'])) if s['path'] else 'manual'
            s['column'] = f"{s['name']} ({label})"
    return specs


def _normalize_join_specs(raw_join, label: str):
    """Normalize one join-side field and require an explicit field name."""
    if isinstance(raw_join, str):
        raw_join = {'name': raw_join}
    if not isinstance(raw_join, dict):
        raise ValueError(f'{label} must be an object with name and optional path')
    specs = _normalize_field_specs([raw_join])
    if not specs:
        raise ValueError(f'{label} is required')
    return specs[0]


def _validate_join_object_scope(join_spec: dict, output_specs: list, label: str):
    """Require joined output fields to come from the join key's object.

    Path-scoped extraction creates one row per object instance. Joining a key
    from a parent Unit object to fields from a child unitSpace object (or vice
    versa) loses their parent/child identity and can cross-match equal unit
    numbers from different properties. All fields on one joined side must
    therefore share the join field's exact structural path. Schema-free manual
    fields remain supported when both the fields and join key are unscoped.
    """
    mismatched = [spec for spec in output_specs
                  if spec.get('path') != join_spec.get('path')]
    if mismatched:
        join_path = _humanize_path(_str_to_path(join_spec.get('path'))) \
            if join_spec.get('path') else 'manual/unscoped fields'
        bad_paths = sorted({
            _humanize_path(_str_to_path(spec.get('path')))
            if spec.get('path') else 'manual/unscoped fields'
            for spec in mismatched
        })
        raise ValueError(
            f'{label} must come from the same object as every selected field. '
            f'The join field is scoped to {join_path}; incompatible output: '
            f'{", ".join(bad_paths)}. Select the parent object and expand its '
            f'child array instead of joining a parent key to child-object rows.')


def _normalize_array_expansion_requests(raw, label='arrayExpansions'):
    if raw is None:
        return []
    if not isinstance(raw, list):
        raise ValueError(f'{label} must be a list')
    normalized, seen = [], set()
    for index, item in enumerate(raw, 1):
        if not isinstance(item, dict):
            raise ValueError(f'{label} item {index} must be an object')
        object_path = item.get('objectPath')
        array_path = item.get('arrayPath')
        if not isinstance(object_path, str) or not isinstance(array_path, str) or not array_path:
            raise ValueError(f'{label} item {index} needs objectPath and arrayPath')
        key = (object_path, array_path)
        if key not in seen:
            seen.add(key)
            normalized.append({'objectPath': object_path, 'arrayPath': array_path})
    return normalized


def _safe_column_path(path: str) -> str:
    return re.sub(r'[^A-Za-z0-9]+', '__', path).strip('_') or 'array'


def _resolve_array_expansions(schema: dict, requests: list):
    """Resolve client array choices against the sampled server-side schema."""
    objects = {item.get('path', ''): item for item in schema.get('objectTypes', [])}
    expansions = []
    for request in requests:
        object_type = objects.get(request['objectPath'])
        if not object_type:
            raise ValueError(f"unknown object path {request['objectPath']!r}")
        array = next((item for item in object_type.get('arrays', [])
                      if item.get('path') == request['arrayPath']), None)
        if not array:
            raise ValueError(
                f"unknown array {request['arrayPath']!r} for object {request['objectPath']!r}")
        base = _safe_column_path(request['arrayPath'])
        fields = []
        for field in array.get('fields', []):
            field_path = field.get('path', '')
            if field_path:
                fields.append({
                    'path': field_path,
                    'column': f'{base}__{_safe_column_path(field_path)}',
                })
        expansions.append({
            **request,
            'countColumn': f'{base}__array_count',
            'statusColumn': f'{base}__expansion_status',
            'fields': fields,
        })
    return expansions


def _nested_value(value, path: str):
    current = value
    for segment in path.split('.') if path else []:
        if not isinstance(current, dict) or segment not in current:
            return None
        current = current[segment]
    return current


def _apply_array_expansions(rows: list, expansions: list):
    """Flatten opted-in arrays only when they contain exactly one item."""
    for row in rows:
        for expansion in expansions:
            value = _nested_value(row, expansion['arrayPath'])
            if not isinstance(value, list):
                count, status, item = 0, 'missing', None
            elif len(value) == 0:
                count, status, item = 0, 'empty', None
            elif len(value) == 1:
                count, status, item = 1, 'expanded', value[0]
            else:
                count, status, item = len(value), 'multiple', None
            row[expansion['countColumn']] = count
            row[expansion['statusColumn']] = status
            for field in expansion['fields']:
                row[field['column']] = (
                    item if field['path'] == 'value' and not isinstance(item, dict)
                    else _nested_value(item, field['path']) if isinstance(item, dict)
                    else None)
    return rows


def _normalize_related_files(raw_related: list, primary_integration: str = ''):
    """Validate and normalize related-file join definitions from the API."""
    if raw_related is None:
        return []
    if not isinstance(raw_related, list):
        raise ValueError('relatedFiles must be a list')

    normalized = []
    for i, item in enumerate(raw_related, 1):
        if not isinstance(item, dict):
            raise ValueError(f'related file {i} must be an object')
        filename = item.get('filename', '')
        if not isinstance(filename, str) or not filename.strip() or '/' in filename:
            raise ValueError(f'related file {i} has an invalid filename')
        rel_integration = _safe_integration(item.get('integration') or primary_integration)
        if not rel_integration:
            raise ValueError(f'related file {i} has an invalid integration')
        if primary_integration and rel_integration not in _allowed_related_integrations(primary_integration):
            allowed = ', '.join(sorted(_allowed_related_integrations(primary_integration)))
            raise ValueError(f'{rel_integration} cannot be joined to {primary_integration}; allowed: {allowed}')
        fields = _normalize_field_specs(item.get('fields') or [])
        if not fields:
            raise ValueError(f'related file {filename!r} needs at least one field')
        primary_join = _normalize_join_specs(item.get('primaryJoin'),
                                             f'primaryJoin for {filename!r}')
        related_join = _normalize_join_specs(item.get('relatedJoin'),
                                             f'relatedJoin for {filename!r}')
        join_type = item.get('joinType', 'left')
        if join_type not in {'inner', 'left', 'right', 'full'}:
            raise ValueError(
                f'joinType for {filename!r} must be inner, left, right, or full')
        normalized.append({
            'integration': rel_integration,
            'filename': _canonical_file_name(rel_integration, filename.strip()),
            'primaryJoin': primary_join,
            'relatedJoin': related_join,
            'joinType': join_type,
            'fields': fields,
            'arrayExpansionRequests': _normalize_array_expansion_requests(
                item.get('arrayExpansions'), f'arrayExpansions for {filename!r}'),
        })
    return normalized


CONDITION_OPERATORS = {'eq', 'contains', 'not_contains', 'ne', 'gt', 'lt'}


def _normalize_conditions(raw_conditions, primary_integration: str, related_files: list):
    """Normalize grouped filters and validate each field source/operator."""
    if raw_conditions is None:
        return []
    if not isinstance(raw_conditions, list):
        raise ValueError('conditions must be a list of groups')

    normalized = []
    for group_index, raw_group in enumerate(raw_conditions, 1):
        if not isinstance(raw_group, dict):
            raise ValueError(f'condition group {group_index} must be an object')
        logic = raw_group.get('logic', 'all')
        if logic not in ('all', 'any'):
            raise ValueError(f'condition group {group_index} logic must be all or any')
        raw_items = raw_group.get('conditions') or []
        if not isinstance(raw_items, list) or not raw_items:
            raise ValueError(f'condition group {group_index} must contain conditions')
        items = []
        for condition_index, raw in enumerate(raw_items, 1):
            if not isinstance(raw, dict):
                raise ValueError(f'condition {group_index}.{condition_index} must be an object')
            source = raw.get('source', 'primary')
            if source == 'primary':
                source_index = None
            elif isinstance(source, str) and source.startswith('related:'):
                try:
                    source_index = int(source.split(':', 1)[1])
                except ValueError:
                    source_index = -1
                if source_index < 0 or source_index >= len(related_files):
                    raise ValueError(f'condition {group_index}.{condition_index} has an invalid related source')
            else:
                raise ValueError(f'condition {group_index}.{condition_index} has an invalid source')
            field = _normalize_join_specs(raw.get('field'),
                                          f'field for condition {group_index}.{condition_index}')
            operator = raw.get('operator')
            if operator not in CONDITION_OPERATORS:
                raise ValueError(f'condition {group_index}.{condition_index} has an invalid operator')
            value = raw.get('value')
            if value is None:
                value = ''
            if isinstance(value, (dict, list)):
                value = _csv_cell(value)
            else:
                value = str(value)
            items.append({
                'sourceIndex': source_index,
                'field': field,
                'operator': operator,
                'value': value,
            })
        normalized.append({'logic': logic, 'conditions': items})
    return normalized


def _condition_value_matches(actual, operator: str, expected: str) -> bool:
    actual_text = _csv_cell(actual).strip()
    expected_text = str(expected).strip()
    if operator == 'eq':
        # An absent field is not an empty one. A rule testing for an empty
        # value (RentCafe "Status: Blank") must match only rows that actually
        # carry a blank status, not rows where the field is missing entirely
        # — e.g. unit_details-only rows, which have no status field at all.
        if actual is None and not expected_text:
            return False
        return actual_text.casefold() == expected_text.casefold()
    if operator == 'ne':
        return actual_text.casefold() != expected_text.casefold()
    if operator == 'contains':
        return expected_text.casefold() in actual_text.casefold()
    if operator == 'not_contains':
        return expected_text.casefold() not in actual_text.casefold()
    if not actual_text or not expected_text:
        return False
    try:
        left, right = float(actual_text), float(expected_text)
    except (TypeError, ValueError):
        left, right = actual_text.casefold(), expected_text.casefold()
    return left > right if operator == 'gt' else left < right


def _conditions_match(groups: list, values: dict) -> bool:
    for group in groups:
        results = [
            _condition_value_matches(values.get(id(condition)), condition['operator'], condition['value'])
            for condition in group['conditions']
        ]
        if (group['logic'] == 'any' and not any(results)) or \
           (group['logic'] == 'all' and not all(results)):
            return False
    return True


def _extract_rows_v2(body: str, specs: list, dynamic_parents: set):
    """
    specs: normalized [{'name','path','column'}, ...] from _normalize_field_specs.

    Fields with path=None group together and extract via the original "any
    dict with this key" walk (unchanged from before schema inference existed
    — still the only option for a field the sample didn't capture, or for
    non-JSON content). Each distinct non-None path extracts precisely,
    matched only against dicts occurring at that exact structural path — two
    fields sharing a path are guaranteed to be siblings on the same object;
    fields from different paths never get cross-matched.

    Every row carries '_group', a human label for which object it came from,
    so mixing fields from different objects in one export stays legible
    (surfaced as an object_type column) instead of just silently sparse.
    """
    legacy  = [s for s in specs if not s['path']]
    by_path = {}
    for s in specs:
        if s['path']:
            by_path.setdefault(s['path'], []).append(s)

    doc, _body_format = _parse_structured_body(body)
    if doc is None:
        # No structure available at all — everything falls back to the
        # positional zip, keyed by name; paths are meaningless without a tree.
        name_to_columns = {}
        for s in specs:
            name_to_columns.setdefault(s['name'], []).append(s['column'])
        text_rows = _extract_text_rows(body, list(name_to_columns.keys()))
        rows = []
        for r in text_rows:
            row = {'_group': 'text'}
            for name, cols in name_to_columns.items():
                for col in cols:
                    row[col] = r.get(name)
            rows.append(row)
        return rows

    rows = []

    if legacy:
        raw_rows = []
        _extract_json_rows(doc, [s['name'] for s in legacy], raw_rows)
        name_to_columns = {}
        for s in legacy:
            name_to_columns.setdefault(s['name'], []).append(s['column'])
        for r in raw_rows:
            row = {'_group': 'manual'}
            for name, cols in name_to_columns.items():
                for col in cols:
                    row[col] = r.get(name)
            rows.append(row)

    if by_path:
        def visit(path, d):
            rp = _path_to_str(_rewrite_path(path, dynamic_parents))
            group = by_path.get(rp)
            if group:
                row = {s['column']: d.get(s['name'], None) for s in group}
                row['_group'] = _humanize_path(_str_to_path(rp)) if rp else 'top level'
                rows.append(row)
        _walk_json(doc, (), visit)

    return rows


def _resolve_org_building_filter(org: str, building_filter: str,
                                 exclude_students: bool = False,
                                 exclude_applications: bool = False,
                                 require_launched_on_leasing: bool = False):
    """Shared by every search mode: -> (allowed_entity_set_or_None, filter_note)."""
    allowed = None
    notes = []
    if org:
        allowed = snowflake_db.building_ids_for_org(org)
        if allowed is None:
            notes.append('organization filter unavailable')
    if building_filter:
        wanted = {b.strip() for b in re.split(r'[\s,]+', building_filter) if b.strip()}
        wanted = {b if b.lower().startswith('building_') else f'building_{b}'
                  for b in wanted}
        allowed = wanted if allowed is None else (allowed & wanted)
    if exclude_students or exclude_applications:
        try:
            metadata_allowed, metadata_notes = snowflake_db.availability_filter_ids(
                exclude_students=exclude_students,
                exclude_applications=exclude_applications)
            notes.extend(metadata_notes)
            if metadata_allowed is not None:
                allowed = metadata_allowed if allowed is None else (allowed & metadata_allowed)
        except Exception as e:
            # Search remains useful without optional Snowflake filters;
            # surface the reason in the summary instead of failing the S3 job.
            notes.append(str(e))
    if require_launched_on_leasing:
        try:
            launched = snowflake_db.launched_on_leasing_building_ids()
            allowed = launched if allowed is None else (allowed & launched)
        except Exception as e:
            notes.append(f'Leasing-launch filter unavailable: {e}')
    return allowed, ' · '.join(dict.fromkeys(notes))


def _build_targets(entities: dict, integration: str, file_name: str, allowed, as_of):
    """
    (entity, snapshot, key) tuples to process. When as_of is None, snapshot/key
    come straight from the index — the fast path, no extra S3 calls needed to
    find them. When as_of is set, snapshot/key are left as None placeholders;
    probe() resolves them live per building, since the index only ever records
    each building's LATEST snapshot, not one at an arbitrary date — whether a
    building had the target file in its *latest* snapshot says nothing about
    whether it had that file in whatever snapshot existed as of the cutoff.
    """
    file_name = _canonical_file_name(integration, file_name)
    if as_of is None:
        # Index construction already applied the 24-hour eligibility window.
        # Once built, the index is the complete latest-search scope even when
        # its recorded snapshots later become more than 24 hours old.
        targets = []
        for entity, (snapshot, files) in entities.items():
            if allowed is not None and entity not in allowed:
                continue
            actual_file = _file_variant(files, integration, file_name)
            if actual_file:
                targets.append(
                    (entity, snapshot,
                     f'{ROOT}{integration}/{entity}/{snapshot}/{actual_file}')
                )
    else:
        targets = [
            (entity, None, None) for entity in entities
            if allowed is None or entity in allowed
        ]
    targets.sort()
    return targets


def _fetch_text(key: str) -> str:
    """GET + gunzip (if applicable) + decode. Raises on failure — caller decides
    how to treat a ClientError (e.g. NoSuchKey is routine for dated searches)."""
    raw = s3().get_object(Bucket=BUCKET, Key=key)['Body'].read()
    if key.endswith('.gz'):
        try:
            raw = gzip_module.decompress(raw)
        except Exception:
            pass
    return raw.decode('utf-8', errors='replace')


def _enrich_with_snowflake(job_id: str, entity_list: list, timeout=None):
    """
    Building name/org lookup for the rows actually being returned. Runs through
    a throwaway single-worker pool so a stuck connection (seen in practice: TCP
    SYN_SENT that never resolves, e.g. an OCSP check blocked by network/VPN
    policy) times out instead of hanging the whole job. shutdown(wait=False)
    means the stuck thread is abandoned, not joined — the caller doesn't wait
    for it to die. Returns (meta_dict_or_None, column_map_or_None, error_or_None).

    `timeout` overrides ENRICH_TIMEOUT for callers that can afford to wait; a
    cold warehouse routinely needs far longer than the interactive default.
    """
    if not entity_list:
        return None, None, None
    if not snowflake_db.configured():
        return None, None, 'Snowflake is not configured: missing credentials'

    _job_update(job_id, note='Loading building details…')
    pool = ThreadPoolExecutor(max_workers=1)
    try:
        future = pool.submit(snowflake_db.lookup, entity_list)
        limit = timeout or ENRICH_TIMEOUT
        meta = future.result(timeout=limit)
        return meta, snowflake_db.column_map(), None
    except FutureTimeoutError:
        return None, None, (f'Snowflake lookup timed out after {limit}s '
                            f'(network/connection issue) — showing results without '
                            f'building details')
    except Exception as e:
        return None, None, str(e)
    finally:
        pool.shutdown(wait=False)


def _run_search_job(job_id: str, integration: str, file_name: str, text: str,
                    org: str = '', building_filter: str = '', as_of=None,
                    include_students: bool = False, max_results: int | None = None):
    try:
        data = _index_load(integration)
        if not data:
            raise RuntimeError('No index for this integration')
        entities = data.get('entities', {})

        # Optional filters are applied BEFORE any S3 reads, so narrowing by
        # organization or building id cuts the GET count proportionally.
        if org:
            _job_update(job_id, note='Filtering by organization…')
        allowed, filter_note = _resolve_org_building_filter(
            org, building_filter, exclude_students=not include_students)

        targets = _build_targets(
            entities, integration, file_name, allowed, as_of)
        _job_update(job_id, total=len(targets),
                   note=(f'Resolving snapshots as of {as_of.isoformat()}…'
                         if as_of else 'Reading snapshots…'))

        matches = []
        errors  = 0
        no_snapshot = 0   # buildings with no snapshot at/before the cutoff
        lock    = threading.Lock()
        counter = {'n': 0}
        result_limit = max_results or RESULT_CAP
        limit_reached = threading.Event()

        def probe(target):
            nonlocal errors, no_snapshot
            if limit_reached.is_set():
                return
            entity, snapshot, key = target

            if as_of is not None:
                entity_prefix = f'{ROOT}{integration}/{entity}/'
                snap_prefix = _snapshot_prefix_before(entity_prefix, as_of)
                if not snap_prefix:
                    with lock:
                        no_snapshot += 1
                        counter['n'] += 1
                    return
                snapshot = snap_prefix[len(entity_prefix):].rstrip('/')
                actual_file = _file_variant(_snapshot_files(entity_prefix, snapshot), integration, file_name)
                if not actual_file:
                    with lock:
                        counter['n'] += 1
                    return
                key = snap_prefix + actual_file

            try:
                body = _fetch_text(key)
            except ClientError as e:
                # Dated searches resolve the snapshot independently of whether
                # it actually has this file — a missing key here just means
                # this building didn't produce that file for that snapshot,
                # not a real error.
                if e.response.get('Error', {}).get('Code') in ('NoSuchKey', '404'):
                    with lock:
                        counter['n'] += 1
                    return
                with lock:
                    errors += 1
                    counter['n'] += 1
                return
            except Exception:
                with lock:
                    errors += 1
                    counter['n'] += 1
                return

            idx = body.find(text)
            hit = None
            if idx >= 0:
                hit = {
                    'entity':   entity,
                    'snapshot': snapshot,
                    'key':      key,
                    'count':    body.count(text),
                    'snippet':  _snippet(body, idx, len(text)),
                }
            with lock:
                counter['n'] += 1
                if hit and len(matches) < result_limit:
                    matches.append(hit)
                    if len(matches) >= result_limit:
                        limit_reached.set()
                if counter['n'] % 25 == 0:
                    _job_update(job_id, done=counter['n'], note=f'{len(matches)} found')

        if targets:
            with ThreadPoolExecutor(max_workers=SEARCH_WORKERS) as pool:
                list(pool.map(probe, targets))

        matches.sort(key=lambda m: m['entity'])
        shown = matches

        meta, cmap, enrich_error = _enrich_with_snowflake(job_id, [m['entity'] for m in shown])
        if meta:
            for m in shown:
                row = meta.get(m['entity'])
                if not row:
                    continue
                m['building'] = {
                    'name':    row.get(cmap['name']) if cmap['name'] else None,
                    'org':     row.get(cmap['org']) if cmap['org'] else None,
                    'orgName': row.get('ORGANIZATION_NAME'),
                    'fields':  {k: v for k, v in row.items() if v is not None},
                }

        _job_update(job_id, done=counter['n'], status='done', finished=time.time(),
                    result={
                        'integration': integration,
                        'fileName':    file_name,
                        'text':        text,
                        'org':         org,
                        'includeStudents': include_students,
                        'resultLimit': max_results,
                        'asOf':        as_of.isoformat() if as_of else None,
                        'searched':    counter['n'],
                        'buildings':   len(entities),
                        'noSnapshot':  no_snapshot,
                        'matchCount':  len(matches),
                        'matches':     shown,
                        'truncated':   limit_reached.is_set(),
                        'errors':      errors,
                        'filterNote':  filter_note,
                        'enrichError': enrich_error,
                        'enrichCredentialIssue': snowflake_db.credential_error(enrich_error),
                    })
    except Exception as e:
        _job_update(job_id, status='error', error=str(e), finished=time.time())


def _cleanup_old_exports():
    """Sweep saved exports past EXPORT_MAX_AGE. Called opportunistically at the
    start of each fields job rather than on a timer — this is a low-traffic
    dev tool, not a service that needs a scheduler."""
    if not os.path.isdir(EXPORT_DIR):
        return
    cutoff = time.time() - EXPORT_MAX_AGE
    with _history_lock:
        favorite_ids = {entry.get('id') for entry in _history_read()
                        if entry.get('favorite')}
    for fn in os.listdir(EXPORT_DIR):
        if fn in {os.path.basename(HISTORY_PATH), os.path.basename(HISTORY_PATH) + '.tmp'}:
            continue
        stem, extension = os.path.splitext(fn)
        job_id = stem if extension in ('.csv', '.json') else None
        if job_id in favorite_ids:
            continue
        path = os.path.join(EXPORT_DIR, fn)
        try:
            if os.path.getmtime(path) < cutoff:
                os.remove(path)
        except Exception:
            pass


def _write_export_csv(job_id: str, columns: list, rows: list, have_building_cols: bool,
                      have_multiple_groups: bool):
    os.makedirs(EXPORT_DIR, exist_ok=True)
    # Keep enrichment columns in every export, even when Snowflake is
    # unavailable. This gives exports a stable schema and makes an enrichment
    # problem visible as blank cells rather than silently dropping columns.
    fieldnames = ['building', 'snapshot', 'building_name', 'org_id', 'org_name', 'snapshot link']
    if have_multiple_groups:
        fieldnames += ['object_type']
    fieldnames += columns

    path = os.path.join(EXPORT_DIR, f'{job_id}.csv')
    tmp  = path + '.tmp'
    with open(tmp, 'w', newline='', encoding='utf-8') as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames, extrasaction='ignore')
        writer.writeheader()
        for r in rows:
            out = {'building': _strip_building_prefix(r['_entity']), 'snapshot': r['_snapshot']}
            out['building_name'] = r.get('_building_name', '')
            out['org_id']        = _csv_cell(r.get('_org_id'))
            out['org_name']      = r.get('_org_name', '')
            out['snapshot link'] = _snapshot_link(r['_entity'], r['_snapshot'], r.get('_org_id'))
            if have_multiple_groups:
                out['object_type'] = r.get('_group', '')
            for c in columns:
                out[c] = _csv_cell(r.get(c))
            writer.writerow(out)
    os.replace(tmp, path)
    return path


def _join_related_rows(left_rows: list, right_rows: list, rel: dict,
                       conditions: list) -> list:
    """Join extracted object rows using SQL outer-join semantics.

    Empty join values never match, consistent with SQL NULL behavior. When a
    key occurs more than once on either side, every matching combination is
    emitted. Right/full joins synthesize an empty left row for an unmatched
    secondary object so its selected fields still appear in the export.
    """
    join_type = rel.get('joinType', 'left')
    rel_index = rel['index']
    by_join = {}
    for index, right_row in enumerate(right_rows):
        join_value = _csv_cell(right_row.get(rel['joinColumn']))
        if join_value:
            by_join.setdefault(join_value, []).append((index, right_row))

    matched_right = set()
    joined = []

    def merge(left_row, right_row):
        merged = dict(left_row)
        for source_col, out_col in rel['outputColumns']:
            merged[out_col] = right_row.get(source_col) if right_row else None
        for group in conditions:
            for condition in group['conditions']:
                if condition['sourceIndex'] == rel_index:
                    merged[condition['mergeColumn']] = (
                        right_row.get(condition['column']) if right_row else None)
        joined.append(merged)

    primary_join_col = rel['primaryJoinColumn']
    for left_row in left_rows:
        join_value = _csv_cell(left_row.get(primary_join_col))
        matches = by_join.get(join_value, []) if join_value else []
        if matches:
            for right_index, right_row in matches:
                matched_right.add(right_index)
                merge(left_row, right_row)
        elif join_type in {'left', 'full'}:
            merge(left_row, None)

    if join_type in {'right', 'full'}:
        for right_index, right_row in enumerate(right_rows):
            if right_index not in matched_right:
                merge({}, right_row)

    return joined


def _run_fields_job(job_id: str, integration: str, file_name: str, raw_field_specs: list,
                    org: str = '', building_filter: str = '', as_of=None,
                    include_students: bool = False, max_results: int | None = None,
                    unique: bool = False, raw_array_expansions: list | None = None,
                    raw_related_files: list | None = None,
                    raw_conditions: list | None = None):
    try:
        _cleanup_old_exports()

        specs = _normalize_field_specs(raw_field_specs)
        if not specs:
            raise RuntimeError('at least one field is required')
        primary_array_requests = _normalize_array_expansion_requests(
            raw_array_expansions or [])
        related_files = _normalize_related_files(raw_related_files or [], integration)
        conditions = _normalize_conditions(raw_conditions or [], integration, related_files)

        for rel in related_files:
            _validate_join_object_scope(
                rel['primaryJoin'], specs,
                f'Primary join field for {rel["filename"]!r}')
            _validate_join_object_scope(
                rel['relatedJoin'], rel['fields'],
                f'Related join field for {rel["filename"]!r}')

        # Join fields are extracted alongside the displayed primary fields,
        # then removed from the output unless the user selected them too.
        primary_join_specs = [r['primaryJoin'] for r in related_files]
        primary_condition_specs = [c['field'] for group in conditions
                                   for c in group['conditions'] if c['sourceIndex'] is None]
        primary_extract_specs = _normalize_field_specs(
            raw_field_specs + primary_join_specs + primary_condition_specs)
        primary_by_key = {(s['name'], s['path']): s for s in primary_extract_specs}
        # Adding a join field can disambiguate an existing same-named output
        # field, so use the columns from the combined normalization everywhere.
        specs = [primary_by_key[(s['name'], s['path'])] for s in specs]
        columns = [s['column'] for s in specs]
        primary_schema = _get_field_schema(integration, file_name) \
            if primary_array_requests else None
        primary_array_expansions = _resolve_array_expansions(
            primary_schema, primary_array_requests) if primary_schema else []
        for expansion in primary_array_expansions:
            columns.extend([
                expansion['countColumn'], expansion['statusColumn'],
                *[field['column'] for field in expansion['fields']],
            ])
        for rel in related_files:
            rel['primaryJoinColumn'] = primary_by_key[
                (rel['primaryJoin']['name'], rel['primaryJoin']['path'])]['column']
        for group in conditions:
            for condition in group['conditions']:
                if condition['sourceIndex'] is None:
                    condition['column'] = primary_by_key[
                        (condition['field']['name'], condition['field']['path'])]['column']

        # Related columns are prefixed with the source filename so a field
        # such as Name from two files cannot collide in the CSV.
        related_extract = []
        related_columns = []
        for rel in related_files:
            rel_index = len(related_extract)
            rel['index'] = rel_index
            prefix = re.sub(r'[^A-Za-z0-9]+', '_', rel['filename']).strip('_') or 'related'
            if rel['integration'] != integration:
                source_prefix = re.sub(r'[^A-Za-z0-9]+', '_', rel['integration']).strip('_')
                prefix = f'{source_prefix}__{prefix}'
            rel_condition_specs = [c['field'] for group in conditions
                                   for c in group['conditions']
                                   if c['sourceIndex'] is not None and
                                   c['sourceIndex'] == rel_index]
            rel_specs = _normalize_field_specs(
                [rel['relatedJoin'], *rel['fields'], *rel_condition_specs])
            rel['extractSpecs'] = rel_specs
            rel['joinColumn'] = next(s['column'] for s in rel_specs
                                     if s['name'] == rel['relatedJoin']['name']
                                     and s['path'] == rel['relatedJoin']['path'])
            rel['outputColumns'] = []
            for spec in rel['fields']:
                source_col = next(s['column'] for s in rel_specs
                                  if s['name'] == spec['name'] and s['path'] == spec['path'])
                out_col = f'{prefix}__{source_col}'
                rel['outputColumns'].append((source_col, out_col))
                related_columns.append(out_col)
            rel_schema = _get_field_schema(rel['integration'], rel['filename']) \
                if rel['arrayExpansionRequests'] else None
            rel['arrayExpansions'] = _resolve_array_expansions(
                rel_schema, rel['arrayExpansionRequests']) if rel_schema else []
            for expansion in rel['arrayExpansions']:
                expansion_columns = [
                    expansion['countColumn'], expansion['statusColumn'],
                    *[field['column'] for field in expansion['fields']],
                ]
                for source_col in expansion_columns:
                    out_col = f'{prefix}__{source_col}'
                    rel['outputColumns'].append((source_col, out_col))
                    related_columns.append(out_col)
            for group in conditions:
                for condition in group['conditions']:
                    if condition['sourceIndex'] == rel_index:
                        condition['column'] = next(s['column'] for s in rel_specs
                                                   if s['name'] == condition['field']['name'] and
                                                   s['path'] == condition['field']['path'])
                        condition['mergeColumn'] = f"_condition_{id(condition)}"
            related_extract.append(rel)
        columns += related_columns

        # Path-scoped fields (picked from the schema dropdown) need the SAME
        # dynamic-parent decisions the dropdown was built from, so a search
        # matches exactly what was shown. Cached — only the first search
        # against a new integration+filename combination pays for the sample.
        dynamic_parents = set()
        if any(s['path'] for s in primary_extract_specs):
            schema = _get_field_schema(integration, file_name)
            dynamic_parents = {_str_to_path(p) for p in schema.get('dynamicParents', [])}

        for rel in related_extract:
            if any(s['path'] for s in rel['extractSpecs']):
                schema = _get_field_schema(rel['integration'], rel['filename'])
                rel['dynamicParents'] = {_str_to_path(p) for p in schema.get('dynamicParents', [])}
            else:
                rel['dynamicParents'] = set()

        data = _index_load(integration)
        if not data:
            raise RuntimeError('No index for this integration')
        entities = data.get('entities', {})
        related_entities = {}
        for rel in related_extract:
            rel_data = _index_load(rel['integration'])
            related_entities[rel['integration']] = (rel_data or {}).get('entities', {})

        if org:
            _job_update(job_id, note='Filtering by organization…')
        allowed, filter_note = _resolve_org_building_filter(
            org, building_filter, exclude_students=not include_students)

        targets = _build_targets(
            entities, integration, file_name, allowed, as_of)
        # A right/full join may have buildings that exist only in the
        # secondary integration/file. Add those buildings without issuing any
        # listing calls: the integration indexes already contain the latest
        # snapshot and filename inventory needed for the default search.
        outer_related = [r for r in related_extract
                         if r['joinType'] in {'right', 'full'}]
        search_buildings = set(entities)
        for rel in outer_related:
            search_buildings.update(related_entities.get(rel['integration'], {}))
        target_by_entity = {target[0]: target for target in targets}
        if outer_related:
            for rel in outer_related:
                for entity, (rel_snapshot, rel_files) in related_entities.get(
                        rel['integration'], {}).items():
                    if entity in target_by_entity or (
                            allowed is not None and entity not in allowed):
                        continue
                    if as_of is None:
                        rel_actual = _file_variant(
                            rel_files, rel['integration'], rel['filename'])
                        if not rel_actual:
                            continue
                        target_by_entity[entity] = (entity, rel_snapshot, None)
                    else:
                        target_by_entity[entity] = (entity, None, None)
            targets = sorted(target_by_entity.values())
        _job_update(job_id, total=len(targets),
                   note=(f'Resolving snapshots as of {as_of.isoformat()}…'
                         if as_of else 'Reading snapshots…'))

        all_rows     = []
        seen_values  = set()   # only populated/consulted when unique=True
        errors       = 0
        no_snapshot  = 0
        lock         = threading.Lock()
        counter      = {'n': 0}
        cap_hit      = {'flag': False}
        row_limit    = max_results or CSV_ROW_CAP
        permit_secondary_only = bool(outer_related)

        def probe(target):
            nonlocal errors, no_snapshot
            if cap_hit['flag']:
                return   # cap already reached — skip the GET entirely, not just the append
            entity, snapshot, key = target

            if as_of is not None:
                entity_prefix = f'{ROOT}{integration}/{entity}/'
                snap_prefix = _snapshot_prefix_before(entity_prefix, as_of)
                if not snap_prefix:
                    key = None
                    snapshot = None
                else:
                    snapshot = snap_prefix[len(entity_prefix):].rstrip('/')
                    actual_file = _file_variant(
                        _snapshot_files(entity_prefix, snapshot), integration, file_name)
                    key = snap_prefix + actual_file if actual_file else None
                if key is None and not permit_secondary_only:
                    with lock:
                        no_snapshot += 1
                        counter['n'] += 1
                    return

            if key:
                try:
                    body = _fetch_text(key)
                    rows = _extract_rows_v2(body, primary_extract_specs, dynamic_parents)
                    _apply_array_expansions(rows, primary_array_expansions)
                except ClientError as e:
                    if e.response.get('Error', {}).get('Code') in ('NoSuchKey', '404'):
                        if not permit_secondary_only:
                            with lock:
                                counter['n'] += 1
                            return
                        rows = []
                    else:
                        with lock:
                            errors += 1
                            counter['n'] += 1
                        return
                except Exception:
                    with lock:
                        errors += 1
                        counter['n'] += 1
                    return
            else:
                rows = []

            # Read related files for the same building. The selected SQL join
            # type determines whether missing/unmatched rows are retained.
            for rel in related_extract:
                rel_entity_data = related_entities.get(rel['integration'], {}).get(entity)
                rel_key = None
                if rel_entity_data:
                    if as_of is not None:
                        rel_prefix = f'{ROOT}{rel["integration"]}/{entity}/'
                        rel_snap_prefix = _snapshot_prefix_before(rel_prefix, as_of)
                        if rel_snap_prefix:
                            rel_snapshot = rel_snap_prefix[len(rel_prefix):].rstrip('/')
                            rel_actual = _file_variant(
                                _snapshot_files(rel_prefix, rel_snapshot),
                                rel['integration'], rel['filename'])
                            if rel_actual:
                                rel_key = rel_snap_prefix + rel_actual
                                if snapshot is None:
                                    snapshot = rel_snapshot
                    else:
                        rel_snapshot = rel_entity_data[0]
                        rel_actual = _file_variant(rel_entity_data[1], rel['integration'], rel['filename'])
                        if rel_actual:
                            rel_key = f'{ROOT}{rel["integration"]}/{entity}/{rel_snapshot}/{rel_actual}'
                            if snapshot is None:
                                snapshot = rel_snapshot
                try:
                    rel_body = _fetch_text(rel_key) if rel_key else None
                    rel_rows = _extract_rows_v2(rel_body, rel['extractSpecs'],
                                                rel['dynamicParents'])
                    _apply_array_expansions(rel_rows, rel['arrayExpansions'])
                except Exception:
                    rel_rows = []
                rows = _join_related_rows(rows, rel_rows, rel, conditions)

            # Conditions are evaluated after all joins so a filter can refer
            # to either the primary row or a matched related row.
            filtered = []
            for row in rows:
                values = {}
                for group in conditions:
                    for condition in group['conditions']:
                        values[id(condition)] = row.get(condition.get('mergeColumn', condition['column']))
                if _conditions_match(conditions, values):
                    filtered.append(row)
            rows = filtered
            with lock:
                counter['n'] += 1
                if rows and not cap_hit['flag']:
                    for r in rows:
                        if unique:
                            # Dedup on the field values alone (not building/
                            # snapshot/group) so this is "distinct value
                            # combinations across everything searched", not
                            # "distinct per file". Rows from a different
                            # object type naturally have a different blank
                            # pattern across `columns`, so they can't collide
                            # with each other by accident.
                            value_key = tuple(_csv_cell(r.get(c)) for c in columns)
                            if value_key in seen_values:
                                continue
                            seen_values.add(value_key)
                        r['_entity']   = entity
                        r['_snapshot'] = snapshot
                        all_rows.append(r)
                        if len(all_rows) >= row_limit:
                            cap_hit['flag'] = True
                            break
                if counter['n'] % 25 == 0:
                    note = f'{len(all_rows)} unique rows found' if unique else f'{len(all_rows)} rows extracted'
                    _job_update(job_id, done=counter['n'], note=note)

        if targets:
            with ThreadPoolExecutor(max_workers=SEARCH_WORKERS) as pool:
                list(pool.map(probe, targets))

        # Building name/org, resolved once for the distinct set of buildings
        # that actually produced rows (not every building searched).
        distinct_entities = sorted({r['_entity'] for r in all_rows})
        meta, cmap, enrich_error = _enrich_with_snowflake(job_id, distinct_entities)
        # The export schema always includes the enrichment columns; this flag
        # controls whether the preview should show them, and is intentionally
        # true even when Snowflake lookup returned no metadata so the UI and
        # downloaded CSV retain the same stable shape.
        have_building_cols = True
        if meta:
            for r in all_rows:
                row = meta.get(r['_entity'])
                if row:
                    r['_building_name'] = row.get(cmap['name']) if cmap['name'] else ''
                    r['_org_id']        = row.get(cmap['org']) if cmap['org'] else ''
                    org_name_col = cmap.get('org_name')
                    r['_org_name']      = (row.get(org_name_col) if org_name_col else '') \
                                          or row.get('ORGANIZATION_NAME') or ''

        have_multiple_groups = len({r.get('_group') for r in all_rows}) > 1

        _job_update(job_id, note='Writing CSV…')
        _write_export_csv(job_id, columns, all_rows, have_building_cols, have_multiple_groups)

        preview = [
            {
                'entity':       _strip_building_prefix(r['_entity']),
                'snapshot':     r['_snapshot'],
                'buildingName': r.get('_building_name') if have_building_cols else None,
                'orgId':        _csv_cell(r.get('_org_id')) if have_building_cols else None,
                'orgName':      r.get('_org_name') if have_building_cols else None,
                'snapshotLink': _snapshot_link(r['_entity'], r['_snapshot'], r.get('_org_id')),
                'objectType':   r.get('_group', '') if have_multiple_groups else None,
                **{c: _csv_cell(r.get(c)) for c in columns},
            }
            for r in all_rows[:FIELDS_PREVIEW]
        ]

        _job_update(job_id, done=counter['n'], status='done', finished=time.time(),
                    result={
                        'integration':  integration,
                        'fileName':     file_name,
                        'fields':       columns,
                        'org':          org,
                        'includeStudents': include_students,
                        'resultLimit':  max_results,
                        'unique':       unique,
                        'asOf':         as_of.isoformat() if as_of else None,
                        'searched':     counter['n'],
                        'buildings':    len(search_buildings),
                        'noSnapshot':   no_snapshot,
                        'rowCount':     len(all_rows),
                        'buildingColumns': have_building_cols,
                        'csvFields':     ['building', 'snapshot', 'building_name', 'org_id',
                                          'org_name', 'snapshot link'] +
                                         (['object_type'] if have_multiple_groups else []) + columns,
                        'preview':      preview,
                        'truncated':    cap_hit['flag'],
                        'errors':       errors,
                        'filterNote':   filter_note,
                        'enrichError':  enrich_error,
                        'enrichCredentialIssue': snowflake_db.credential_error(enrich_error),
                        'downloadUrl':  f'/api/search/csv/{job_id}',
                    })
        _history_record(job_id, 'fields', _job_get(job_id)['result'], {
            'fileName': file_name,
            'org': org,
            'buildings': building_filter,
            'includeStudents': include_students,
            'resultLimit': max_results,
            'asOf': as_of.isoformat() if as_of else None,
            'unique': unique,
            'fields': columns,
            'relatedFiles': [
                {'integration': rel['integration'], 'filename': rel['filename'],
                 'joinType': rel['joinType'],
                 'primaryJoin': {
                     'name': rel['primaryJoin']['name'],
                     'path': rel['primaryJoin']['path'],
                 },
                 'relatedJoin': {
                     'name': rel['relatedJoin']['name'],
                     'path': rel['relatedJoin']['path'],
                 },
                 'arrayExpansions': rel.get('arrayExpansionRequests', [])}
                for rel in related_files
            ],
            'arrayExpansions': primary_array_requests,
            'conditionCount': sum(len(group.get('conditions', [])) for group in conditions),
        })
    except Exception as e:
        _job_update(job_id, status='error', error=str(e), finished=time.time())


# ── Availability Agent ───────────────────────────────────────────────────────

def _availability_rules():
    global _availability_rules_cache, _availability_rules_cache_mtime
    mtime = os.stat(AVAILABILITY_RULES_PATH).st_mtime_ns
    if (_availability_rules_cache is None or
            _availability_rules_cache_mtime != mtime):
        with open(AVAILABILITY_RULES_PATH, 'r', encoding='utf-8') as fh:
            _availability_rules_cache = json.load(fh)
        _availability_rules_cache_mtime = mtime
    return _availability_rules_cache


def _availability_file_variant(files, integration: str, configured: str):
    """Resolve a logical rules-file name to an actual snapshot filename."""
    exact = _file_variant(files, integration, configured)
    if exact:
        return exact
    for actual in sorted(files):
        if actual == configured or actual.startswith(configured + '_') or actual.startswith(configured + '.'):
            return actual
    return None


def _availability_first_file(files, integration: str, candidates: list):
    for candidate in candidates:
        actual = _availability_file_variant(files, integration, candidate)
        if actual:
            return actual
    return None


def _availability_matching_files(files, integration: str, candidates: list):
    """Return every physical file matching configured logical candidates."""
    matches = []
    for actual in sorted(files or []):
        if any(actual == candidate or actual.startswith(candidate + '_') or
               actual.startswith(candidate + '.')
               for candidate in (candidates or [])):
            matches.append(actual)
    return matches


def _availability_primary_files(files, integration: str, candidates: list) -> list:
    """Every physical file for the first primary/actual candidate name that
    has any match in this snapshot -- preferring an earlier candidate (e.g.
    Voyager's AvailableUnits_Login over its AllUnits_Login fallback) but
    taking every property-code variant of that chosen candidate, not just
    one.

    A single MITS building can be backed by more than one property on the
    PMS side (RealPage's getunitlist_<site>.xml.gz, Voyager's
    AvailableUnits_Login_<property>.xml.gz) -- each its own physical file.
    Taking only the first (_availability_first_file) silently dropped every
    unit belonging to the other properties.
    """
    for candidate in candidates or []:
        matches = _availability_matching_files(files, integration, [candidate])
        if matches:
            return matches
    return []


def _availability_source_lookup(source_by_key: dict, source: dict,
                                primary_row: dict, primary_key: list) -> dict:
    """Look up a `sources` entry's enrichment row for `primary_row`.

    Keyed by (file property code, join-key value) so a multi-property-code
    source (RealPage's getallunits split by site, Voyager's AllUnits_Login
    split by property) never crosses property boundaries -- the same local
    UnitNumber/@IDValue can exist independently in more than one property
    backing a single building. Integrations with no property-code concept
    key everything under a None code, which is the pre-existing behavior.
    """
    keyed = source_by_key.get(source['file']) or {}
    code = primary_row.get('__file_property_code')
    source_keys = _availability_keys(
        primary_row, source.get('primary_key') or primary_key)
    related = next((keyed[(code, k)] for k in source_keys
                    if (code, k) in keyed), None)
    if related is None:
        related = keyed.get((code, '__all__'))
    return related or {}


def _availability_value(row: dict, field: str):
    """Read a field from a row, including nested JSON stored as a string.

    Several integration files expose building-level settings inside a JSON
    object field. RentCafe's property_details.apartmentSettings is the key
    example: monthsAvailabilityRestrictedTo is not a top-level property.
    """
    wanted = str(field).casefold()
    seen = set()

    def find(value):
        marker = id(value)
        if marker in seen:
            return None
        seen.add(marker)
        if isinstance(value, dict):
            for key, nested in value.items():
                # Extracted rows deliberately include None placeholders for
                # requested fields that are absent at that object level. Do
                # not let such a placeholder mask the real value inside a
                # nested settings object (for example RentCafe's
                # apartmentSettings.monthsAvailabilityRestrictedTo).
                if str(key).casefold() == wanted and nested is not None:
                    return nested
            for nested in value.values():
                found = find(nested)
                if found is not None:
                    return found
        elif isinstance(value, (list, tuple)):
            for nested in value:
                found = find(nested)
                if found is not None:
                    return found
        elif isinstance(value, str):
            text = value.strip()
            if text.startswith(('{', '[')):
                try:
                    return find(json.loads(text))
                except (TypeError, ValueError, json.JSONDecodeError):
                    pass
        return None

    return find(row)


def _availability_key(row: dict, candidates: list):
    for field in candidates:
        value = _availability_value(row, field)
        if value is not None and str(value).strip():
            return str(value).strip().casefold()
    return None


def _availability_voyager_units(body: str, fields: list) -> list:
    """Extract one coherent row per MITS ILS_Unit XML element."""
    try:
        root = ET.fromstring(body)
    except (ET.ParseError, TypeError, ValueError):
        return []
    rows = []
    wanted = {str(field): str(field).lstrip('@') for field in fields}
    for unit in root.iter():
        if unit.tag.rsplit('}', 1)[-1] != 'ILS_Unit':
            continue
        row = {'_group': 'ILS_Unit'}
        for field, local in wanted.items():
            if field.startswith('@'):
                value = next((value for key, value in unit.attrib.items()
                              if key.rsplit('}', 1)[-1] == local), None)
                if value is None:
                    # Unit identity is not represented consistently across
                    # Voyager feeds. IDValue may be on ILS_Unit while IDType
                    # is commonly on its nested Identification element.
                    value = next((value
                                  for descendant in unit.iter()
                                  if descendant is not unit
                                  for key, value in descendant.attrib.items()
                                  if key.rsplit('}', 1)[-1] == local), None)
            else:
                value = None
                for descendant in unit.iter():
                    if descendant is unit or descendant.tag.rsplit('}', 1)[-1] != local:
                        continue
                    value = (descendant.text or '').strip() or None
                    if value is None:
                        if (local == 'MadeReadyDate' and
                                all(descendant.attrib.get(part) for part in
                                    ('Year', 'Month', 'Day'))):
                            date_parts = {
                                part: str(descendant.attrib[part]).strip()
                                for part in ('Year', 'Month', 'Day')
                            }
                            if all(value == '0' for value in date_parts.values()):
                                # Voyager emits 0/0/0 for a made-ready date
                                # that is deliberately unset. Keep the normal
                                # date value empty, but retain this distinction
                                # so availability rules can exclude the unit.
                                row['__made_ready_date_all_zero'] = True
                            try:
                                value = datetime(
                                    int(date_parts['Year']),
                                    int(date_parts['Month']),
                                    int(date_parts['Day']),
                                ).date().isoformat()
                            except (TypeError, ValueError):
                                value = None
                    if value is None:
                        # MITS values such as EffectiveRent are represented as
                        # attributes; Min is the unit-level effective value.
                        value = (descendant.attrib.get('Min') or
                                 descendant.attrib.get('Value') or
                                 descendant.attrib.get('Max'))
                    if value is not None:
                        break
            row[field] = value
        rows.append(row)
    return rows


def _availability_realpage_units(body: str, fields: list) -> list:
    """Extract one coherent row per RealPage ``UnitObject`` XML element.

    RealPage nests identity fields under ``Address`` and availability fields
    under ``Availability``. The generic unscoped XML extractor treats those
    nested objects as separate rows, which prevents PropertyNumberID + UnitID
    from forming the canonical key used to join against unit-details.
    """
    try:
        root = ET.fromstring(body)
    except (ET.ParseError, TypeError, ValueError):
        return []
    # LRO (Lease Rent Optimization) pricing is exposed as a whole <RentMatrix>
    # element per unit, never a scalar the generic text-extraction below can
    # read. Its mere presence anywhere in this property's raw feed means the
    # property runs LRO; a unit within it that lacks its own <RentMatrix> is
    # missing pricing the PMS itself expected it to have.
    building_has_lro = bool(root.findall('.//RentMatrix'))
    rows = []
    wanted = {str(field): str(field).lstrip('@') for field in fields}
    for unit in root.iter():
        if unit.tag.rsplit('}', 1)[-1] != 'UnitObject':
            continue
        row = {'_group': 'UnitObject', '__building_has_lro': building_has_lro}
        for field, local in wanted.items():
            if field.startswith('@'):
                value = next((value for key, value in unit.attrib.items()
                              if key.rsplit('}', 1)[-1] == local), None)
            else:
                value = None
                found = False
                for descendant in unit.iter():
                    if (descendant is unit or
                            descendant.tag.rsplit('}', 1)[-1] != local):
                        continue
                    found = True
                    value = (descendant.text or '').strip() or None
                    if value is None:
                        value = (descendant.attrib.get('Value') or
                                 descendant.attrib.get('Min') or
                                 descendant.attrib.get('Max'))
                    if value is not None:
                        break
                if value is None and found:
                    # A structural element with no scalar text/Value/Min/Max
                    # (RentMatrix's content is a nested Rows/Row tree) still
                    # carries meaning by existing at all -- record presence
                    # so rules can test it with truthy/missing like any
                    # other field, rather than reading as absent.
                    value = 'true'
            row[field] = value
        rows.append(row)
    return rows


def _availability_extract(body: str, fields: list, voyager_units: bool = False,
                          realpage_units: bool = False):
    if voyager_units:
        return _availability_voyager_units(body, fields)
    if realpage_units:
        return _availability_realpage_units(body, fields)
    specs = _normalize_field_specs([{'name': field} for field in fields])
    return _extract_rows_v2(body, specs, set()) if specs else []


def _availability_date(value):
    if not value:
        return None
    raw = str(value).strip()
    for candidate in (raw, raw.replace('Z', '+00:00')):
        try:
            dt = datetime.fromisoformat(candidate)
            return dt.date()
        except ValueError:
            pass
    for fmt in ('%m/%d/%Y', '%Y-%m-%d', '%Y-%m-%dT%H:%M:%S'):
        try:
            return datetime.strptime(raw, fmt).date()
        except ValueError:
            pass
    return None


def _availability_snapshot_datetime(snapshot):
    """Parse an indexed snapshot name into an aware UTC datetime."""
    raw = str(snapshot or '')
    if raw.startswith('snapshot-'):
        raw = raw[len('snapshot-'):]
    if not raw:
        return None
    try:
        parsed = datetime.fromisoformat(raw.replace('Z', '+00:00'))
    except ValueError:
        return None
    return parsed.replace(tzinfo=timezone.utc) if parsed.tzinfo is None else parsed.astimezone(timezone.utc)


def _availability_leading_number(text) -> float:
    """Parse the leading numeric token of a raw PMS value, tolerating a
    trailing unit label the API appends to an otherwise-numeric field --
    e.g. Entrata's Area: "1663.0000 SquareFeet". Raises ValueError/TypeError
    the same as float() when there is no leading number at all, so callers
    that already catch those need no other change."""
    match = re.match(r'\s*[+-]?\d+(?:\.\d+)?', str(text))
    if not match:
        raise ValueError(f'no leading number in {text!r}')
    return float(match.group())


def _availability_when(values: dict, clause: dict):
    if 'any' in clause:
        return any(_availability_when(values, child) for child in (clause.get('any') or []))
    if 'all' in clause:
        return all(_availability_when(values, child) for child in (clause.get('all') or []))
    if 'not' in clause:
        return not _availability_when(values, clause.get('not') or {})
    actual = _availability_value(values, clause.get('field'))
    op = clause.get('op')
    expected = clause.get('value', '')
    text = _csv_cell(actual).strip()
    # Availability rules describe the state represented by a snapshot. Use
    # that snapshot's UTC calendar date so historical/as-of results do not
    # change when the same file is evaluated on a later day. Fall back to the
    # current UTC date for callers that do not provide snapshot context.
    reference_date = _availability_date(values.get('__current_date'))
    reference_date = reference_date or datetime.now(timezone.utc).date()
    if op == 'missing':
        return actual is None or text == ''
    if op == 'nonempty':
        return actual is not None and text != ''
    if op == 'truthy':
        return bool(actual) and text.casefold() not in ('false', '0', 'none', 'null', 'no')
    if op == 'falsey':
        return not actual or text.casefold() in ('false', '0', 'none', 'null', 'no')
    if op == 'falsey_present':
        return actual is not None and text.casefold() in ('', 'false', '0', 'none', 'null', 'no')
    if op == 'invalid_rent':
        try:
            return not (100 < _availability_leading_number(actual) < 50000)
        except (TypeError, ValueError):
            return True
    if op == 'invalid_sqft':
        # A missing/falsy square-footage value, including numeric or textual
        # zero, is valid for availability purposes and must not trigger the
        # invalid-square-footage override. Nonzero malformed or out-of-range
        # values remain invalid.
        if not actual or text.casefold() in ('false', '0', 'none', 'null', 'no'):
            return False
        try:
            # Some raw feeds append a unit label to an otherwise-numeric
            # value (Entrata's Area: "1663.0000 SquareFeet"); read the
            # leading number rather than treating the whole field as
            # malformed.
            numeric = _availability_leading_number(actual)
            if numeric == 0:
                return False
            return not (0 < numeric < 10000)
        except (TypeError, ValueError):
            return True
    if op == 'stage_in':
        allowed = {str(item).strip() for item in (expected if isinstance(expected, list)
                                                   else str(expected).split(','))}
        return str(values.get('__direct_stage', '')).strip() in allowed
    if op == 'source_present':
        return bool(values.get(f'__source_present__{expected}'))
    if op == 'future_days':
        date = _availability_date(actual)
        try:
            days = float(expected)
        except (TypeError, ValueError):
            return False
        return bool(date and date > reference_date + timedelta(days=days))
    if op == 'future_or_equal_days':
        date = _availability_date(actual)
        try:
            days = float(expected)
        except (TypeError, ValueError):
            return False
        return bool(date and date >= reference_date + timedelta(days=days))
    if op == 'future_by_field_days':
        date = _availability_date(actual)
        try:
            days = float(_availability_value(values, clause.get('days_field')) or 0)
            days *= float(clause.get('multiplier', 1))
        except (TypeError, ValueError):
            return False
        return bool(date and days > 0 and
                    date > reference_date + timedelta(days=days))
    if op == 'future':
        date = _availability_date(actual)
        return bool(date and date > reference_date)
    if op in ('equals', 'not_equals', 'contains', 'not_contains'):
        return _condition_value_matches(actual, {'equals': 'eq', 'not_equals': 'ne',
                                                  'contains': 'contains', 'not_contains': 'not_contains'}[op],
                                         str(expected))
    return False


def _availability_direct_prediction(rule: dict, values: dict):
    direct = rule.get('direct') or {}
    field = direct.get('field')
    actual = _availability_value(values, field) if field else None
    if actual is not None:
        key = str(actual).casefold() if direct.get('casefold') else str(actual)
        mapping = direct.get('map') or {}
        if direct.get('casefold'):
            mapping = {str(k).casefold(): v for k, v in mapping.items()}
        if key in mapping:
            return int(mapping[key]), f'Status: {actual}'
    for candidate in rule.get('direct_rules') or []:
        clauses = candidate.get('when') or []
        if clauses and all(_availability_when(values, clause) for clause in clauses):
            return int(candidate['stage']), candidate.get('reason') or f'Status: {actual}'
    return None, None


def _availability_predict(rule: dict, values: dict):
    predicted, reason = _availability_direct_prediction(rule, values)
    direct_predicted = predicted
    override_reason = None
    for override in rule.get('overrides') or []:
        # Overrides are exclusion rules: they may only remove a unit from
        # availability by mapping it to Lease Signed (stage 9). Renovating and
        # other non-9 outcomes belong in the explicit direct rules instead.
        try:
            override_stage = int(override['stage'])
        except (KeyError, TypeError, ValueError):
            continue
        if override_stage != 9:
            continue
        clauses = override.get('when') or []
        if clauses and all(_availability_when(values, clause) for clause in clauses):
            predicted = override_stage
            override_reason = override.get('reason') or f"Override: {predicted}"
            # Rules may explicitly prefer an override's more specific reason
            # even when the direct status already maps to the same stage.
            if override.get('replace_reason') or direct_predicted != predicted:
                reason = override_reason
    if predicted is None:
        fallback = rule.get('fallback') or {}
        if 'stage' in fallback:
            predicted = int(fallback['stage'])
            reason = fallback.get('reason') or f'Fallback: {predicted}'
    if predicted is None:
        return None, None
    return predicted, reason or override_reason


def _availability_source_rows(body: str, fields: list, key_candidates: list):
    rows = _availability_extract(body, fields)
    keyed = {}
    for row in rows:
        key = _availability_key(row, key_candidates)
        if key:
            keyed.setdefault(key, row)
    return rows, keyed


def _availability_keys(row: dict, candidates: list):
    """Return every usable candidate key, not just the first populated field.

    Snapshot schemas frequently carry both an opaque PMS id and a human unit
    number. Matching all populated candidates lets unit_details line up on the
    latter while joins such as AppFolio listing.json still use the former.
    """
    keys = []
    for field in candidates or []:
        value = _availability_value(row, field)
        if value is not None and str(value).strip():
            key = str(value).strip().casefold()
            if key not in keys:
                keys.append(key)
    return keys


def _availability_unit_key(row: dict, rule: dict,
                           phase_prefix_values: set | None = None):
    """Derive the integration's persisted building_unique_id from its rule."""
    config = rule.get('unit_key') or {}
    parts = []
    phase_fields = config.get('phase_prefix_when_multiple') or []
    if phase_fields and len(phase_prefix_values or ()) > 1:
        phase_value = next((_availability_value(row, field)
                            for field in phase_fields
                            if _availability_value(row, field) is not None and
                            str(_availability_value(row, field)).strip()), None)
        if phase_value is None:
            return None
        parts.append(str(phase_value).strip())
    for candidates in config.get('components') or []:
        value = next((_availability_value(row, field)
                      for field in candidates
                      if _availability_value(row, field) is not None and
                      str(_availability_value(row, field)).strip()), None)
        if value is None:
            return None
        parts.append(str(value).strip())
    return '-'.join(parts).casefold() if parts else None


def _availability_wait_unit(row: dict, rule: dict) -> bool:
    """True if `row`'s raw PMS identity field (unit_name_fields) reads as a
    wait-list/tour-scheduling placeholder. Always evaluated against a raw
    primary-feed row -- never against unit_details, which has no
    unit_name_fields concept and must not drive this determination."""
    for field in rule.get('unit_name_fields') or []:
        value = _availability_value(row, field)
        if value is not None and 'wait' in str(value).casefold():
            return True
    return False


def _availability_file_property_code(filename: str, candidates: list):
    """Extract a property-code suffix such as AllUnits_Login_utbanhil.xml.gz."""
    for candidate in candidates or []:
        if filename.startswith(candidate + '_'):
            suffix = filename[len(candidate) + 1:]
            # A period can be part of the external property id (for example
            # 4600.02). Remove only recognized file extensions rather than
            # truncating at the first punctuation character.
            for extension in ('.xml.gz', '.json.gz', '.xml', '.json', '.gz'):
                if suffix.casefold().endswith(extension):
                    suffix = suffix[:-len(extension)]
                    break
            return suffix.strip() or None
    return None


def _availability_promote_missing_source_units(primary_rows: list,
                                                source_rows: list,
                                                rules: dict) -> list:
    """Add rows from a `sources` entry declared `add_missing_as_units` whose
    identity (the rules' own unit_key) has no counterpart already in
    `primary_rows`, flagged __supplemental_unit so they classify the same way
    RentCafe/Voyager classify a cross-integration all-units supplement (e.g.
    as lease-signed).

    This is the same-integration variant of that pattern: the supplemental
    data already lives in a declared `sources` file within this same
    snapshot -- e.g. RealPage's getallunits alongside getunitlist, both
    carrying the same raw UnitID -- so no cross-integration/cross-snapshot
    resolution is needed, unlike supplemental_units.
    """
    existing_keys = {_availability_unit_key(row, rules) for row in primary_rows}
    existing_keys.discard(None)
    added = []
    for row in source_rows:
        key = _availability_unit_key(row, rules)
        if key is None or key in existing_keys:
            continue
        new_row = dict(row)
        new_row['__supplemental_unit'] = True
        added.append(new_row)
        existing_keys.add(key)
    return added


def _availability_supplemental_rows(body: str, config: dict,
                                    primary_rows: list,
                                    property_code: str | None = None) -> list:
    """Return source units whose external ids are absent from the primary feed.

    RentCafe is the first consumer: Voyager Unit Identification/@IDType is the
    same identifier exposed as RentCafe voyagerApartmentId, while @IDValue is
    the human unit name used to join unit_details.
    """
    primary_id_field = config.get('primary_id_field')
    supplemental_id_field = config.get('supplemental_id_field')
    supplemental_name_field = config.get('supplemental_name_field')
    if not all((primary_id_field, supplemental_id_field,
                supplemental_name_field)):
        return []

    output_name_field = config.get('output_name_field') or 'unit_number'
    output_property_field = config.get('output_property_field')
    existing_ids = set()
    existing_id_values = set()
    existing_names = set()
    existing_name_values = set()
    for row in primary_rows:
        row_code = (_availability_value(row, output_property_field)
                    if output_property_field else None)
        normalized_code = str(row_code or '').strip().casefold()
        source_id = _availability_value(row, primary_id_field)
        if source_id is not None and str(source_id).strip():
            normalized_id = str(source_id).strip().casefold()
            existing_ids.add((normalized_code, normalized_id))
            existing_id_values.add(normalized_id)
        value = _availability_value(row, output_name_field)
        if value is not None and str(value).strip():
            normalized_name = str(value).strip().casefold()
            existing_names.add((normalized_code, normalized_name))
            existing_name_values.add(normalized_name)
    seen_ids = set(existing_ids)
    seen_id_values = set(existing_id_values)
    seen_names = set(existing_names)
    seen_name_values = set(existing_name_values)
    output = []
    row_type_field = config.get('row_type_field')
    row_type_value = str(config.get('row_type_value') or '').strip().casefold()
    for source_row in _availability_extract(
            body, config.get('fields') or [], voyager_units=True):
        if row_type_field:
            actual_type = _availability_value(source_row, row_type_field)
            # A coherent ILS_Unit row is already scoped to a physical unit.
            # Older feeds expose OrganizationName="Unit"; newer feeds omit it.
            if (source_row.get('_group') != 'ILS_Unit' and
                    str(actual_type or '').strip().casefold() != row_type_value):
                continue
        source_id = _availability_value(source_row, supplemental_id_field)
        source_name = _availability_value(source_row, supplemental_name_field)
        normalized_id = str(source_id or '').strip().casefold()
        normalized_name = str(source_name or '').strip().casefold()
        normalized_code = str(property_code or '').strip().casefold()
        # Some RentCafe rows omit voyagerApartmentId even though the unit is
        # present. The external property id plus IDValue/name is the safe
        # fallback that prevents the same physical unit from being re-added as
        # a duplicate supplemental Voyager unit.
        id_seen = ((normalized_code, normalized_id) in seen_ids
                   if normalized_code else normalized_id in seen_id_values)
        name_seen = ((normalized_code, normalized_name) in seen_names
                     if normalized_code else normalized_name in seen_name_values)
        if not normalized_id or id_seen or not normalized_name or name_seen:
            continue
        seen_ids.add((normalized_code, normalized_id))
        seen_id_values.add(normalized_id)
        seen_names.add((normalized_code, normalized_name))
        seen_name_values.add(normalized_name)
        supplemental_row = dict(source_row)
        supplemental_row.update({
            output_name_field: source_name,
            primary_id_field: source_id,
            '__supplemental_unit': True,
        })
        output_status_field = config.get('output_status_field')
        if output_status_field:
            supplemental_row[output_status_field] = config.get(
                'output_status_value')
        if output_property_field and property_code:
            supplemental_row[output_property_field] = property_code
        output.append(supplemental_row)
    return output


def _availability_supplemental_targets(entity: str, primary_snapshot: str,
                                       as_of, config: dict,
                                       indexed_entities: dict):
    """Resolve all supplemental files, preferring an existing on-disk index."""
    integrations = config.get('integrations') or []
    files = config.get('files') or []
    if as_of is None:
        for related_integration in integrations:
            entity_data = indexed_entities.get(related_integration, {}).get(entity)
            if not entity_data:
                continue
            snapshot, snapshot_files = entity_data
            actuals = _availability_matching_files(
                snapshot_files, related_integration, files)
            if actuals:
                return [(related_integration, snapshot, actual)
                        for actual in actuals]

    primary_reference = _availability_snapshot_datetime(primary_snapshot)
    cutoff = as_of or primary_reference
    for related_integration in integrations:
        entity_prefix = f'{ROOT}{related_integration}/{entity}/'
        if as_of is None and primary_reference is not None:
            try:
                nearest_minutes = int(config.get(
                    'nearest_snapshot_minutes', 15))
            except (TypeError, ValueError):
                nearest_minutes = 15
            snapshot_prefix = _snapshot_prefix_nearest(
                entity_prefix, primary_reference,
                max_skew_minutes=max(0, nearest_minutes))
            if snapshot_prefix:
                snapshot = snapshot_prefix[len(entity_prefix):].rstrip('/')
            elif config.get('use_latest_historical_snapshot'):
                snapshot = _latest_snapshot_seeked(
                    entity_prefix, _cutoff_stamps(), full_fallback=True)
                if not snapshot:
                    continue
            else:
                continue
        elif cutoff is not None:
            snapshot_prefix = _snapshot_prefix_before(entity_prefix, cutoff)
            if not snapshot_prefix:
                continue
            snapshot = snapshot_prefix[len(entity_prefix):].rstrip('/')
        else:
            snapshot = _latest_snapshot_seeked(
                entity_prefix, _cutoff_stamps(), full_fallback=True)
            if not snapshot:
                continue
        snapshot_files = _snapshot_files(entity_prefix, snapshot)
        actuals = _availability_matching_files(
            snapshot_files, related_integration, files)
        if actuals:
            return [(related_integration, snapshot, actual)
                    for actual in actuals]
    return []


def _write_availability_csv(job_id: str, rows: list, fieldnames: list):
    os.makedirs(EXPORT_DIR, exist_ok=True)
    path = os.path.join(EXPORT_DIR, f'{job_id}.csv')
    tmp = path + '.tmp'
    with open(tmp, 'w', newline='', encoding='utf-8') as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames, extrasaction='ignore')
        writer.writeheader()
        for row in rows:
            writer.writerow({field: _csv_cell(row.get(field)) for field in fieldnames})
    os.replace(tmp, path)


def _run_availability_job(job_id: str, integration: str, org: str = '',
                          building_filter: str = '', as_of=None,
                          show_unknown: bool = False,
                          include_students: bool = True,
                          include_applications: bool = True,
                          include_not_launched_on_leasing: bool = True,
                          max_results: int | None = None,
                          record_history: bool = True,
                          stop_job_id: str | None = None):
    try:
        control_job_id = stop_job_id or job_id
        _job_update(job_id, note=f'Loading {integration} index…')
        rules = _availability_rules().get('integrations', {}).get(integration)
        if not rules:
            raise RuntimeError(f'Availability Agent does not support {integration}')
        data = _index_load(integration)
        if not data:
            raise RuntimeError(f'No index for {integration}; build its index first')
        source_integration = _availability_source_integration(integration)
        entities = data.get('entities', {})
        filter_bits = []
        if org:
            filter_bits.append('organization')
        if building_filter:
            filter_bits.append('building')
        if not include_students:
            filter_bits.append('student-community exclusion')
        if not include_applications:
            filter_bits.append('Applications exclusion')
        if not include_not_launched_on_leasing:
            filter_bits.append('not-launched-on-Leasing exclusion')
        _job_update(
            job_id,
            note=('Applying ' + ', '.join(filter_bits) + ' filters…'
                  if filter_bits else 'Preparing building scope…'))
        allowed, filter_note = _resolve_org_building_filter(
            org, building_filter,
            exclude_students=not include_students,
            exclude_applications=not include_applications,
            require_launched_on_leasing=not include_not_launched_on_leasing)
        primary_candidates = rules.get('primary') or []
        actual_candidates = rules.get('actual') or []
        supplemental_config = rules.get('supplemental_units') or {}
        supplemental_indexes = {}
        for related_integration in supplemental_config.get('integrations') or []:
            related_data = _index_load(related_integration)
            supplemental_indexes[related_integration] = (
                (related_data or {}).get('entities', {})
                if isinstance(related_data, dict) else {})
        limit_note = f' for a {max_results:,}-unit limit' if max_results else ''
        _job_update(job_id, note=f'Selecting indexed buildings{limit_note}…')
        targets = []
        # The index builder owns the 24-hour building eligibility rule. A
        # latest-index run must consume every stored entry without applying a
        # second rolling age cutoff as wall-clock time advances.
        for entity, (snapshot, files) in entities.items():
            if allowed is not None and entity not in allowed:
                continue
            primary_files = _availability_primary_files(
                files, source_integration, primary_candidates)
            unit_details_actual = _availability_first_file(
                files, source_integration, actual_candidates)
            if unit_details_actual:
                targets.append((entity, snapshot, primary_files, files))
            elif as_of is not None:
                targets.append((entity, None, [], []))
        targets.sort()
        _job_update(job_id, total=len(targets),
                    note=f'Selected {len(targets):,} candidate buildings…')

        rollout_configs = rules.get('rollouts') or {}
        rollout_names = list(rollout_configs)
        building_fields = rules.get('building_fields') or []
        rollout_values = {}
        rollout_error = None
        metadata_checked = False
        meta = None
        cmap = None
        enrich_error = None
        if ((rollout_names or building_fields) and targets and
                not _job_stop_requested(control_job_id)):
            target_times = {
                entity: (as_of or _availability_snapshot_datetime(snapshot)
                         or datetime.now(timezone.utc))
                for entity, snapshot, _actual, _files in targets
            }
            # Organization-level rollout rules need the building -> org
            # mapping before unit evaluation. Reuse this metadata for the
            # final CSV enrichment below instead of querying Snowflake twice.
            meta, cmap, enrich_error = _enrich_with_snowflake(
                job_id, list(target_times))
            metadata_checked = True
            if rollout_names:
                org_ids = {}
                if enrich_error:
                    rollout_error = f'organization lookup unavailable: {enrich_error}'
                elif meta and cmap and cmap.get('org'):
                    org_ids = {
                        entity: detail.get(cmap['org'])
                        for entity, detail in meta.items()
                    }
                try:
                    rollout_values = snowflake_db.rollout_variants(
                        list(target_times), rollout_names, target_times, org_ids)
                except Exception as e:
                    # Keep the run usable, but mark rollout state unknown so a
                    # rollout-dependent override is not applied speculatively.
                    rollout_error = str(e) if not rollout_error else f'{rollout_error}; {e}'

        source_fields = {'primary': list(dict.fromkeys((rules.get('fields') or []) +
                                                        (rules.get('primary_key') or [])))}
        source_configs = rules.get('sources') or []
        for source in source_configs:
            source_fields[source['file']] = list(dict.fromkeys(source.get('fields') or []))
        actual_fields = list(dict.fromkeys((rules.get('actual_fields') or ['availability_stage', 'availabilityStage']) +
                                           (rules.get('actual_key') or [])))
        primary_key = rules.get('primary_key') or []
        actual_key = rules.get('actual_key') or []
        all_rows = []
        errors = 0
        supplemental_errors = 0
        supplemental_units = 0
        wait_filtered = 0
        no_snapshot = 0
        counter = {'n': 0}
        cap_hit = {'flag': False}
        lock = threading.Lock()

        def probe(target):
            nonlocal errors, no_snapshot, supplemental_errors, supplemental_units, wait_filtered
            if cap_hit['flag'] or _job_stop_requested(control_job_id):
                return
            entity, snapshot, primary_files, snapshot_files = target
            entity_prefix = f'{ROOT}{source_integration}/{entity}/'
            if as_of is not None:
                snap_prefix = _snapshot_prefix_before(entity_prefix, as_of)
                if not snap_prefix:
                    with lock:
                        no_snapshot += 1
                        counter['n'] += 1
                    return
                snapshot = snap_prefix[len(entity_prefix):].rstrip('/')
                snapshot_files = _snapshot_files(entity_prefix, snapshot)
                primary_files = _availability_primary_files(
                    snapshot_files, source_integration, primary_candidates)
            actual_actual = _availability_first_file(
                snapshot_files, source_integration, actual_candidates)
            if not actual_actual:
                with lock:
                    counter['n'] += 1
                return
            try:
                actual_body = _fetch_text(
                    f'{ROOT}{source_integration}/{entity}/{snapshot}/{actual_actual}')
                actual_rows = _availability_extract(actual_body, actual_fields)
            except Exception:
                with lock:
                    errors += 1
                    counter['n'] += 1
                return

            primary_rows = []
            source_rows = {source['file']: [] for source in source_configs}
            raw_errors = 0
            # A single MITS building can be backed by more than one PMS
            # property (RealPage's getunitlist_<site>, Voyager's
            # AvailableUnits_Login_<property>) -- read every variant, each
            # tagged with its own property code so identities never collide.
            for primary_actual in primary_files:
                try:
                    primary_body = _fetch_text(
                        f'{ROOT}{source_integration}/{entity}/{snapshot}/{primary_actual}')
                    rows = _availability_extract(
                        primary_body, source_fields['primary'],
                        voyager_units=integration == 'Voyager',
                        realpage_units=integration == 'RealPage')
                    file_property_code = _availability_file_property_code(
                        primary_actual, primary_candidates)
                    if file_property_code:
                        for row in rows:
                            row['__file_property_code'] = file_property_code
                    primary_rows.extend(rows)
                except Exception:
                    raw_errors += 1
            for source in source_configs:
                actual_sources = _availability_matching_files(
                    snapshot_files, source_integration, [source['file']])
                for actual_source in actual_sources:
                    try:
                        source_body = _fetch_text(
                            f'{ROOT}{source_integration}/{entity}/{snapshot}/{actual_source}')
                        rows = _availability_extract(
                            source_body, source_fields[source['file']],
                            voyager_units=(integration == 'Voyager' and
                                           source['file'].startswith(
                                               ('AllUnits_Login', 'AvailableUnits_Login'))),
                            realpage_units=integration == 'RealPage')
                        file_property_code = _availability_file_property_code(
                            actual_source, [source['file']])
                        if file_property_code:
                            for row in rows:
                                row['__file_property_code'] = file_property_code
                        source_rows[source['file']].extend(rows)
                    except Exception:
                        raw_errors += 1
                if source.get('add_missing_as_units'):
                    # e.g. RealPage's getallunits: a same-integration
                    # all-units feed that carries units getunitlist omits,
                    # keyed by the same raw UnitID. Every property-code
                    # variant of this source is already loaded above.
                    primary_rows.extend(
                        _availability_promote_missing_source_units(
                            primary_rows, source_rows[source['file']], rules))
            rentcafe_codes = {
                str(code).strip()
                for row in primary_rows
                for code in [_availability_value(row, 'voyagerPropertyCode')]
                if code is not None and str(code).strip()
            } if integration == 'RentCafe' else set()
            phase_fields = (rules.get('unit_key') or {}).get(
                'phase_prefix_when_multiple') or []
            phase_prefix_values = {
                str(value).strip().casefold()
                for row in primary_rows
                for field in phase_fields
                for value in [_availability_value(row, field)]
                if value is not None and str(value).strip()
            }

            added_supplemental = []
            supplemental_targets = []
            if supplemental_config:
                try:
                    supplemental_targets = _availability_supplemental_targets(
                        entity, snapshot, as_of, supplemental_config,
                        supplemental_indexes)
                    for (related_integration, related_snapshot,
                         related_file) in supplemental_targets:
                        supplemental_body = _fetch_text(
                            f'{ROOT}{related_integration}/{entity}/'
                            f'{related_snapshot}/{related_file}')
                        property_code = _availability_file_property_code(
                            related_file, supplemental_config.get('files') or [])
                        new_rows = _availability_supplemental_rows(
                            supplemental_body, supplemental_config,
                            primary_rows + added_supplemental, property_code)
                        added_supplemental.extend(new_rows)
                    # A legacy unsuffixed Voyager file has no property code.
                    # It is safe to inherit one only for a single-code
                    # RentCafe building; multi-code files are keyed by their
                    # own filename suffix above.
                    if len(rentcafe_codes) == 1:
                        sole_code = next(iter(rentcafe_codes))
                        for row in added_supplemental:
                            row.setdefault('voyagerPropertyCode', sole_code)
                    primary_rows.extend(added_supplemental)
                except Exception:
                    # The primary RentCafe analysis is still useful if the
                    # optional Voyager supplement is temporarily unreadable.
                    with lock:
                        supplemental_errors += 1

            actual_by_key = {}
            actual_entries = list(enumerate(actual_rows))
            for actual_index, row in actual_entries:
                for key in _availability_keys(row, actual_key):
                    actual_by_key.setdefault(key, (actual_index, row))
            source_by_key = {}
            for source in source_configs:
                # Keyed by (file property code, join-key value): a
                # multi-property-code source must never let one property's
                # row enrich another property's unit just because their
                # local UnitNumber/@IDValue happens to coincide.
                keyed = {}
                join_key = source.get('join_key')
                rows_for_file = source_rows[source['file']]
                for row in rows_for_file:
                    code = row.get('__file_property_code')
                    for key in _availability_keys(row, join_key or []):
                        keyed.setdefault((code, key), row)
                if not join_key:
                    seen_codes = set()
                    for row in rows_for_file:
                        code = row.get('__file_property_code')
                        if code in seen_codes:
                            continue
                        seen_codes.add(code)
                        keyed[(code, '__all__')] = row
                source_by_key[source['file']] = keyed

            produced = []
            seen_unit_keys = set()
            matched_actual_indices = set()
            for primary_row in primary_rows:
                if cap_hit['flag']:
                    break
                required_key = rules.get('required_key') or primary_key
                if required_key and not _availability_keys(primary_row, required_key):
                    # JSON files such as AppFolio units.json can contain
                    # nested marketing/amenity objects alongside real units.
                    # Do not turn those non-unit records into unexplained
                    # availability rows.
                    continue
                # A wait-list/tour-scheduling placeholder (e.g. Voyager's
                # WAITTOUR) is a genuine row in the raw feed, identified purely
                # from its own raw identity field (unit_name_fields). It is
                # counted here and still matched normally below; __wait_unit
                # carries the flag into the values dict so the rules can
                # classify it via a declared override rather than this loop
                # silently dropping it.
                is_wait_unit = _availability_wait_unit(primary_row, rules)
                if is_wait_unit:
                    with lock:
                        wait_filtered += 1
                primary_keys = _availability_keys(primary_row, primary_key)
                unit_key = _availability_unit_key(
                    primary_row, rules, phase_prefix_values)
                actual_match = actual_by_key.get(unit_key)
                if integration == 'RentCafe':
                    is_supplemental = bool(
                        primary_row.get('__supplemental_unit'))
                    # RentCafe unit-details may persist only the bare external
                    # id. A single RentCafe property code is unambiguous; a
                    # Voyager-only supplemental row is also safe to match by
                    # its unit name because the supplement already deduplicates
                    # names within this building.
                    if (actual_match is None and
                            (len(rentcafe_codes) == 1 or is_supplemental)):
                        name = (_availability_value(primary_row, 'apartmentName') or
                                _availability_value(primary_row, 'ApartmentName'))
                        name_key = str(name).strip().casefold() if name is not None else ''
                        actual_match = actual_by_key.get(name_key)
                        if actual_match is not None and is_supplemental:
                            unit_key = name_key
                    if not unit_key and not is_supplemental:
                        actual_match = None
                elif integration == 'Voyager' and actual_match is None:
                    # Current Voyager unit-details snapshots persist a bare
                    # ILS unit external_id for a single property file, even
                    # though the canonical identity is property-unit. Use the
                    # bare value only when this snapshot exposes one Voyager
                    # property code; otherwise it is ambiguous.
                    property_codes = {
                        code for file_name in snapshot_files
                        for code in [_availability_file_property_code(
                            file_name, primary_candidates)]
                        if code
                    }
                    if len(property_codes) == 1:
                        bare_id = _availability_value(primary_row, '@IDValue')
                        if bare_id is not None:
                            actual_match = actual_by_key.get(
                                str(bare_id).strip().casefold())
                # A canonical external identity may occur more than once in a
                # raw feed. Retain the first row and its status deterministically.
                if unit_key in seen_unit_keys:
                    continue
                if unit_key:
                    seen_unit_keys.add(unit_key)
                # unit_details is the canonical post-filter physical-unit
                # feed. Never emit raw API records — including supplemental
                # cross-integration units — when that unit was filtered out
                # before unit_details was produced.
                if actual_match is None:
                    continue
                actual_index, actual_row = actual_match
                if actual_index in matched_actual_indices:
                    continue
                matched_actual_indices.add(actual_index)
                values = dict(primary_row)
                # This unit came from the availability (primary) feed, so
                # rules may gate field tests on the fields actually existing.
                values['__primary_row'] = True
                values['__wait_unit'] = is_wait_unit
                snapshot_datetime = _availability_snapshot_datetime(snapshot)
                if snapshot_datetime is not None:
                    values['__current_date'] = snapshot_datetime.date().isoformat()
                for key, value in primary_row.items():
                    values[f'primary__{key}'] = value
                building_detail = (meta or {}).get(entity, {})
                for field in building_fields:
                    values[f'__building__{field}'] = _availability_value(
                        building_detail, field)
                for rollout_name, rollout_config in rollout_configs.items():
                    if rollout_error:
                        variant = '__unknown__'
                    else:
                        variant = rollout_values.get(entity, {}).get(
                            rollout_name,
                            (rollout_config or {}).get('default', 'disabled'))
                    values[f'__rollout__{rollout_name}'] = variant
                for source in source_configs:
                    related = _availability_source_lookup(
                        source_by_key, source, primary_row, primary_key)
                    if related:
                        for key, value in related.items():
                            values.setdefault(key, value)
                        for field, value in related.items():
                            values[f"{source['file']}__{field}"] = value
                    values[f"__source_present__{source['file']}"] = bool(related)
                values['__direct_stage'] = _availability_direct_prediction(
                    rules, values)[0]
                predicted, reason = _availability_predict(rules, values)
                actual_stage = _availability_value(actual_row, 'availability_stage')
                if actual_stage is None:
                    actual_stage = _availability_value(actual_row, 'availabilityStage')
                try:
                    actual_stage = int(actual_stage) if actual_stage is not None else None
                except (TypeError, ValueError):
                    pass
                # Unknown mappings are specifically prediction mismatches.
                # Keep the reason even when the prediction disagrees with the
                # observed stage so the CSV shows what the current rules did.
                unknown = predicted != actual_stage
                if show_unknown and not unknown:
                    continue
                output = {
                    '_entity': entity, '_snapshot': snapshot,
                    '_supplemental': bool(primary_row.get('__supplemental_unit')),
                    '_unit_details_only': False,
                    'unit_key': unit_key or '',
                    'Actual Availability': actual_stage,
                    'Predicted Availability': predicted,
                    'Availability Reason': reason or (
                        'No matching availability rule' if predicted is None else ''),
                }
                for rollout_name, rollout_config in rollout_configs.items():
                    if rollout_error:
                        variant = '__unknown__'
                    else:
                        variant = rollout_values.get(entity, {}).get(
                            rollout_name,
                            (rollout_config or {}).get('default', 'disabled'))
                    output[f'rollout__{rollout_name}'] = variant
                for field in source_fields['primary']:
                    output[f'primary__{field}'] = _availability_value(primary_row, field)
                for source in source_configs:
                    related = _availability_source_lookup(
                        source_by_key, source, primary_row, primary_key)
                    for field in source_fields[source['file']]:
                        output[f"{source['file']}__{field}"] = _availability_value(related, field)
                for field in actual_fields:
                    output[f'unit_details__{field}'] = _availability_value(actual_row, field)
                produced.append(output)

            # unit-details is the canonical physical-unit inventory. Emit
            # every record that did not match a raw API row, leaving all raw
            # and prediction columns blank so missing upstream data is visible
            # without removing the unit from the report.
            for actual_index, actual_row in actual_entries:
                if actual_index in matched_actual_indices:
                    continue
                actual_stage = _availability_value(actual_row, 'availability_stage')
                if actual_stage is None:
                    actual_stage = _availability_value(actual_row, 'availabilityStage')
                try:
                    actual_stage = int(actual_stage) if actual_stage is not None else None
                except (TypeError, ValueError):
                    pass
                predicted = None
                reason = None
                if rules.get('predict_unit_details_only'):
                    # This unit has no primary/supplemental raw-feed match at
                    # all, so there is no raw API data to base a prediction
                    # on. `values` is deliberately NOT seeded from actual_row:
                    # unit_details is the destination this tool is trying to
                    # reproduce, and mapping logic may only read raw API data,
                    # rollout state, or Snowflake building info -- never the
                    # destination's own fields. Only the explicit provenance
                    # flags below (computed from the raw-feed matching process
                    # itself, not from any unit_details field value) can
                    # explain such a row.
                    values = {}
                    values['__primary_row'] = False
                    values['__supplemental_snapshot_missing'] = not bool(
                        supplemental_targets)
                    values['__supplemental_unit_missing'] = bool(
                        supplemental_targets)
                    snapshot_datetime = _availability_snapshot_datetime(snapshot)
                    if snapshot_datetime is not None:
                        values['__current_date'] = snapshot_datetime.date().isoformat()
                    values['__direct_stage'] = _availability_direct_prediction(
                        rules, values)[0]
                    predicted, reason = _availability_predict(rules, values)
                if show_unknown and predicted == actual_stage:
                    continue
                actual_unit_keys = _availability_keys(actual_row, actual_key)
                output = {
                    '_entity': entity, '_snapshot': snapshot,
                    '_supplemental': False,
                    '_unit_details_only': True,
                    'unit_key': actual_unit_keys[0] if actual_unit_keys else '',
                    'Actual Availability': actual_stage,
                    'Predicted Availability': predicted,
                    'Availability Reason': reason or (
                        'No matching availability rule' if predicted is None else ''),
                }
                for rollout_name in rollout_names:
                    output[f'rollout__{rollout_name}'] = None
                for field in source_fields['primary']:
                    output[f'primary__{field}'] = None
                for source in source_configs:
                    for field in source_fields[source['file']]:
                        output[f"{source['file']}__{field}"] = None
                for field in actual_fields:
                    output[f'unit_details__{field}'] = _availability_value(actual_row, field)
                produced.append(output)
            with lock:
                errors += raw_errors
                if max_results is not None:
                    remaining = max_results - len(all_rows)
                    if remaining <= 0:
                        cap_hit['flag'] = True
                    else:
                        selected = produced[:remaining]
                        all_rows.extend(selected)
                        supplemental_units += sum(
                            1 for row in selected if row.get('_supplemental'))
                        if len(all_rows) >= max_results:
                            cap_hit['flag'] = True
                else:
                    all_rows.extend(produced)
                    supplemental_units += sum(
                        1 for row in produced if row.get('_supplemental'))
                counter['n'] += 1

        if targets:
            with ThreadPoolExecutor(max_workers=SEARCH_WORKERS) as pool:
                target_iter = iter(targets)
                pending = set()
                initial_workers = (SEARCH_WORKERS if max_results is None else
                                   max(1, min(8, max_results, SEARCH_WORKERS)))
                active_workers = initial_workers
                _job_update(
                    job_id, done=0,
                    note=(f'Reading availability snapshots · starting with '
                          f'{initial_workers} concurrent building '
                          f'read{"s" if initial_workers != 1 else ""}…'))

                def fill_workers():
                    while (len(pending) < active_workers and not cap_hit['flag'] and
                           not _job_stop_requested(control_job_id)):
                        try:
                            pending.add(pool.submit(probe, next(target_iter)))
                        except StopIteration:
                            break

                fill_workers()
                limit_note_shown = False
                while pending:
                    completed, pending = wait(pending, return_when=FIRST_COMPLETED)
                    # Surface worker exceptions instead of silently losing a
                    # probe and leaving the progress state unexplained.
                    for future in completed:
                        future.result()
                    stop_requested = _job_stop_requested(control_job_id)
                    if cap_hit['flag'] or stop_requested:
                        for future in pending:
                            future.cancel()
                        pending = {future for future in pending if not future.cancelled()}
                        if pending:
                            limit_note_shown = True
                            _job_update(
                                job_id, done=counter['n'],
                                note=((f'Stop requested at {len(all_rows):,} units · '
                                       if stop_requested else
                                       f'Result limit reached at {len(all_rows):,} units · ') +
                                      f'finishing {len(pending)} in-flight '
                                      f'building read{"s" if len(pending) != 1 else ""}…'))
                    else:
                        if max_results is not None and counter['n'] >= 4:
                            # Estimate how many concurrent buildings are still
                            # useful from the observed unit yield. Zero/very
                            # low-yield filters ramp toward full concurrency;
                            # high-yield integrations stay small and avoid
                            # dozens of unnecessary S3/Voyager reads.
                            remaining_rows = max(0, max_results - len(all_rows))
                            observed_yield = len(all_rows) / max(1, counter['n'])
                            estimated_buildings = int(
                                remaining_rows / max(observed_yield, .25) + .999)
                            active_workers = min(
                                SEARCH_WORKERS,
                                max(initial_workers, estimated_buildings))
                        fill_workers()
                        if max_results is not None:
                            _job_update(
                                job_id, done=counter['n'],
                                note=(f'{len(all_rows):,} of {max_results:,} units '
                                      f'collected · {counter["n"]:,} buildings '
                                      f'checked · {active_workers} concurrent reads'))
                        elif counter['n'] and counter['n'] % 10 == 0:
                            _job_update(
                                job_id, done=counter['n'],
                                note=(f'{len(all_rows):,} units evaluated · '
                                      f'{counter["n"]:,} buildings checked'))

                stopped = _job_stop_requested(control_job_id)
                if cap_hit['flag'] or limit_note_shown or stopped:
                    _job_update(job_id, done=counter['n'], total=counter['n'],
                                note=((f'Stop requested · finalizing {len(all_rows):,} units…')
                                      if stopped else
                                      f'Result limit reached · finalizing {len(all_rows):,} units…'))

        distinct_entities = sorted({row['_entity'] for row in all_rows})
        if not metadata_checked and distinct_entities:
            _job_update(job_id, done=counter['n'], note='Loading building details…')
            meta, cmap, enrich_error = _enrich_with_snowflake(job_id, distinct_entities)
        _job_update(job_id, done=counter['n'], note='Preparing CSV columns…')
        fieldnames = ['building', 'snapshot', 'building_name', 'org_id', 'org_name', 'snapshot link',
                      'unit_key', 'Actual Availability', 'Predicted Availability', 'Availability Reason']
        fieldnames.extend(f'rollout__{name}' for name in rollout_names)
        for source in source_configs:
            fieldnames.extend(f"{source['file']}__{field}" for field in source_fields[source['file']])
        fieldnames.extend(f'primary__{field}' for field in source_fields['primary'])
        fieldnames.extend(f'unit_details__{field}' for field in actual_fields)
        for row in all_rows:
            building = row['_entity']
            detail = meta.get(building, {}) if meta else {}
            row['building'] = _strip_building_prefix(building)
            row['snapshot'] = row['_snapshot']
            row['building_name'] = detail.get(cmap['name'], '') if cmap and cmap.get('name') else ''
            row['org_id'] = _csv_cell(detail.get(cmap['org'], '')) if cmap and cmap.get('org') else ''
            org_name_col = cmap.get('org_name') if cmap else None
            row['org_name'] = (detail.get(org_name_col, '') if org_name_col else '') or detail.get('ORGANIZATION_NAME', '')
            row['snapshot link'] = _snapshot_link(building, row['_snapshot'], row.get('org_id'))
        _job_update(job_id, done=counter['n'], note=f'Writing {len(all_rows):,} CSV rows…')
        _write_availability_csv(job_id, all_rows, fieldnames)
        _job_update(job_id, done=counter['n'], note='Finalizing result preview…')
        preview = [{field: _csv_cell(row.get(field)) for field in fieldnames} for row in all_rows[:FIELDS_PREVIEW]]
        _job_update(job_id, done=counter['n'], status='done', finished=time.time(), result={
            'integration': integration, 'asOf': as_of.isoformat() if as_of else None,
            'searched': counter['n'], 'buildings': len(entities), 'rowCount': len(all_rows),
            'unknownCount': sum(1 for row in all_rows
                                if row.get('Predicted Availability') != row.get('Actual Availability')),
            'unitDetailsOnlyCount': sum(
                1 for row in all_rows if row.get('_unit_details_only')),
            'limit': max_results, 'limited': bool(max_results is not None and cap_hit['flag']),
            'stopped': _job_stop_requested(control_job_id),
            'includeStudents': include_students,
            'includeApplications': include_applications,
            'includeNotLaunchedOnLeasing': include_not_launched_on_leasing,
            'supplementalUnits': supplemental_units,
            'supplementalErrors': supplemental_errors,
            'waitFiltered': wait_filtered,
            'showUnknown': show_unknown, 'fields': fieldnames, 'preview': preview,
            'noSnapshot': no_snapshot, 'errors': errors, 'filterNote': filter_note,
            'enrichError': enrich_error,
            'enrichCredentialIssue': snowflake_db.credential_error(enrich_error),
            'rolloutError': rollout_error,
            'rolloutCredentialIssue': snowflake_db.credential_error(rollout_error),
            'downloadUrl': f'/api/search/csv/{job_id}',
        })
        if record_history:
            _history_record(job_id, 'availability', _job_get(job_id)['result'], {
                'org': org,
                'buildings': building_filter,
                'asOf': as_of.isoformat() if as_of else None,
                'showUnknown': show_unknown,
                'includeStudents': include_students,
                'includeApplications': include_applications,
                'includeNotLaunchedOnLeasing': include_not_launched_on_leasing,
                'supplementalUnits': supplemental_units,
                'supplementalErrors': supplemental_errors,
                'waitFiltered': wait_filtered,
                'limit': max_results,
            })
    except Exception as e:
        _job_update(job_id, status='error', error=str(e), finished=time.time())


def _run_availability_batch_job(job_id: str, integrations: list, org: str = '',
                                building_filter: str = '', as_of=None,
                                show_unknown: bool = False,
                                include_students: bool = False,
                                include_applications: bool = False,
                                include_not_launched_on_leasing: bool = False,
                                max_results: int | None = None):
    """Run the cataloged integrations sequentially and combine their CSVs.

    Sequential child jobs keep S3/Snowflake load bounded while the parent job
    exposes one stable progress stream and one download for the user.
    """
    try:
        integrations = list(dict.fromkeys(integrations))
        _job_update(job_id, total=len(integrations), note='Preparing integrations…')
        combined_rows = []
        combined_fields = []
        searched = buildings = unknown = errors = no_snapshot = 0
        supplemental_units = supplemental_errors = wait_filtered = 0
        unit_details_only = 0
        notes = []
        failed = []
        skipped = []
        rollout_errors = []

        def add_fields(fields):
            for field in fields:
                if field not in combined_fields:
                    combined_fields.append(field)

        for position, integration in enumerate(integrations, start=1):
            if _job_stop_requested(job_id):
                skipped = integrations[position - 1:]
                _job_update(job_id, done=position - 1,
                            note=f'Stop requested · finalizing {len(combined_rows):,} rows')
                break
            if max_results is not None and len(combined_rows) >= max_results:
                skipped = integrations[position - 1:]
                _job_update(job_id, done=position - 1,
                            note=f'Result limit {max_results:,} reached')
                break

            if not _index_load(integration):
                failed.append(integration)
                errors += 1
                _job_update(job_id, done=position,
                            note=f'{integration} index unavailable')
                continue

            if max_results is None:
                remaining = None
            else:
                remaining_total = max_results - len(combined_rows)
                integrations_left = len(integrations) - position + 1
                # Spread a global cap across the catalog so an all-
                # integrations smoke test samples each integration whenever
                # the requested limit is large enough to do so.
                remaining = max(1, (remaining_total + integrations_left - 1) // integrations_left)
            child_id = _job_new('availability', integration)
            _job_update(job_id, done=position - 1,
                        note=f'Checking {integration}…')
            _run_availability_job(
                child_id, integration, org, building_filter, as_of, show_unknown,
                include_students, include_applications,
                include_not_launched_on_leasing, remaining, False, job_id)
            child = _job_get(child_id) or {}
            if child.get('status') != 'done' or not child.get('result'):
                failed.append(integration)
                errors += 1
                if child.get('error'):
                    notes.append(f'{integration}: {child["error"]}')
                _job_update(job_id, done=position, note=f'{integration} failed')
                continue

            result = child['result']
            add_fields(result.get('fields') or [])
            searched += result.get('searched') or 0
            buildings += result.get('buildings') or 0
            unknown += result.get('unknownCount') or 0
            errors += result.get('errors') or 0
            no_snapshot += result.get('noSnapshot') or 0
            supplemental_units += result.get('supplementalUnits') or 0
            supplemental_errors += result.get('supplementalErrors') or 0
            wait_filtered += result.get('waitFiltered') or 0
            unit_details_only += result.get('unitDetailsOnlyCount') or 0
            if result.get('filterNote'):
                notes.append(f'{integration}: {result["filterNote"]}')
            if result.get('rolloutError'):
                rollout_errors.append(f'{integration}: {result["rolloutError"]}')

            child_path = os.path.join(EXPORT_DIR, f'{child_id}.csv')
            with open(child_path, newline='', encoding='utf-8') as fh:
                combined_rows.extend(dict(row) for row in csv.DictReader(fh))
            if max_results is not None:
                combined_rows = combined_rows[:max_results]
            _job_update(job_id, done=position,
                        note=f'{integration}: {len(combined_rows):,} rows collected')

        if not combined_fields:
            combined_fields = ['building', 'snapshot', 'building_name', 'org_id',
                               'org_name', 'snapshot link']
        _write_availability_csv(job_id, combined_rows, combined_fields)
        preview = [{field: _csv_cell(row.get(field)) for field in combined_fields}
                   for row in combined_rows[:FIELDS_PREVIEW]]
        _job_update(job_id, done=len(integrations), status='done', finished=time.time(),
                    result={
                        'integration': 'All integrations',
                        'integrations': integrations,
                        'asOf': as_of.isoformat() if as_of else None,
                        'searched': searched, 'buildings': buildings,
                        'rowCount': len(combined_rows), 'unknownCount': unknown,
                        'unitDetailsOnlyCount': unit_details_only,
                        'supplementalUnits': supplemental_units,
                        'supplementalErrors': supplemental_errors,
                        'waitFiltered': wait_filtered,
                        'showUnknown': show_unknown, 'fields': combined_fields,
                        'preview': preview, 'noSnapshot': no_snapshot,
                        'errors': errors, 'filterNote': ' · '.join(dict.fromkeys(notes)),
                        'failedIntegrations': failed,
                        'skippedIntegrations': skipped,
                        'rolloutError': ' · '.join(rollout_errors),
                        'rolloutCredentialIssue': any(
                            snowflake_db.credential_error(error) for error in rollout_errors),
                        'limit': max_results,
                        'limited': bool(max_results is not None and
                                        len(combined_rows) >= max_results),
                        'stopped': _job_stop_requested(job_id),
                        'includeStudents': include_students,
                        'includeApplications': include_applications,
                        'includeNotLaunchedOnLeasing': include_not_launched_on_leasing,
                        'downloadUrl': f'/api/search/csv/{job_id}',
                    })
        _history_record(job_id, 'availability', _job_get(job_id)['result'], {
            'org': org,
            'buildings': building_filter,
            'asOf': as_of.isoformat() if as_of else None,
            'showUnknown': show_unknown,
            'includeStudents': include_students,
            'includeApplications': include_applications,
            'includeNotLaunchedOnLeasing': include_not_launched_on_leasing,
            'supplementalUnits': supplemental_units,
            'supplementalErrors': supplemental_errors,
            'waitFiltered': wait_filtered,
            'limit': max_results,
        })
    except Exception as e:
        _job_update(job_id, status='error', error=str(e), finished=time.time())


# ── Sync Issues ───────────────────────────────────────────────────────────────

SYNC_ISSUES_QUERY_TIMEOUT = 600   # seconds; the CTE chain is expensive

# Cap the unit identifiers sent per reason per building.  A single sync can mark
# thousands of units unavailable and the whole payload is re-sent on every poll.
SYNC_ISSUES_MAX_UNITS_PER_REASON = 250

# How far back to look for the snapshot preceding the one being analysed.  That
# earlier snapshot is the baseline used to tell units this sync newly marked
# unavailable apart from units that were already unavailable going in.
SYNC_ISSUES_BASELINE_LOOKBACK_HOURS = 72

# The building/org lookup that feeds rollout and building-flag overrides can
# take ~50s on a cold warehouse — far past the interactive ENRICH_TIMEOUT.  It
# runs once per job, before the S3 fan-out, so it can afford to wait.
SYNC_ISSUES_ENRICH_TIMEOUT = 180

# Simplified version of the dashboard SQL: only the unavailable-threshold branch.
# Parameters (positional %s in order):
#   1 audit_date_range_start  (date/timestamp)
#   2 audit_date_range_end    (date/timestamp)
#   3..N one bind param per selected integration (0 params when "All
#        Integrations" — the {integration_clause} format placeholder becomes
#        the literal TRUE in that case, so no params are needed there)
#   N+1 new_import_window_minutes (integer)
#   N+2 unit_unavailable_threshold (decimal 0–1)
# LIMIT and the integration clause are both formatted in ({limit} as a safe
# integer, {integration_clause} as a parameterized SQL fragment — see
# _sync_issues_integration_clause).
_SYNC_ISSUES_SQL = """\
WITH buildings AS (
    SELECT ID AS BUILDING_ID, ORG_ID, ORG_NAME, BUILDING_NAME
    FROM ELISE.DA.DIM_BUILDINGS
    WHERE IS_TEST = FALSE
        AND COALESCE(IS_STUDENT_HOUSING, FALSE) = FALSE
),
audit_rows AS (
    SELECT
        a.BUILDING_ID, a.CHANGE_GROUP_ID, a.UNIT_ID, a.CHANGE_TYPE,
        a.SOURCE, a.APP_USER_ID, a.CHANGE_TIMESTAMP,
        a.OLD_VALUE:availability_stage::NUMBER AS OLD_AVAILABILITY_STAGE,
        a.NEW_VALUE:availability_stage::NUMBER AS NEW_AVAILABILITY_STAGE,
        a.OLD_VALUE:active::NUMBER AS OLD_ACTIVE,
        a.NEW_VALUE:active::NUMBER AS NEW_ACTIVE,
        a.OLD_VALUE:is_deleted::BOOLEAN AS OLD_IS_DELETED,
        a.NEW_VALUE:is_deleted::BOOLEAN AS NEW_IS_DELETED,
        a.OLD_VALUE:is_it_default_unit::NUMBER AS OLD_IS_IT_DEFAULT_UNIT,
        a.NEW_VALUE:is_it_default_unit::NUMBER AS NEW_IS_IT_DEFAULT_UNIT,
        a.OLD_VALUE:unit_use_type::STRING AS OLD_UNIT_USE_TYPE,
        a.NEW_VALUE:unit_use_type::STRING AS NEW_UNIT_USE_TYPE
    FROM ENG_REPORTING.PUBLIC.UNIT_AUDIT_LOG_V2 AS a
    WHERE a.CHANGE_TIMESTAMP >= %s
        AND a.CHANGE_TIMESTAMP < DATEADD('day', 1, %s)
        AND a.CHANGE_GROUP_ID IS NOT NULL
        AND a.CHANGE_TYPE IN ('unit_created', 'unit_updated', 'unit_deleted')
),
audit_enriched AS (
    SELECT a.*,
        MAX(IFF(
            a.CHANGE_TYPE = 'unit_updated'
            AND a.OLD_ACTIVE = 1 AND a.OLD_IS_IT_DEFAULT_UNIT = 0
            AND COALESCE(a.OLD_IS_DELETED, FALSE) = FALSE
            AND (a.OLD_UNIT_USE_TYPE IS NULL OR a.OLD_UNIT_USE_TYPE != 'commercial')
            AND NOT (a.NEW_ACTIVE = 1 AND a.NEW_IS_IT_DEFAULT_UNIT = 0
                AND COALESCE(a.NEW_IS_DELETED, FALSE) = FALSE
                AND (a.NEW_UNIT_USE_TYPE IS NULL OR a.NEW_UNIT_USE_TYPE != 'commercial')),
            1, 0
        )) OVER (PARTITION BY a.BUILDING_ID, a.CHANGE_GROUP_ID, a.UNIT_ID)
            AS IS_DEACTIVATED_IN_SYNC
    FROM audit_rows AS a
),
syncs AS (
    SELECT
        a.BUILDING_ID, a.CHANGE_GROUP_ID,
        MIN(a.CHANGE_TIMESTAMP) AS SYNC_STARTED_AT,
        MAX(a.CHANGE_TIMESTAMP) AS SYNC_COMPLETED_AT,
        LISTAGG(DISTINCT a.SOURCE, ', ') WITHIN GROUP (ORDER BY a.SOURCE) AS SOURCES,
        LISTAGG(DISTINCT a.APP_USER_ID, ', ') WITHIN GROUP (ORDER BY a.APP_USER_ID) AS APP_USER_IDS,
        COUNT(DISTINCT a.UNIT_ID) AS UNITS_CHANGED,
        COUNT(DISTINCT CASE
            WHEN a.CHANGE_TYPE = 'unit_updated'
                AND a.OLD_AVAILABILITY_STAGE IN (0, 1)
                AND a.NEW_AVAILABILITY_STAGE = 9
                AND a.OLD_ACTIVE = 1 AND a.OLD_IS_IT_DEFAULT_UNIT = 0
                AND COALESCE(a.OLD_IS_DELETED, FALSE) = FALSE
                AND (a.OLD_UNIT_USE_TYPE IS NULL OR a.OLD_UNIT_USE_TYPE != 'commercial')
                AND a.IS_DEACTIVATED_IN_SYNC = 0
                THEN a.UNIT_ID END) AS UNITS_MARKED_UNAVAILABLE
    FROM audit_enriched AS a
    GROUP BY 1, 2
),
active_units AS (
    SELECT u.BUILDING_ID,
        COUNT(*) AS TOTAL_UNITS,
        COUNT_IF(u.AVAILABILITY_STAGE = 9) AS TOTAL_UNAVAILABLE_UNITS_NOW
    FROM ELISE.FANSCAN_LOGICAL_PUBLIC.UNIT_DETAILS AS u
    INNER JOIN (SELECT DISTINCT BUILDING_ID FROM syncs) AS s ON u.BUILDING_ID = s.BUILDING_ID
    WHERE u.ACTIVE = 1 AND u.IS_IT_DEFAULT_UNIT = 0
        AND (u.IS_DELETED IS NULL OR u.IS_DELETED = FALSE)
        AND (u.UNIT_USE_TYPE IS NULL OR u.UNIT_USE_TYPE != 'commercial')
    GROUP BY 1
),
scored AS (
    SELECT b.ORG_ID, b.ORG_NAME, b.BUILDING_NAME,
        s.BUILDING_ID, s.CHANGE_GROUP_ID, s.SYNC_STARTED_AT, s.SYNC_COMPLETED_AT,
        s.SOURCES, s.APP_USER_IDS, u.TOTAL_UNITS, u.TOTAL_UNAVAILABLE_UNITS_NOW,
        s.UNITS_CHANGED, s.UNITS_MARKED_UNAVAILABLE
    FROM syncs AS s
    INNER JOIN buildings AS b ON s.BUILDING_ID = b.BUILDING_ID
    INNER JOIN active_units AS u ON s.BUILDING_ID = u.BUILDING_ID
),
candidate_syncs AS (
    SELECT * FROM scored
    WHERE UNITS_MARKED_UNAVAILABLE >= 10
        AND ({integration_clause})
),
snapshot_unit_state_before AS (
    SELECT f.BUILDING_ID, f.CHANGE_GROUP_ID, s.DBT_VALID_FROM,
        s.ACTIVE, s.AVAILABILITY_STAGE, s.IS_IT_DEFAULT_UNIT, s.IS_DELETED, s.UNIT_USE_TYPE
    FROM candidate_syncs AS f
    INNER JOIN ELISE.DA.UNIT_DETAILS_SNAPSHOT AS s
        ON s.BUILDING_ID = f.BUILDING_ID
        AND s.DBT_VALID_FROM <= DATEADD('minute', -1, f.SYNC_STARTED_AT)
        AND (s.DBT_VALID_TO > DATEADD('minute', -1, f.SYNC_STARTED_AT) OR s.DBT_VALID_TO IS NULL)
),
historical_unit_counts AS (
    SELECT BUILDING_ID, CHANGE_GROUP_ID,
        MAX(DBT_VALID_FROM) AS SNAPSHOT_AS_OF,
        COUNT_IF(ACTIVE = 1 AND IS_IT_DEFAULT_UNIT = 0
            AND (IS_DELETED IS NULL OR IS_DELETED = FALSE)
            AND (UNIT_USE_TYPE IS NULL OR UNIT_USE_TYPE != 'commercial')) AS TOTAL_UNITS_BEFORE_SYNC,
        COUNT_IF(ACTIVE = 1 AND AVAILABILITY_STAGE = 9 AND IS_IT_DEFAULT_UNIT = 0
            AND (IS_DELETED IS NULL OR IS_DELETED = FALSE)
            AND (UNIT_USE_TYPE IS NULL OR UNIT_USE_TYPE != 'commercial')) AS TOTAL_UNAVAILABLE_UNITS_BEFORE_SYNC
    FROM snapshot_unit_state_before
    GROUP BY 1, 2
),
pre_sync_audit AS (
    SELECT f.BUILDING_ID, f.CHANGE_GROUP_ID,
        COUNT(DISTINCT CASE
            WHEN a.CHANGE_TYPE = 'unit_created'
                AND a.NEW_VALUE:active::NUMBER = 1 AND a.NEW_VALUE:is_it_default_unit::NUMBER = 0
                AND COALESCE(a.NEW_VALUE:is_deleted::BOOLEAN, FALSE) = FALSE
                AND COALESCE(a.NEW_VALUE:unit_use_type::STRING, '') != 'commercial'
                THEN a.UNIT_ID END) AS UNITS_CREATED_SINCE_SNAPSHOT,
        COUNT(DISTINCT CASE
            WHEN a.CHANGE_TYPE IN ('unit_deleted', 'unit_updated')
                AND a.OLD_VALUE:active::NUMBER = 1 AND a.OLD_VALUE:is_it_default_unit::NUMBER = 0
                AND COALESCE(a.OLD_VALUE:is_deleted::BOOLEAN, FALSE) = FALSE
                AND COALESCE(a.OLD_VALUE:unit_use_type::STRING, '') != 'commercial'
                AND NOT (a.CHANGE_TYPE = 'unit_updated'
                    AND a.NEW_VALUE:active::NUMBER = 1 AND a.NEW_VALUE:is_it_default_unit::NUMBER = 0
                    AND COALESCE(a.NEW_VALUE:is_deleted::BOOLEAN, FALSE) = FALSE
                    AND COALESCE(a.NEW_VALUE:unit_use_type::STRING, '') != 'commercial')
                THEN a.UNIT_ID END) AS UNITS_REMOVED_SINCE_SNAPSHOT
    FROM candidate_syncs AS f
    INNER JOIN historical_unit_counts AS h ON f.BUILDING_ID = h.BUILDING_ID AND f.CHANGE_GROUP_ID = h.CHANGE_GROUP_ID
    INNER JOIN ENG_REPORTING.PUBLIC.UNIT_AUDIT_LOG_V2 AS a
        ON a.BUILDING_ID = f.BUILDING_ID
        AND a.CHANGE_TIMESTAMP > h.SNAPSHOT_AS_OF
        AND a.CHANGE_TIMESTAMP < f.SYNC_STARTED_AT
    GROUP BY 1, 2
),
recent_unit_creations AS (
    SELECT f.BUILDING_ID, f.CHANGE_GROUP_ID,
        COUNT(DISTINCT a.UNIT_ID) AS UNITS_CREATED_RECENTLY
    FROM candidate_syncs AS f
    INNER JOIN ENG_REPORTING.PUBLIC.UNIT_AUDIT_LOG_V2 AS a
        ON a.BUILDING_ID = f.BUILDING_ID
        AND a.CHANGE_TYPE = 'unit_created'
        AND a.CHANGE_TIMESTAMP >= DATEADD('minute', -%s, f.SYNC_STARTED_AT)
        AND a.CHANGE_TIMESTAMP <= f.SYNC_STARTED_AT
        AND a.NEW_VALUE:active::NUMBER = 1 AND a.NEW_VALUE:is_it_default_unit::NUMBER = 0
        AND COALESCE(a.NEW_VALUE:is_deleted::BOOLEAN, FALSE) = FALSE
        AND COALESCE(a.NEW_VALUE:unit_use_type::STRING, '') != 'commercial'
    GROUP BY 1, 2
),
history_adjusted AS (
    SELECT f.*,
        COALESCE(r.UNITS_CREATED_RECENTLY, 0) AS UNITS_CREATED_RECENTLY,
        h.TOTAL_UNITS_BEFORE_SYNC AS TOTAL_UNITS_IN_SNAPSHOT,
        COALESCE(p.UNITS_CREATED_SINCE_SNAPSHOT, 0) AS UNITS_CREATED_SINCE_SNAPSHOT,
        COALESCE(p.UNITS_REMOVED_SINCE_SNAPSHOT, 0) AS UNITS_REMOVED_SINCE_SNAPSHOT,
        GREATEST(
            h.TOTAL_UNITS_BEFORE_SYNC
                + COALESCE(p.UNITS_CREATED_SINCE_SNAPSHOT, 0)
                - COALESCE(p.UNITS_REMOVED_SINCE_SNAPSHOT, 0),
            0
        ) AS TOTAL_UNITS_BEFORE_SYNC,
        h.TOTAL_UNAVAILABLE_UNITS_BEFORE_SYNC
    FROM candidate_syncs AS f
    LEFT JOIN historical_unit_counts AS h ON f.BUILDING_ID = h.BUILDING_ID AND f.CHANGE_GROUP_ID = h.CHANGE_GROUP_ID
    LEFT JOIN pre_sync_audit AS p ON f.BUILDING_ID = p.BUILDING_ID AND f.CHANGE_GROUP_ID = p.CHANGE_GROUP_ID
    LEFT JOIN recent_unit_creations AS r ON f.BUILDING_ID = r.BUILDING_ID AND f.CHANGE_GROUP_ID = r.CHANGE_GROUP_ID
),
scored_with_history AS (
    SELECT f.*,
        GREATEST(f.TOTAL_UNITS_BEFORE_SYNC, f.UNITS_MARKED_UNAVAILABLE, 0) AS TOTAL_UNITS_AFTER_SYNC,
        LEAST(
            GREATEST(f.TOTAL_UNITS_BEFORE_SYNC, f.UNITS_MARKED_UNAVAILABLE, 0),
            f.TOTAL_UNAVAILABLE_UNITS_BEFORE_SYNC + f.UNITS_MARKED_UNAVAILABLE
        ) AS TOTAL_UNAVAILABLE_UNITS_AFTER_SYNC,
        DIV0(
            f.UNITS_MARKED_UNAVAILABLE,
            GREATEST(f.TOTAL_UNITS_BEFORE_SYNC, f.UNITS_MARKED_UNAVAILABLE, 0)
        ) AS PCT_UNITS_MARKED_UNAVAILABLE
    FROM history_adjusted AS f
),
scored_final AS (
    SELECT s.*,
        s.UNITS_CREATED_RECENTLY > 0
            AND DIV0(s.UNITS_CREATED_RECENTLY, s.TOTAL_UNITS_AFTER_SYNC) >= 0.5
            AS IS_LIKELY_INITIAL_IMPORT
    FROM scored_with_history AS s
),
flagged AS (
    SELECT * FROM scored_final
    WHERE PCT_UNITS_MARKED_UNAVAILABLE >= %s
        AND UNITS_MARKED_UNAVAILABLE >= 10
        AND TOTAL_UNITS_BEFORE_SYNC IS NOT NULL
        AND NOT IS_LIKELY_INITIAL_IMPORT
    ORDER BY SYNC_STARTED_AT DESC
    LIMIT {limit}
)
SELECT
    f.ORG_NAME, f.BUILDING_NAME, f.BUILDING_ID, f.CHANGE_GROUP_ID,
    'https://app.meetelise.com/tools/snapshot-viewer?tab=mits&org_id='
        || f.ORG_ID
        || '&building_id=' || f.BUILDING_ID
        || '&reference_time='
        || REPLACE(
            TO_CHAR(DATEADD('minute', -1, f.SYNC_STARTED_AT), 'YYYY-MM-DD"T"HH24:MI:SS.FF3"Z"'),
            ':', '%%3A'
        )
        || '&num_before=1&num_after=1&gc_search_mode=mc_id' AS SNAPSHOT_LINK,
    f.SYNC_STARTED_AT, f.SYNC_COMPLETED_AT, f.SOURCES, f.APP_USER_IDS,
    f.TOTAL_UNITS, f.TOTAL_UNITS_BEFORE_SYNC, f.TOTAL_UNITS_AFTER_SYNC,
    f.TOTAL_UNAVAILABLE_UNITS_BEFORE_SYNC, f.UNITS_MARKED_UNAVAILABLE,
    f.TOTAL_UNAVAILABLE_UNITS_AFTER_SYNC, f.TOTAL_UNAVAILABLE_UNITS_NOW,
    f.PCT_UNITS_MARKED_UNAVAILABLE, f.IS_LIKELY_INITIAL_IMPORT
FROM flagged AS f
ORDER BY f.SYNC_STARTED_AT DESC
"""


def _infer_sync_integration(sources: str) -> str | None:
    """Map SOURCES string (e.g. 'RentCafe, YardiVoyager') to an availability
    agent integration name, or None if none matches."""
    available = set(_availability_rules().get('integrations', {}).keys())
    aliases = {'YardiVoyager': 'Voyager', 'yardivoyager': 'Voyager'}
    for source in sources.split(','):
        s = source.strip()
        if s in available:
            return s
        mapped = aliases.get(s) or aliases.get(s.lower())
        if mapped and mapped in available:
            return mapped
    return None


def _sync_issues_integration_clause(integrations: list) -> tuple[str, list]:
    """SQL fragment + bind params for filtering candidate_syncs by SOURCES.

    Each selected integration becomes its own CONTAINS(UPPER(SOURCES), ...)
    check, OR'd together, so any number can be selected at once; e.g.
    'Voyager' matches 'YardiVoyager' as a substring, mirroring how the old
    single-select filter already worked without needing an alias lookup.
    No selections means "All Integrations": the fragment is the literal
    TRUE and no params are added.
    """
    names = [str(n).strip() for n in (integrations or []) if str(n).strip()]
    if not names:
        return 'TRUE', []
    clause = ' OR '.join('CONTAINS(UPPER(SOURCES), UPPER(%s))' for _ in names)
    return f'({clause})', names


def _sync_issues_target(sync):
    """(integration, entity, as_of) for one sync row; integration None if the
    source has no availability rules.  Shared by the metadata pre-pass and the
    per-building probe so both agree on which snapshot window applies."""
    integration = _infer_sync_integration(str(sync.get('SOURCES') or ''))
    if not integration:
        return None, None, None
    raw = str(sync.get('BUILDING_ID') or '')
    entity = raw if raw.lower().startswith('building_') else f'building_{raw}'
    completed_raw = sync.get('SYNC_COMPLETED_AT')
    try:
        if isinstance(completed_raw, str):
            completed_dt = datetime.fromisoformat(
                completed_raw.replace('Z', '+00:00'))
        else:
            completed_dt = completed_raw
        if completed_dt is not None and completed_dt.tzinfo is None:
            completed_dt = completed_dt.replace(tzinfo=timezone.utc)
    except (TypeError, ValueError, AttributeError):
        completed_dt = None
    as_of = (completed_dt + timedelta(minutes=90)) if completed_dt else None
    return integration, entity, as_of


def _sync_issues_reason_rows(reason_counts, reason_counts_new,
                             total_all, total_new):
    """One row per reason carrying both the all-units and newly-marked counts."""
    rows = []
    for reason in set(reason_counts) | set(reason_counts_new):
        c_all = reason_counts.get(reason, 0)
        c_new = reason_counts_new.get(reason, 0)
        rows.append({
            'reason':   reason,
            'count':    c_all,
            'countNew': c_new,
            'pct':      round(100 * c_all / total_all, 1) if total_all else 0,
            'pctNew':   round(100 * c_new / total_new, 1) if total_new else 0,
        })
    # Sorted by the all-units count; the UI re-sorts when showing newly-marked.
    rows.sort(key=lambda r: (-r['count'], r['reason']))
    return rows


def _sync_issues_partial_result(reason_counts, by_integration,
                                stage_9_count, total_analyzed,
                                n_done, n_total, skipped, partial=True,
                                buildings=None, reason_counts_new=None,
                                newly_marked_count=0, by_integration_new=None,
                                baseline_missing=0, rollout_error=None,
                                enrich_error=None):
    """Build the result dict used both for live updates and the final payload."""
    reason_counts_new = reason_counts_new or {}
    return {
        'partial': partial,
        'syncsAnalyzed': n_done,
        'syncsWithData': n_done - skipped,
        'skipped': skipped,
        'totalUnitsAnalyzed': total_analyzed,
        'unavailableUnits': stage_9_count,
        # Units this sync actually flipped to unavailable, per the snapshot
        # immediately preceding the one analysed.
        'newlyMarkedUnits': newly_marked_count,
        # Buildings with no usable pre-sync snapshot, so their units cannot be
        # split into newly-marked vs already-unavailable.
        'baselineMissingBuildings': baseline_missing,
        'byIntegration': dict(by_integration),
        'byIntegrationNew': dict(by_integration_new or {}),
        'reasonDistribution': _sync_issues_reason_rows(
            reason_counts, reason_counts_new, stage_9_count, newly_marked_count),
        # Metadata-lookup failures leave rollout-dependent overrides dormant,
        # so surface them instead of silently under-reporting reasons.
        'rolloutError': rollout_error,
        'enrichError':  enrich_error,
        'rolloutCredentialIssue': (
            snowflake_db.credential_error(rollout_error) if rollout_error else None),
        # Per-building breakdown, keyed by BUILDING_ID, so the UI can expand a
        # single sync row into its own distribution and unit list.
        'buildings': dict(buildings or {}),
    }


def _sync_issues_first_value(*sources, keys):
    """Return the first non-empty value found under `keys` across `sources`."""
    for src in sources:
        if not isinstance(src, dict):
            continue
        for k in keys:
            v = src.get(k)
            if v not in (None, '', []):
                return v
    return None


# Field-name candidates vary by integration, so probe a few spellings each.
# The unit number comes from the actual (unit_details) file; it is reported
# alongside the join key rather than instead of it, because the two can differ.
_SI_UNIT_NUMBER_KEYS = ('unit_number', 'unitNumber', 'apartmentName',
                        'unitName', 'unit_name', 'external_id')
_SI_UNIT_STATUS_KEYS = ('unitStatus', 'unit_status', 'status',
                        'occupancyStatus', 'availabilityStatus')
_SI_UNIT_RENT_KEYS   = ('minimumRent', 'marketRent', 'askingRent', 'rent',
                        'market_rent', 'minimum_rent')
_SI_UNIT_DATE_KEYS   = ('availableDate', 'available_date', 'dateAvailable',
                        'madeReadyDate')
_SI_UNIT_SQFT_KEYS   = ('sqft', 'squareFeet', 'square_feet', 'squareFootage')


def _sync_issues_unit_label(primary_row, actual_row, unit_key, values=None):
    """Shape one unavailable unit for the per-building expand view.

    Reports the join key and the unit_details unit number separately, since a
    mismatch between them is itself a useful signal.
    """
    number = _sync_issues_first_value(actual_row, primary_row,
                                      keys=_SI_UNIT_NUMBER_KEYS)
    unit = {
        'unitKey':    str(unit_key) if unit_key not in (None, '') else '—',
        'unitNumber': str(number)   if number   not in (None, '') else '—',
    }
    for field, keys in (('status', _SI_UNIT_STATUS_KEYS),
                        ('rent',   _SI_UNIT_RENT_KEYS),
                        ('availableDate', _SI_UNIT_DATE_KEYS),
                        ('sqft',   _SI_UNIT_SQFT_KEYS)):
        v = _sync_issues_first_value(primary_row, actual_row, values, keys=keys)
        if v not in (None, ''):
            unit[field] = v
    return unit


def _sync_issues_building_detail(sync, integration=None, snapshot=None,
                                 skip_reason=None, stage_9=0, analyzed=0,
                                 reasons=None, units=None, reasons_new=None,
                                 newly_marked=0, baseline_snapshot=None,
                                 baseline_available=False,
                                 excluded_from_issues=False):
    """Shape one building's analysis outcome for the per-sync expand view."""
    reasons     = reasons or {}
    reasons_new = reasons_new or {}
    units       = units or {}
    rows = _sync_issues_reason_rows(reasons, reasons_new, stage_9, newly_marked)
    for row in rows:
        bucket = units.get(row['reason']) or []
        row['units'] = bucket[:SYNC_ISSUES_MAX_UNITS_PER_REASON]
        row['unitsTruncated'] = len(bucket) > SYNC_ISSUES_MAX_UNITS_PER_REASON
    return {
        'buildingId':   str(sync.get('BUILDING_ID') or ''),
        'buildingName': sync.get('BUILDING_NAME') or '',
        'orgName':      sync.get('ORG_NAME') or '',
        'integration':  integration,
        'snapshot':     snapshot,
        'status':       'skipped' if skip_reason else 'ok',
        'skipReason':   skip_reason,
        # Some Snowflake candidates cannot be verified as sync issues from
        # MITS alone.  In particular, without a pre-sync snapshot there is no
        # evidence that the analysed sync newly caused the unavailable state.
        'excludedFromIssues': bool(excluded_from_issues),
        'unavailableUnits':  stage_9,
        'newlyMarkedUnits':  newly_marked,
        'preExistingUnits':  max(0, stage_9 - newly_marked),
        # The snapshot used as the pre-sync baseline; without one we cannot
        # tell newly-marked units from already-unavailable ones.
        'baselineSnapshot':  baseline_snapshot,
        'baselineAvailable': bool(baseline_available),
        'totalUnitsAnalyzed': analyzed,
        # What Snowflake believed the sync did, for side-by-side comparison.
        'reportedMarkedUnavailable': sync.get('UNITS_MARKED_UNAVAILABLE'),
        'reportedUnitsBeforeSync':   sync.get('TOTAL_UNITS_BEFORE_SYNC'),
        'reasons': rows,
    }


# ── Dynamic Pricing Cadence ──────────────────────────────────────────────────

_DYNAMIC_PRICING_COMMUNITIES_SQL = """\
WITH dynamic_pricing_flags AS (
    SELECT ID, ID_TYPE, VALUE
    FROM ELISE.FANSCAN_PUBLIC.CONVERSATION_FEATURE_FLAGS
    WHERE FEATURE_FLAG_NAME = 'leasing_dynamic_pricing'
        AND COALESCE(_FIVETRAN_DELETED, FALSE) = FALSE
)
SELECT
    b.ID AS BUILDING_ID,
    b.BUILDING_NAME,
    b.ORG_ID,
    b.ORG_NAME
FROM ELISE.DA.DIM_BUILDINGS AS b
LEFT JOIN dynamic_pricing_flags AS building_flag
    ON building_flag.ID_TYPE = 'building'
    AND TRY_TO_NUMBER(building_flag.ID) = b.ID
LEFT JOIN dynamic_pricing_flags AS org_flag
    ON org_flag.ID_TYPE = 'organization'
    AND TRY_TO_NUMBER(org_flag.ID) = b.ORG_ID
LEFT JOIN dynamic_pricing_flags AS default_flag
    ON default_flag.ID_TYPE = 'default'
WHERE COALESCE(
        building_flag.VALUE, org_flag.VALUE, default_flag.VALUE, FALSE) = TRUE
    AND b.IS_ACTIVE = TRUE
    AND COALESCE(b.IS_TEST, FALSE) = FALSE
    {search_filter}
    AND UPPER(COALESCE(
        b.PRICING_USED, b.PMS_USED_NAME, b.CRM_USED_NAME, '')) = 'ENTRATA'
ORDER BY b.ID
LIMIT {limit}
"""


def _dynamic_pricing_iso_date(value):
    """Return YYYY-MM-DD for one matrix date, or None when it is invalid."""
    text = str(value or '').strip()
    if not text:
        return None
    try:
        return date.fromisoformat(text[:10]).isoformat()
    except ValueError:
        for fmt in ('%m/%d/%Y', '%m/%d/%y'):
            try:
                return datetime.strptime(text, fmt).date().isoformat()
            except ValueError:
                continue
    return None


def _dynamic_pricing_signature(prices):
    """Comparable lease-term/rent signature for one availability date."""
    signature = []
    for price in prices:
        if not isinstance(price, dict):
            continue
        term = price.get('leaseTermLength')
        rent = price.get('rent')
        try:
            rent = float(rent)
        except (TypeError, ValueError):
            rent = str(rent or '')
        signature.append((str(term or ''), rent))
    return tuple(sorted(signature, key=lambda item: (item[0], str(item[1]))))


def _dynamic_pricing_unit_result(matrix, ordinal):
    """Extract dated prices and their actual contiguous signature ranges."""
    if not isinstance(matrix, dict):
        return None
    price_matrix = matrix.get('priceMatrix') or {}
    prices = price_matrix.get('prices') if isinstance(price_matrix, dict) else []
    if not isinstance(prices, list):
        prices = []

    by_date = {}
    for price in prices:
        if not isinstance(price, dict):
            continue
        day = _dynamic_pricing_iso_date(price.get('dateAvailable'))
        if day:
            by_date.setdefault(day, []).append(price)
    pricing_dates = sorted(by_date)
    if not pricing_dates:
        return None

    change_dates = []
    price_ranges = []
    previous_signature = None
    range_start = None
    previous_day = None
    for day in pricing_dates:
        signature = _dynamic_pricing_signature(by_date[day])
        is_calendar_contiguous = False
        if previous_day is not None:
            is_calendar_contiguous = (
                date.fromisoformat(day) - date.fromisoformat(previous_day)
            ).days == 1
        if (previous_signature is None
                or signature != previous_signature
                or not is_calendar_contiguous):
            change_dates.append(day)
            if range_start is not None:
                price_ranges.append({
                    'start': range_start,
                    'end': previous_day,
                })
            range_start = day
        previous_signature = signature
        previous_day = day
    if range_start is not None:
        price_ranges.append({'start': range_start, 'end': previous_day})
    _dynamic_pricing_add_range_lengths(price_ranges)

    observed_gaps = [
        (date.fromisoformat(current) - date.fromisoformat(previous_day)).days
        for previous_day, current in zip(change_dates, change_dates[1:])
    ]
    cadence_days = min(observed_gaps) if observed_gaps else None
    source_unit_id = matrix.get('unitId') or matrix.get('id')
    unit_id = (matrix.get('unitNumber') or matrix.get('apartmentName')
               or source_unit_id or f'Unit {ordinal}')
    return {
        'unitId': str(unit_id),
        'sourceUnitId': (
            str(source_unit_id) if source_unit_id not in (None, '') else None),
        'cadenceDays': cadence_days,
        'cadence': str(cadence_days) if cadence_days is not None else None,
        'cadencePattern': observed_gaps,
        'pricingDates': pricing_dates,
        'pricingDateCount': len(pricing_dates),
        # The retrieval input is a calendar-day hold, not the count of prices
        # Entrata happened to return. A temporarily unavailable unit can have
        # sparse pricing dates inside that requested window.
        'pricingWindowDayCount': (
            date.fromisoformat(pricing_dates[-1])
            - date.fromisoformat(pricing_dates[0])
        ).days + 1,
        'priceRanges': price_ranges,
        'priceRangeCount': len(price_ranges),
        'priceRangeLengths': [
            price_range.get('lengthDays') for price_range in price_ranges
        ],
        'observedChangeDates': change_dates,
        # Kept only while the server builds and verifies the retrieval plan;
        # removed before the result is sent to the browser.
        '_pricingSignatures': {
            day: _dynamic_pricing_signature(by_date[day])
            for day in pricing_dates
        },
    }


def _dynamic_pricing_add_range_lengths(ranges):
    """Add inclusive day counts for each actual price-signature range."""
    for price_range in ranges:
        try:
            start = date.fromisoformat(price_range['start'])
            end = date.fromisoformat(price_range['end'])
            price_range['lengthDays'] = (end - start).days + 1
        except (KeyError, TypeError, ValueError):
            price_range['lengthDays'] = None
    return ranges


def _dynamic_pricing_minimum_range_dates(units):
    """Return a minimum set of dates intersecting every unit pricing range.

    For intervals, greedily choosing the earliest uncovered range's end date
    is optimal: that point also covers every later-ending range containing it.
    """
    ranges = []
    for unit in units:
        for price_range in unit.get('priceRanges') or []:
            try:
                start = date.fromisoformat(price_range['start'])
                end = date.fromisoformat(price_range['end'])
            except (KeyError, TypeError, ValueError):
                continue
            ranges.append((end, start))
    ranges.sort()

    selected = []
    selected_day = None
    for end, start in ranges:
        if selected_day is None or not start <= selected_day <= end:
            selected_day = end
            selected.append(selected_day.isoformat())
    return selected


def _dynamic_pricing_cycle_range_units(units, cadence_days, shared_phase=None):
    """Partition each unit horizon into the cadence ranges to be sampled."""
    cycle_units = []
    for unit in units:
        unit['cycleEdgeInferenceGroups'] = []
        pricing_dates = unit.get('pricingDates') or []
        phase = shared_phase
        if phase is None:
            phase = unit.get('_cyclePhase')
        if phase is None and pricing_dates:
            # A unit with no visible price boundary has no observable phase.
            # Sampling cadence-sized slices from its first returned date still
            # guarantees that its whole horizon is checked.
            phase = date.fromisoformat(pricing_dates[0]).toordinal() % cadence_days
            unit['_cyclePhase'] = phase

        groups = []
        current_key = None
        current_dates = []
        for day in pricing_dates:
            parsed = date.fromisoformat(day)
            cycle_key = (parsed.toordinal() - phase) // cadence_days
            if current_key is not None and cycle_key != current_key:
                groups.append(current_dates)
                current_dates = []
            current_key = cycle_key
            current_dates.append(day)
        if current_dates:
            groups.append(current_dates)

        # A horizon may begin or end in the middle of a cadence range. If
        # that clipped edge has the same effective price as its neighboring
        # range, it does not need its own near-duplicate API call. Fold it
        # into the neighbor before enforcing cadence spacing.
        signatures = unit.get('_pricingSignatures') or {}

        def same_effective_price(left, right):
            values = {
                signatures.get(day) for day in (left + right)
            }
            return len(values) == 1

        if (len(groups) > 1 and len(groups[0]) < cadence_days
                and same_effective_price(groups[0], groups[1])):
            groups[1] = groups[0] + groups[1]
            unit['cycleEdgeInferenceGroups'].append(list(groups[1]))
            groups.pop(0)
        if (len(groups) > 1 and len(groups[-1]) < cadence_days
                and same_effective_price(groups[-2], groups[-1])):
            groups[-2] = groups[-2] + groups[-1]
            unit['cycleEdgeInferenceGroups'].append(list(groups[-2]))
            groups.pop()
        cycle_units.append({
            'priceRanges': [
                {'start': days[0], 'end': days[-1]}
                for days in groups if days
            ],
            '_cycleDateGroups': groups,
            '_pricingSignatures': signatures,
        })
    return cycle_units


def _dynamic_pricing_cadence_spaced_range_dates(units, cadence_days):
    """Return a range cover whose calls are at least one cadence apart.

    Once cadence and unit phase are known, one response anywhere inside each
    cadence range fills that entire range. This dynamic program picks the
    fewest property dates that intersect every required range while enforcing
    cadence-sized spacing between consecutive calls. It avoids the redundant
    per-unit anchor grids that previously produced calls such as 10/27 and
    10/29 for a three-day cadence.

    A strict spacing solution can be impossible when two different units have
    non-overlapping, truncated edge ranges less than one cadence apart.  In
    that genuine edge case, retain the unconstrained exact interval cover
    rather than claim that an incomplete matrix is accurate.
    """
    if not isinstance(cadence_days, int) or cadence_days <= 0:
        return _dynamic_pricing_minimum_range_dates(units), False

    intervals = []
    for unit in units:
        for price_range in unit.get('priceRanges') or []:
            try:
                start = date.fromisoformat(price_range['start']).toordinal()
                end = date.fromisoformat(price_range['end']).toordinal()
            except (KeyError, TypeError, ValueError):
                continue
            if start <= end:
                intervals.append((start, end))
    if not intervals:
        return [], True
    intervals.sort(key=lambda interval: (interval[1], interval[0]))

    # Given the last selected point, every interval beginning on or before it
    # is already covered. The earliest-ending remaining interval constrains
    # the next point; exploring the dates inside only that interval is enough
    # to find the globally smallest feasible sequence.
    memo = {}

    def solve(last_selected):
        if last_selected in memo:
            return memo[last_selected]
        remaining = [
            interval for interval in intervals if interval[0] > last_selected
        ]
        if not remaining:
            memo[last_selected] = ()
            return ()
        start, end = min(remaining, key=lambda interval: interval[1])
        lower = max(start, last_selected + cadence_days)
        best = None
        for candidate in range(lower, end + 1):
            tail = solve(candidate)
            if tail is None:
                continue
            proposed = (candidate,) + tail
            if (best is None or len(proposed) < len(best)
                    or (len(proposed) == len(best) and proposed > best)):
                # On equal call counts, later dates cover more future ranges.
                best = proposed
        memo[last_selected] = best
        return best

    first_start, first_end = min(intervals, key=lambda interval: interval[1])
    best = None
    for first_call in range(first_start, first_end + 1):
        tail = solve(first_call)
        if tail is None:
            continue
        proposed = (first_call,) + tail
        if (best is None or len(proposed) < len(best)
                or (len(proposed) == len(best) and proposed > best)):
            best = proposed
    if best is None:
        return _dynamic_pricing_minimum_range_dates(units), False
    return [date.fromordinal(day).isoformat() for day in best], True


def _dynamic_pricing_range_plan_accuracy(units, calls):
    """Measure reconstruction when each hit cadence range uses its response."""
    call_set = set(calls)
    total = correct = 0
    for unit in units:
        signatures = unit.get('_pricingSignatures') or {}
        for days in unit.get('_cycleDateGroups') or []:
            selected = next((day for day in days if day in call_set), None)
            inferred = signatures.get(selected) if selected else None
            total += len(days)
            correct += sum(signatures.get(day) == inferred for day in days)
    return round(100 * correct / total, 3) if total else 0.0


def _dynamic_pricing_adaptive_retrieval_dates(units, cadence_days):
    """Simulate an exact, phase-agnostic retrieval once cadence is known.

    A cadence-sized gap contains at most one effective price boundary for a
    unit.  We therefore query each unit's first day, cadence-spaced anchors,
    and final day. Equal signatures at adjacent anchors prove every day
    between them has the same effective price. When they differ, query the
    date that bisects the most unresolved unit intervals; every property-date
    call answers all units, so one probe can advance many binary searches.

    This is the safe bootstrap plan. Once actual unit ranges have been
    learned, ``_dynamic_pricing_minimum_range_dates`` is the lower-call
    steady-state plan. Hidden cycle boundaries whose adjacent prices happen
    to be equal do not affect matrix reconstruction and need no extra call.
    """
    if not isinstance(cadence_days, int) or cadence_days <= 0:
        dates = sorted({
            day for unit in units for day in (unit.get('pricingDates') or [])
        })
        return dates, 100.0 if dates else 0.0

    base_calls = set()
    for unit in units:
        pricing_dates = unit.get('pricingDates') or []
        if not pricing_dates:
            continue
        start = date.fromisoformat(pricing_dates[0])
        end = date.fromisoformat(pricing_dates[-1])
        cursor = start
        while cursor <= end:
            base_calls.add(cursor.isoformat())
            cursor += timedelta(days=cadence_days)
        base_calls.add(end.isoformat())
    call_order = sorted(base_calls)
    calls = set(call_order)

    def unresolved_intervals():
        unresolved = []
        for unit_index, unit in enumerate(units):
            signatures = unit.get('_pricingSignatures') or {}
            known = [
                day for day in (unit.get('pricingDates') or [])
                if day in calls
            ]
            for lower, upper in zip(known, known[1:]):
                gap = (date.fromisoformat(upper)
                       - date.fromisoformat(lower)).days
                if (gap > 1
                        and signatures.get(lower) != signatures.get(upper)):
                    unresolved.append((unit_index, lower, upper))
        return unresolved

    while True:
        unresolved = unresolved_intervals()
        if not unresolved:
            break

        candidates = set()
        for unit_index, lower, upper in unresolved:
            candidates.update(
                day for day in (units[unit_index].get('pricingDates') or [])
                if lower < day < upper and day not in calls
            )

        # Prefer a call useful to the largest number of units. The balance
        # tiebreaker keeps each binary search shallow; the date tiebreaker is
        # deterministic for repeatable reports and CSV exports.
        best_date = None
        best_rank = None
        for candidate in candidates:
            candidate_day = date.fromisoformat(candidate)
            covered = 0
            balance = 0
            for unit_index, lower, upper in unresolved:
                lower_day = date.fromisoformat(lower)
                upper_day = date.fromisoformat(upper)
                signatures = units[unit_index].get('_pricingSignatures') or {}
                if (candidate in signatures
                        and lower_day < candidate_day < upper_day):
                    covered += 1
                    balance += min(
                        (candidate_day - lower_day).days,
                        (upper_day - candidate_day).days)
            rank = (covered, balance, candidate)
            if best_rank is None or rank > best_rank:
                best_rank = rank
                best_date = candidate
        if best_date is None:
            break
        calls.add(best_date)
        call_order.append(best_date)

    correct = 0
    total = 0
    for unit in units:
        pricing_dates = unit.get('pricingDates') or []
        signatures = unit.get('_pricingSignatures') or {}
        known = [day for day in pricing_dates if day in calls]
        positions = {day: index for index, day in enumerate(pricing_dates)}
        reconstructed = {day: signatures.get(day) for day in known}
        for lower, upper in zip(known, known[1:]):
            lower_signature = signatures.get(lower)
            upper_signature = signatures.get(upper)
            if lower_signature == upper_signature:
                for day in pricing_dates[positions[lower]:positions[upper] + 1]:
                    reconstructed[day] = lower_signature
        total += len(pricing_dates)
        correct += sum(
            reconstructed.get(day) == signatures.get(day)
            for day in pricing_dates
        )
    accuracy = round(100 * correct / total, 3) if total else 0.0
    return call_order, accuracy


def _dynamic_pricing_aligned_retrieval_dates(units, cadence_days, phase):
    """Return one shared cadence-grid plan for a community-aligned matrix.

    All unit cycle boundaries share ``phase`` (an ordinal modulo cadence), so
    each unit's horizon can be partitioned into the same calendar cycles. A
    minimum interval-stabbing pass then chooses property dates that cover all
    unit-cycle slices, including truncated first and last slices.
    """
    if not isinstance(cadence_days, int) or cadence_days <= 0:
        return [], 0.0

    cycle_units = []
    for unit in units:
        groups = []
        current_key = None
        current_dates = []
        for day in unit.get('pricingDates') or []:
            parsed = date.fromisoformat(day)
            cycle_key = (parsed.toordinal() - phase) // cadence_days
            if current_key is not None and cycle_key != current_key:
                groups.append(current_dates)
                current_dates = []
            current_key = cycle_key
            current_dates.append(day)
        if current_dates:
            groups.append(current_dates)
        cycle_units.append({
            'priceRanges': [
                {'start': days[0], 'end': days[-1]}
                for days in groups if days
            ],
            '_cycleDateGroups': groups,
            '_pricingSignatures': unit.get('_pricingSignatures') or {},
        })

    calls = _dynamic_pricing_minimum_range_dates(cycle_units)
    call_set = set(calls)
    total = 0
    correct = 0
    for unit in cycle_units:
        signatures = unit['_pricingSignatures']
        for days in unit['_cycleDateGroups']:
            selected = next((day for day in days if day in call_set), None)
            inferred = signatures.get(selected) if selected else None
            total += len(days)
            correct += sum(signatures.get(day) == inferred for day in days)
    accuracy = round(100 * correct / total, 3) if total else 0.0
    return calls, accuracy


def _dynamic_pricing_cycle_groups(unit, cadence_days, phase):
    """Return this unit's dated cadence groups for one proven phase."""
    groups = []
    current_key = None
    current_dates = []
    for day in unit.get('pricingDates') or []:
        parsed = date.fromisoformat(day)
        cycle_key = (parsed.toordinal() - phase) // cadence_days
        if current_key is not None and cycle_key != current_key:
            groups.append(current_dates)
            current_dates = []
        current_key = cycle_key
        current_dates.append(day)
    if current_dates:
        groups.append(current_dates)
    return groups


def _dynamic_pricing_phase_proof_call(unit, call_sequence, cadence_ready_at):
    """Return when adjacent queried dates first prove a unit boundary."""
    call_index = {day: index for index, day in enumerate(call_sequence, 1)}
    signatures = unit.get('_pricingSignatures') or {}
    proofs = []
    for previous, current in zip(
            unit.get('pricingDates') or [],
            (unit.get('pricingDates') or [])[1:]):
        if signatures.get(previous) == signatures.get(current):
            continue
        if previous in call_index and current in call_index:
            proofs.append(max(call_index[previous], call_index[current]))
    if not proofs:
        return None
    return max(min(proofs), cadence_ready_at or 0)


def _dynamic_pricing_verification_boundaries(units, cadence_days):
    """Choose two observed adjacent boundaries exactly one cadence apart."""
    candidates = []
    for unit_index, unit in enumerate(units):
        ranges = unit.get('priceRanges') or []
        for index in range(1, len(ranges) - 1):
            try:
                first = date.fromisoformat(ranges[index]['start'])
                second = date.fromisoformat(ranges[index + 1]['start'])
            except (KeyError, TypeError, ValueError):
                continue
            if (second - first).days != cadence_days:
                continue
            first_pricing = date.fromisoformat(unit['pricingDates'][0])
            candidates.append(((second - first_pricing).days,
                               second, unit_index, first, second))
    if not candidates:
        return None
    _span, _second, unit_index, first, second = min(candidates)
    return unit_index, first, second


def _dynamic_pricing_discovered_cadence(
        units, call_sequence, expected_cadence=None):
    """Return the earliest cadence proven by any unit in the responses so far.

    A price boundary is observable only when both adjacent dates were queried.
    Two observed boundaries for the same unit expose one complete cycle. The
    property-level caller benefits from every unit returned by each API call;
    discovery is therefore not limited to whichever unit started the search.
    """
    call_index = {day: index for index, day in enumerate(call_sequence, 1)}
    candidates = []
    for unit_index, unit in enumerate(units):
        signatures = unit.get('_pricingSignatures') or {}
        observed_boundaries = []
        dates = unit.get('pricingDates') or []
        for previous, current in zip(dates, dates[1:]):
            try:
                adjacent = (
                    date.fromisoformat(current) - date.fromisoformat(previous)
                ).days == 1
            except (TypeError, ValueError):
                adjacent = False
            if (not adjacent or previous not in call_index
                    or current not in call_index
                    or signatures.get(previous) == signatures.get(current)):
                continue
            observed_boundaries.append((current, max(
                call_index[previous], call_index[current])))
        for first, second in zip(
                observed_boundaries, observed_boundaries[1:]):
            cadence = (
                date.fromisoformat(second[0]) - date.fromisoformat(first[0])
            ).days
            if cadence <= 0:
                continue
            # During historical evaluation, ignore longer spans caused by an
            # unchanged price crossing a real cycle boundary. In production
            # the derived community cadence is the candidate being evaluated.
            if expected_cadence and cadence != expected_cadence:
                continue
            candidates.append({
                'call': max(first[1], second[1]),
                'cadenceDays': cadence,
                'unitIndex': unit_index,
                'firstBoundary': first[0],
                'secondBoundary': second[0],
            })
    return min(candidates, key=lambda item: (
        item['call'], item['secondBoundary'], item['unitIndex'])) if candidates else None


def _dynamic_pricing_causal_retrieval_plan(units, cadence_days, cadence_mode):
    """Build a plan whose visible conclusions follow only from prior calls.

    Unknown-cadence mode queries consecutive dates through two observed price
    boundaries. Known-cadence mode verifies the supplied cadence by querying
    both sides of two boundaries separated by that cadence. Trusted-cadence
    mode accepts the supplied cadence without verification. Unit phase is never
    considered known until two adjacent queried cells have different signatures.
    Once cadence and phase are proven, one call in each resulting cadence group
    is sufficient to fill that group.
    """
    all_pricing_dates = sorted({
        day for unit in units for day in (unit.get('pricingDates') or [])
    })
    if not all_pricing_dates:
        return {
            'calls': [], 'steps': [], 'accuracy': 0.0,
            'cadenceKnownAtCall': None, 'cadenceVerifiedAtCall': None,
            'phaseKnownAtCall': {}, 'strategy': 'No pricing dates',
        }

    call_sequence = []
    call_steps = []
    call_set = set()

    def add_call(day, stage, reason):
        day = day.isoformat() if isinstance(day, date) else str(day)
        if day not in all_pricing_dates or day in call_set:
            return False
        call_set.add(day)
        call_sequence.append(day)
        call_steps.append({'date': day, 'stage': stage, 'reason': reason})
        return True

    if not isinstance(cadence_days, int) or cadence_days <= 0:
        for day in all_pricing_dates:
            add_call(day, 'Daily fallback',
                     'Cadence is not reliable enough to infer unqueried dates.')
        return {
            'calls': call_sequence,
            'steps': call_steps,
            'accuracy': 100.0,
            'cadenceKnownAtCall': None,
            'cadenceVerifiedAtCall': None,
            'phaseKnownAtCall': {},
            'strategy': 'Daily fallback; cadence unresolved',
        }

    if cadence_mode == 'trusted':
        cadence_known_at = 0
        cadence_verified_at = None
        cadence_ready_at = 0
        strategy_prefix = 'Trust supplied cadence without verification'
    else:
        verification = _dynamic_pricing_verification_boundaries(
            units, cadence_days)
        if verification is None:
            for day in all_pricing_dates:
                add_call(day, 'Daily fallback',
                         'Two adjacent cadence boundaries could not be verified.')
            return {
                'calls': call_sequence,
                'steps': call_steps,
                'accuracy': 100.0,
                'cadenceKnownAtCall': None,
                'cadenceVerifiedAtCall': None,
                'phaseKnownAtCall': {},
                'strategy': 'Daily fallback; cadence could not be verified',
            }

        representative_index, first_boundary, second_boundary = verification
        representative = units[representative_index]
        representative_label = (
            representative.get('unitId') or 'representative unit')
        second_previous = second_boundary - timedelta(days=1)

    if cadence_mode == 'unknown':
        discovery_start = date.fromisoformat(representative['pricingDates'][0])
        cursor = discovery_start
        discovery = None
        while cursor <= second_boundary:
            added = add_call(
                cursor, 'Discover cadence',
                'Query the next property date; inspect every returned unit for '
                'two observed adjacent price boundaries.')
            if added:
                discovery = _dynamic_pricing_discovered_cadence(
                    units, call_sequence, cadence_days)
                if discovery:
                    evidence_unit = units[discovery['unitIndex']]
                    evidence_label = (
                        evidence_unit.get('unitId') or 'an observed unit')
                    call_steps[-1]['reason'] = (
                        f'Unit {evidence_label} now has observed boundaries on '
                        f"{discovery['firstBoundary']} and "
                        f"{discovery['secondBoundary']}; their "
                        f"{discovery['cadenceDays']}-day separation proves the "
                        'community cadence.')
                    break
            cursor += timedelta(days=1)
        cadence_known_at = discovery['call'] if discovery else len(call_sequence)
        cadence_verified_at = cadence_known_at
        strategy_prefix = 'Discover cadence from the earliest qualifying unit'
    elif cadence_mode == 'known':
        verification_start = date.fromisoformat(representative['pricingDates'][0])
        cursor = verification_start
        while cursor <= first_boundary:
            add_call(
                cursor, 'Verify known cadence',
                f'Query consecutive dates for unit {representative_label} '
                'until its first adjacent price change is observed.')
            cursor += timedelta(days=1)
        add_call(
            second_previous, 'Verify known cadence',
            f'Check the day before the boundary predicted by the known '
            f'{cadence_days}-day cadence.')
        add_call(
            second_boundary, 'Verify known cadence',
            f'Confirm the second boundary and verify the {cadence_days}-day cadence.')
        cadence_known_at = 0
        cadence_verified_at = len(call_sequence)
        strategy_prefix = 'Verify known cadence at two adjacent boundaries'

    cadence_ready_at = cadence_verified_at or 0

    def phase_proofs():
        return {
            index: _dynamic_pricing_phase_proof_call(
                unit, call_sequence, cadence_ready_at)
            for index, unit in enumerate(units)
        }

    proofs = phase_proofs()
    unresolved = {
        index for index, unit in enumerate(units)
        if len(unit.get('priceRanges') or []) > 1 and proofs.get(index) is None
    }

    # Pick adjacent-date probes that establish phase for as many unresolved
    # units as possible. A price difference across non-adjacent calls marks an
    # interval containing a boundary, but never establishes its exact date.
    while unresolved:
        candidates = {}
        for unit_index in unresolved:
            unit = units[unit_index]
            signatures = unit.get('_pricingSignatures') or {}
            dates = unit.get('pricingDates') or []
            for previous, current in zip(dates, dates[1:]):
                if signatures.get(previous) == signatures.get(current):
                    continue
                key = (previous, current)
                covered = set()
                for other_index in unresolved:
                    other_signatures = (
                        units[other_index].get('_pricingSignatures') or {})
                    if (previous in other_signatures and current in other_signatures
                            and other_signatures[previous]
                            != other_signatures[current]):
                        covered.add(other_index)
                candidates[key] = covered
        if not candidates:
            break
        (previous, current), covered = max(
            candidates.items(),
            key=lambda item: (
                len(item[1]),
                -sum(day not in call_set for day in item[0]),
                item[0][1]),
        )
        labels = ', '.join(str(units[index].get('unitId') or index)
                           for index in sorted(covered)[:3])
        suffix = ' and others' if len(covered) > 3 else ''
        reason = f'Query adjacent dates to establish cycle position for {labels}{suffix}.'
        add_call(previous, 'Locate unit cycles', reason)
        add_call(current, 'Locate unit cycles', reason)
        proofs = phase_proofs()
        unresolved = {
            index for index in unresolved if proofs.get(index) is None
        }

    # Every proven unit is partitioned only by its observed adjacent boundary.
    # Units without an observable boundary are retrieved daily; inventing a
    # phase for them would make the reconstruction look more certain than it is.
    target_ranges = []
    for unit_index, unit in enumerate(units):
        phase_known_at = proofs.get(unit_index)
        unit_phase = unit.get('_cyclePhase')
        if phase_known_at is None or unit_phase is None:
            for day in unit.get('pricingDates') or []:
                if day not in call_set:
                    target_ranges.append({'start': day, 'end': day})
            continue
        for days in _dynamic_pricing_cycle_groups(
                unit, cadence_days, unit_phase):
            if not any(day in call_set for day in days):
                target_ranges.append({'start': days[0], 'end': days[-1]})

    fill_dates = _dynamic_pricing_minimum_range_dates([
        {'priceRanges': target_ranges}
    ])
    for day in fill_dates:
        add_call(day, 'Fill matrix',
                 'Retrieve one value inside every proven unit-cycle group.')

    proofs = phase_proofs()
    total = correct = 0
    for unit_index, unit in enumerate(units):
        dates = unit.get('pricingDates') or []
        known = {day for day in dates if day in call_set}
        phase_known_at = proofs.get(unit_index)
        unit_phase = unit.get('_cyclePhase')
        if phase_known_at is not None and unit_phase is not None:
            for group in _dynamic_pricing_cycle_groups(
                    unit, cadence_days, unit_phase):
                if any(day in call_set for day in group):
                    known.update(group)
        total += len(dates)
        correct += len(known)
    accuracy = round(100 * correct / total, 3) if total else 0.0
    return {
        'calls': call_sequence,
        'steps': call_steps,
        'accuracy': accuracy,
        'cadenceKnownAtCall': cadence_known_at,
        'cadenceVerifiedAtCall': cadence_verified_at,
        'phaseKnownAtCall': proofs,
        'strategy': f'{strategy_prefix}; adjacent phase probes; cycle-range cover',
    }


def _dynamic_pricing_lower_bound_retrieval_plan(
        units, cadence_lower_bound, cadence_mode):
    """Cover observed price ranges when only a cadence lower bound is known.

    With no complete interior range, the exact cadence cannot be measured. The
    longest observed equal-price range is nevertheless a useful conservative
    lower bound. One response within each observed range is sufficient under
    that assumption; changing units first require an adjacent response pair so
    the boundary between their (necessarily edge) ranges is actually observed.
    """
    all_pricing_dates = sorted({
        day for unit in units for day in (unit.get('pricingDates') or [])
    })
    call_sequence = []
    call_steps = []
    call_set = set()

    def add_call(day, stage, reason):
        day = str(day)
        if day not in all_pricing_dates or day in call_set:
            return False
        call_set.add(day)
        call_sequence.append(day)
        call_steps.append({'date': day, 'stage': stage, 'reason': reason})
        return True

    phase_known_at = {
        index: 0
        for index, unit in enumerate(units)
        if len(unit.get('priceRanges') or []) <= 1
    }
    unresolved = {
        index for index, unit in enumerate(units)
        if len(unit.get('priceRanges') or []) > 1
    }

    # A property-date response applies to every active unit. Select adjacent
    # probes that expose boundaries for the greatest number of units at once.
    while unresolved:
        candidates = {}
        for unit_index in unresolved:
            unit = units[unit_index]
            signatures = unit.get('_pricingSignatures') or {}
            dates = unit.get('pricingDates') or []
            for previous, current in zip(dates, dates[1:]):
                if signatures.get(previous) == signatures.get(current):
                    continue
                key = (previous, current)
                covered = set()
                for other_index in unresolved:
                    other_signatures = (
                        units[other_index].get('_pricingSignatures') or {})
                    if (previous in other_signatures
                            and current in other_signatures
                            and other_signatures[previous]
                            != other_signatures[current]):
                        covered.add(other_index)
                candidates[key] = covered
        if not candidates:
            break
        (previous, current), covered = max(
            candidates.items(),
            key=lambda item: (
                len(item[1]),
                -sum(day not in call_set for day in item[0]),
                item[0][1]),
        )
        labels = ', '.join(str(units[index].get('unitId') or index)
                           for index in sorted(covered)[:3])
        suffix = ' and others' if len(covered) > 3 else ''
        reason = (
            f'Observe the adjacent price boundary for {labels}{suffix}; '
            f'the assumed cadence is at least {cadence_lower_bound} days.')
        add_call(previous, 'Locate price ranges', reason)
        add_call(current, 'Locate price ranges', reason)
        for index in tuple(unresolved):
            proof = _dynamic_pricing_phase_proof_call(
                units[index], call_sequence, 0)
            if proof is not None:
                phase_known_at[index] = proof
                unresolved.remove(index)

    target_ranges = []
    for unit_index, unit in enumerate(units):
        if unit_index not in phase_known_at:
            target_ranges.extend({
                'start': day, 'end': day
            } for day in (unit.get('pricingDates') or []) if day not in call_set)
            continue
        for price_range in unit.get('priceRanges') or []:
            if not any(
                    price_range['start'] <= day <= price_range['end']
                    for day in call_set):
                target_ranges.append({
                    'start': price_range['start'],
                    'end': price_range['end'],
                })

    for day in _dynamic_pricing_minimum_range_dates([
            {'priceRanges': target_ranges}]):
        add_call(
            day, 'Fill matrix',
            'Retrieve one value in each observed range covered by the cadence '
            'lower-bound assumption.')

    # Calls added while filling can also complete an adjacent boundary proof.
    for index, unit in enumerate(units):
        if len(unit.get('priceRanges') or []) <= 1:
            phase_known_at[index] = 0
            continue
        proof = _dynamic_pricing_phase_proof_call(unit, call_sequence, 0)
        if proof is not None:
            phase_known_at[index] = proof

    total = correct = 0
    for unit_index, unit in enumerate(units):
        dates = unit.get('pricingDates') or []
        known = {day for day in dates if day in call_set}
        if unit_index in phase_known_at:
            for price_range in unit.get('priceRanges') or []:
                range_days = [
                    day for day in dates
                    if price_range['start'] <= day <= price_range['end']
                ]
                if any(day in call_set for day in range_days):
                    known.update(range_days)
        total += len(dates)
        correct += len(known)

    if cadence_mode == 'trusted':
        strategy_prefix = 'Trust cadence lower bound without verification'
    elif cadence_mode == 'known':
        strategy_prefix = 'Use supplied cadence lower bound; exact verification unavailable'
    else:
        strategy_prefix = 'Infer cadence lower bound from observed price ranges'
    return {
        'calls': call_sequence,
        'steps': call_steps,
        'accuracy': round(100 * correct / total, 3) if total else 0.0,
        'cadenceKnownAtCall': 0,
        'cadenceVerifiedAtCall': None,
        'phaseKnownAtCall': phase_known_at,
        'strategy': f'{strategy_prefix}; observed-range cover',
    }


def _dynamic_pricing_observation_only_plan(
        units, supplied_cadence, cadence_mode, cadence_is_lower_bound=False,
        _seed_call_steps=None, _rejected_cadences=None,
        _cadence_invalidations=None, _cadence_candidate_rejections=None):
    """Simulate retrieval using only metadata and responses already returned.

    The scheduler can inspect each unit's initial pricing window (availability
    date plus hold time), the supplied cadence in known/trusted modes, and the
    signatures returned by prior property-date calls. Full-matrix signatures
    are read only inside ``query`` and during the final accuracy evaluation.
    """
    window_dates = [
        list(unit.get('_initialPricingDates') or []) for unit in units
    ]
    window_sets = [set(days) for days in window_dates]
    property_dates = sorted({day for days in window_dates for day in days})
    truth = [unit.get('_pricingSignatures') or {} for unit in units]
    # A property-date response includes every unit returned for that date, not
    # only units whose metadata-derived window currently contains the date.
    # Keep those raw responses separately so a delayed first pricing date can
    # move a unit's requested window forward without losing earlier calls.
    api_responses = [{} for _unit in units]
    observations = [{} for _unit in units]
    call_sequence = []
    call_steps = []
    call_index = {}
    adjusted_window_at_call = {}
    rejected_cadences = set(_rejected_cadences or [])
    cadence_invalidations = list(_cadence_invalidations or [])
    cadence_candidate_rejections = list(
        _cadence_candidate_rejections or [])

    def reconcile_delayed_pricing_windows():
        """Shift a unit window after observing its actual pricing start.

        ``unit_details`` can say that an already-available unit starts on the
        sync date even though Entrata omits it from pricing responses until a
        later move-in date. Two adjacent responses -- no price followed by a
        price -- prove that later start without consulting the matrix ahead of
        time. Preserve the requested hold length and extend the end date by the
        same amount.
        """
        changed = False
        for unit_index, days in enumerate(window_dates):
            if not days or unit_index in adjusted_window_at_call:
                continue
            responses = api_responses[unit_index]
            # Do not mistake a temporary no-price gap for a delayed pricing
            # start. The metadata-derived first day must itself have returned
            # no price before the window is allowed to move.
            if (days[0] not in responses
                    or responses.get(days[0]) is not None):
                continue
            priced_days = sorted(
                day for day, signature in responses.items()
                if signature is not None)
            if not priced_days:
                continue
            first_priced = priced_days[0]
            previous = (
                date.fromisoformat(first_priced) - timedelta(days=1)
            ).isoformat()
            if (first_priced <= days[0]
                    or previous not in responses
                    or responses.get(previous) is not None):
                continue

            start = date.fromisoformat(first_priced)
            shifted = [
                (start + timedelta(days=offset)).isoformat()
                for offset in range(len(days))
            ]
            window_dates[unit_index] = shifted
            window_sets[unit_index] = set(shifted)
            observations[unit_index] = {
                day: signature
                for day, signature in responses.items()
                if day in window_sets[unit_index]
            }
            adjusted_window_at_call[unit_index] = len(call_sequence)
            changed = True

        if changed:
            property_dates[:] = sorted({
                day for days in window_dates for day in days
            })
        return changed

    observed_boundaries_cache = {}
    observed_equal_span_cache = {}
    lower_bound_contradiction_cache = {}
    response_lower_bound_components_cache = {}

    def query(day, stage, reason):
        """Issue one simulated API call and reveal only that date's response."""
        if day not in property_dates or day in call_index:
            return False
        call_sequence.append(day)
        call_index[day] = len(call_sequence)
        call_steps.append({'date': day, 'stage': stage, 'reason': reason})
        for unit_index, days in enumerate(window_sets):
            signature = truth[unit_index].get(day)
            api_responses[unit_index][day] = signature
            if day in days:
                observations[unit_index][day] = signature
        # Every evidence cache is scoped to the responses available before
        # this property call. Invalidate once here instead of rescanning the
        # same units repeatedly for every inferred cell.
        observed_boundaries_cache.clear()
        observed_equal_span_cache.clear()
        lower_bound_contradiction_cache.clear()
        response_lower_bound_components_cache.clear()
        lower_bound_inference_cache.clear()
        reconcile_delayed_pricing_windows()
        refresh_no_future_endpoint_equalities()
        # A property-wide response can make a previously exhausted unit
        # actionable even when another unit selected the date.
        phase_probe_exhausted.clear()
        return True

    def observed_boundaries(unit_index):
        """Return exact boundaries supported by two adjacent responses."""
        cached = observed_boundaries_cache.get(unit_index)
        if cached is not None:
            return cached
        result = []
        days = window_dates[unit_index]
        observed = observations[unit_index]
        for previous, current in zip(days, days[1:]):
            if previous not in observed or current not in observed:
                continue
            previous_signature = observed[previous]
            current_signature = observed[current]
            if (previous_signature is None or current_signature is None
                    or previous_signature == current_signature):
                continue
            result.append({
                'date': current,
                'proofCall': max(call_index[previous], call_index[current]),
            })
        observed_boundaries_cache[unit_index] = result
        return result

    def observed_equal_span_consistent(unit_index, start_day, end_day):
        """Return whether responses support one equal-price inclusive span.

        Both endpoints must have been retrieved with the same price. Any
        retrieved interior date with another price invalidates the span. This
        prevents skipped short ranges from masquerading as one long cadence.
        """
        cache_key = (unit_index, start_day, end_day)
        cached = observed_equal_span_cache.get(cache_key)
        if cached is not None:
            return cached
        days = window_dates[unit_index]
        positions = {day: index for index, day in enumerate(days)}
        start = positions.get(start_day)
        end = positions.get(end_day)
        observed = observations[unit_index]
        if (start is None or end is None or end < start
                or start_day not in observed or end_day not in observed):
            observed_equal_span_cache[cache_key] = False
            return False
        signature = observed.get(start_day)
        if signature is None or observed.get(end_day) != signature:
            observed_equal_span_cache[cache_key] = False
            return False
        result = all(
            observed.get(day) == signature
            for day in days[start:end + 1]
            if day in observed)
        observed_equal_span_cache[cache_key] = result
        return result

    def future_availability_probe_days(unit_index, cadence_hint):
        """Return n+cadence-1/n+cadence for a future-available unit.

        The pair verifies the common Entrata pattern that the availability date
        is cycle day one. It is only a hypothesis until the two returned prices
        differ; a same-price response pair falls through to adaptive search.
        """
        if not cadence_hint:
            return []
        unit = units[unit_index]
        days = window_dates[unit_index]
        if (unit.get('availabilityTiming') != 'Future Available'
                or not days
                or unit.get('availableDate') != days[0]
                or cadence_hint >= len(days)):
            return []
        return [days[cadence_hint - 1], days[cadence_hint]]

    def is_future_cycle_start_candidate(unit_index):
        unit = units[unit_index]
        days = window_dates[unit_index]
        return bool(
            len(days) > 1
            and unit.get('availabilityTiming') == 'Future Available'
            and unit.get('availableDate') == days[0])

    endpoint_equal_at_call = {}
    supplied_response_lower_bound = (
        supplied_cadence
        if (cadence_mode == 'known' and cadence_is_lower_bound
            and supplied_cadence) else 0)
    equal_edge_range_cache = {'callCount': -1, 'ranges': []}

    def refresh_no_future_endpoint_equalities():
        """Accept equal whole-window endpoints when no future unit exists.

        Without a future-availability cycle-start candidate, discovery uses
        the documented lower-bound assumption: an unchanged retrieved window
        establishes cadence at least as long as that window.  Two property
        calls can establish this for every coextensive unit.
        """
        if (cadence_mode != 'unknown' or any(
                is_future_cycle_start_candidate(index)
                for index in range(len(units)))):
            return
        for unit_index, days in enumerate(window_dates):
            if len(days) < 2:
                continue
            observed = observations[unit_index]
            first_signature = observed.get(days[0])
            last_signature = observed.get(days[-1])
            if (days[0] in observed and days[-1] in observed
                    and first_signature is not None
                    and first_signature == last_signature):
                endpoint_equal_at_call[unit_index] = max(
                    call_index[days[0]], call_index[days[-1]])

    def observed_equal_edge_ranges():
        """Return response-proven equal ranges touching a unit-window edge.

        A response-proven adjacent boundary plus an equal response at the
        corresponding window edge establishes an observed edge range.  When
        no complete interior cycle fits in the hold, the analyzer's domain
        rule treats the longest such range as a cadence lower bound.  This is
        deliberately derived only from prior responses; the truth ranges are
        never consulted by the planner.
        """
        call_count = len(call_sequence)
        if equal_edge_range_cache['callCount'] == call_count:
            return equal_edge_range_cache['ranges']
        ranges = []
        for unit_index, days in enumerate(window_dates):
            if not days:
                continue
            positions = {day: index for index, day in enumerate(days)}
            observed = observations[unit_index]
            for boundary in observed_boundaries(unit_index):
                position = positions[boundary['date']]
                if position > 0:
                    start_day = days[0]
                    end_day = days[position - 1]
                    if observed_equal_span_consistent(
                            unit_index, start_day, end_day):
                        ranges.append({
                            'unitIndex': unit_index,
                            'start': start_day,
                            'end': end_day,
                            'length': position,
                            'signature': observed[start_day],
                            'proofCall': max(
                                boundary['proofCall'],
                                call_index[start_day],
                                call_index[end_day]),
                        })
                if position < len(days):
                    start_day = days[position]
                    end_day = days[-1]
                    if observed_equal_span_consistent(
                            unit_index, start_day, end_day):
                        ranges.append({
                            'unitIndex': unit_index,
                            'start': start_day,
                            'end': end_day,
                            'length': len(days) - position,
                            'signature': observed[start_day],
                            'proofCall': max(
                                boundary['proofCall'],
                                call_index[start_day],
                                call_index[end_day]),
                        })
        equal_edge_range_cache['callCount'] = call_count
        equal_edge_range_cache['ranges'] = ranges
        return ranges

    def shared_endpoint_lower_bound_evidence():
        """Return endpoint evidence safe to promote to the community level."""
        future_indexes = [
            index for index in endpoint_equal_at_call
            if is_future_cycle_start_candidate(index)
        ]
        if future_indexes:
            return [
                (index, endpoint_equal_at_call[index])
                for index in future_indexes
            ]
        eligible_indexes = [
            index for index, days in enumerate(window_dates)
            if len(days) > 1
        ]
        if eligible_indexes and all(
                index in endpoint_equal_at_call
                for index in eligible_indexes):
            return [
                (index, endpoint_equal_at_call[index])
                for index in eligible_indexes
            ]
        return []

    def lower_bound_response_contradiction(cadence_lower_bound, step=None):
        """Reject a lower bound when responses prove a closer next change.

        An equal edge range remains safe to infer directly, but its length is
        not a reusable cadence lower bound if a price observed within that
        many days of an exact boundary differs from the boundary-side price.
        This catches a long constant prefix followed by daily pricing without
        consulting any unqueried matrix cell.
        """
        cache_key = (cadence_lower_bound, step)
        if cache_key in lower_bound_contradiction_cache:
            return lower_bound_contradiction_cache[cache_key]
        if not cadence_lower_bound or cadence_lower_bound <= 1:
            lower_bound_contradiction_cache[cache_key] = False
            return False
        for unit_index, days in enumerate(window_dates):
            positions = {day: index for index, day in enumerate(days)}
            observed = observations[unit_index]
            visible = {
                day: signature for day, signature in observed.items()
                if step is None or call_index.get(day, step + 1) <= step
            }
            for boundary in observed_boundaries(unit_index):
                if step is not None and boundary['proofCall'] > step:
                    continue
                position = positions[boundary['date']]
                left_signature = visible.get(days[position - 1])
                right_signature = visible.get(days[position])
                for offset in range(
                        position + 1,
                        min(len(days), position + cadence_lower_bound)):
                    signature = visible.get(days[offset])
                    if (signature is not None
                            and right_signature is not None
                            and signature != right_signature):
                        lower_bound_contradiction_cache[cache_key] = True
                        return True
                for offset in range(
                        max(0, position - cadence_lower_bound + 1),
                        position - 1):
                    signature = visible.get(days[offset])
                    if (signature is not None
                            and left_signature is not None
                            and signature != left_signature):
                        lower_bound_contradiction_cache[cache_key] = True
                        return True
        lower_bound_contradiction_cache[cache_key] = False
        return False

    def response_lower_bound_components(step=None):
        """Return the strongest response lower bound known for each unit."""
        if step in response_lower_bound_components_cache:
            return response_lower_bound_components_cache[step]
        if cadence_mode != 'unknown' and not (
                cadence_mode == 'known' and cadence_is_lower_bound):
            response_lower_bound_components_cache[step] = {}
            return {}
        bounds = {}
        for index, proof_call in shared_endpoint_lower_bound_evidence():
            length = len(window_dates[index])
            if ((step is None or proof_call <= step)
                    and length not in rejected_cadences
                    and not lower_bound_response_contradiction(length, step)):
                bounds[index] = max(bounds.get(index, 0), length)
        for evidence in observed_equal_edge_ranges():
            if ((step is None or evidence['proofCall'] <= step)
                    and evidence['length'] not in rejected_cadences
                    and not lower_bound_response_contradiction(
                        evidence['length'], step)):
                index = evidence['unitIndex']
                bounds[index] = max(
                    bounds.get(index, 0), evidence['length'])
        response_lower_bound_components_cache[step] = bounds
        return bounds

    def current_response_cadence_lower_bound(unit_index=None):
        """Return a conservative community/target-unit cadence lower bound.

        The community-wide value is the minimum of the strongest bounds
        supported by participating units.  A static unit can therefore never
        promote its long hold into a larger bound for changing units.  A
        target unit may still use its own stronger response-backed bound.
        """
        components = response_lower_bound_components()
        community_bound = min(components.values()) if components else 0
        unit_bound = components.get(unit_index, 0)
        return max(
            supplied_response_lower_bound, community_bound, unit_bound)

    def cadence_lower_bound_at_call(step, unit_index=None):
        components = response_lower_bound_components(step)
        community_bound = min(components.values()) if components else 0
        unit_bound = components.get(unit_index, 0)
        return max(
            supplied_response_lower_bound, community_bound, unit_bound)

    lower_bound_inference_cache = {}

    def lower_bound_inference_evidence(unit_index):
        """Map inferred dates to their response-only signature and proof call."""
        cache_key = (
            unit_index, len(call_sequence), cadence_ready_at,
            effective_cadence, calendar_month_day)
        cached = lower_bound_inference_cache.get(cache_key)
        if cached is not None:
            return cached
        days = window_dates[unit_index]
        positions = {day: index for index, day in enumerate(days)}
        inferred = {}

        def bound_and_call(evidence_call):
            lower_bound = cadence_lower_bound_at_call(
                evidence_call, unit_index)
            if cadence_ready_at is not None and effective_cadence:
                # Endpoint equality is unit evidence, not proof that every
                # unit shares that long lower bound. Once an exact, smaller
                # property cadence is response-proven, recompute all bounded
                # inference on that safe cadence and do not display it before
                # the cadence proof existed.
                lower_bound = min(
                    lower_bound or effective_cadence, effective_cadence)
                return lower_bound, max(evidence_call, cadence_ready_at)
            if lower_bound:
                return lower_bound, evidence_call
            final_bound = current_response_cadence_lower_bound(unit_index)
            qualifying_calls = [
                proof_call
                for index, proof_call in shared_endpoint_lower_bound_evidence()
                if len(window_dates[index]) >= final_bound
            ] + [
                evidence['proofCall']
                for evidence in observed_equal_edge_ranges()
                if evidence['length'] >= final_bound
            ]
            if not final_bound or not qualifying_calls:
                return 0, evidence_call
            return final_bound, max(evidence_call, min(qualifying_calls))

        observed = observations[unit_index]
        observed_days = sorted(observed, key=positions.get)
        for edge_range in observed_equal_edge_ranges():
            if edge_range['unitIndex'] != unit_index:
                continue
            start = positions[edge_range['start']]
            end = positions[edge_range['end']]
            for day in days[start:end + 1]:
                inferred[day] = {
                    'call': edge_range['proofCall'],
                    'signature': edge_range['signature'],
                }
        if cadence_mode != 'unknown' and not (
                cadence_mode == 'known' and cadence_is_lower_bound):
            lower_bound_inference_cache[cache_key] = inferred
            return inferred
        # Compare every response-observed pair, not only pairs that remain
        # adjacent after all calls finish. A later property-wide response can
        # land inside an interval that was already proven equal and must not
        # erase that interval's earlier inference time in the visualizer.
        for left_offset, left_day in enumerate(observed_days):
            left = positions[left_day]
            if observed.get(left_day) is None:
                continue
            for right_day in observed_days[left_offset + 1:]:
                right = positions[right_day]
                evidence_call = max(
                    call_index[left_day], call_index[right_day])
                lower_bound, inference_call = bound_and_call(evidence_call)
                if not lower_bound or right - left > lower_bound:
                    continue
                if observed.get(left_day) != observed.get(right_day):
                    continue
                for day in days[left:right + 1]:
                    previous = inferred.get(day)
                    evidence = {
                        'call': inference_call,
                        'signature': observed.get(left_day),
                    }
                    if previous is None or inference_call < previous['call']:
                        inferred[day] = evidence

        for boundary in observed_boundaries(unit_index):
            boundary_call = boundary['proofCall']
            lower_bound, boundary_call = bound_and_call(boundary_call)
            if not lower_bound:
                continue
            position = positions[boundary['date']]
            start = max(0, position - lower_bound)
            end = min(len(days), position + lower_bound)
            left_signature = observed.get(days[position - 1])
            right_signature = observed.get(days[position])
            for offset, day in enumerate(days[start:end], start):
                previous = inferred.get(day)
                evidence = {
                    'call': boundary_call,
                    'signature': (left_signature if offset < position
                                  else right_signature),
                }
                if previous is None or boundary_call < previous['call']:
                    inferred[day] = evidence
        lower_bound_inference_cache[cache_key] = inferred
        return inferred

    def lower_bound_inference_calls(unit_index):
        return {
            day: evidence['call']
            for day, evidence in lower_bound_inference_evidence(
                unit_index).items()
        }

    def future_discovery_candidate(unit_index):
        """Derive cadence from response-observed future-unit boundaries.

        The availability date is treated as cycle day one. Two boundaries are
        normally required. If the first boundary is at least halfway through
        the hold, a second cannot fit; the one-boundary result is accepted only
        when the observed post-boundary tail retains one price.
        """
        if not is_future_cycle_start_candidate(unit_index):
            return None
        days = window_dates[unit_index]
        boundaries = observed_boundaries(unit_index)
        if not boundaries:
            return None
        positions = {day: index for index, day in enumerate(days)}
        first = boundaries[0]
        first_offset = positions[first['date']]
        response_lower_bound = current_response_cadence_lower_bound(
            unit_index)
        if first_offset <= 0:
            return None
        if len(boundaries) >= 2:
            for first_boundary, second in zip(
                    boundaries, boundaries[1:]):
                gap = (
                    positions[second['date']]
                    - positions[first_boundary['date']])
                if gap in rejected_cadences:
                    continue
                second_previous = days[positions[second['date']] - 1]
                if (gap <= 0 or not observed_equal_span_consistent(
                        unit_index, first_boundary['date'],
                        second_previous)):
                    continue
                candidate = {
                    'cadenceDays': gap,
                    'unitIndex': unit_index,
                    'firstBoundary': first_boundary['date'],
                    'secondBoundary': second['date'],
                    'proofCall': max(
                        first_boundary['proofCall'], second['proofCall']),
                    'singleBoundaryAssumption': False,
                    'ready': True,
                }
                # Equal day-of-month boundaries 28-31 days apart may be a
                # calendar-month schedule rather than one fixed day count.
                # Verify the next monthly edge once for the whole property;
                # do not repeat this check for every unit.
                first_date = date.fromisoformat(first_boundary['date'])
                second_date = date.fromisoformat(second['date'])
                if (28 <= gap <= 31
                        and first_date.day == second_date.day):
                    next_month = 1 if second_date.month == 12 else (
                        second_date.month + 1)
                    next_year = (second_date.year + 1
                                 if second_date.month == 12
                                 else second_date.year)
                    following_month = 1 if next_month == 12 else next_month + 1
                    following_year = (next_year + 1
                                      if next_month == 12 else next_year)
                    month_end = (
                        date(following_year, following_month, 1)
                        - timedelta(days=1)).day
                    projected = date(
                        next_year, next_month,
                        min(second_date.day, month_end))
                    previous = projected - timedelta(days=1)
                    probe_days = [
                        day.isoformat() for day in (previous, projected)
                        if day.isoformat() in window_sets[unit_index]
                    ]
                    if (len(probe_days) == 2 and any(
                            day not in observations[unit_index]
                            for day in probe_days)):
                        candidate['calendarProbeDays'] = probe_days
                        candidate['ready'] = False
                return candidate
        single_boundary_ready = (
            first_offset >= response_lower_bound
            and 2 * first_offset >= len(days)
            and observed_equal_span_consistent(
                unit_index, first['date'], days[-1]))
        return {
            'cadenceDays': first_offset,
            'unitIndex': unit_index,
            'firstBoundary': first['date'],
            'secondBoundary': None,
            'proofCall': first['proofCall'],
            'singleBoundaryAssumption': single_boundary_ready,
            'ready': single_boundary_ready,
        }

    def next_future_discovery_probe(unit_index):
        """Compare endpoints, then bisect to the first future-unit boundary."""
        if not is_future_cycle_start_candidate(unit_index):
            return None
        days = window_dates[unit_index]
        observed = observations[unit_index]
        if days[0] not in observed:
            return days[0]
        if days[-1] not in observed:
            return days[-1]
        first_signature = observed.get(days[0])
        last_signature = observed.get(days[-1])
        if (first_signature is not None
                and first_signature == last_signature):
            endpoint_equal_at_call[unit_index] = max(
                call_index[days[0]], call_index[days[-1]])
            return None

        # Under the future-availability hypothesis, cycle one begins at index
        # zero. Maintain a same-as-first / different-from-first bracket and
        # halve it until the first boundary is adjacent.
        low = 0
        high = len(days) - 1
        while high - low > 1:
            midpoint = (low + high) // 2
            midpoint_day = days[midpoint]
            if midpoint_day not in observed:
                return midpoint_day
            if observed.get(midpoint_day) == first_signature:
                low = midpoint
            else:
                high = midpoint
        return None

    def next_candidate_boundary_confirmation_probe(unit_index, candidate):
        """Confirm a future unit's next projected boundary in one call.

        Discovery's first exact boundary supplies a provisional cadence from
        the availability-date hypothesis. If its next projected boundary is
        already observed, query the preceding day directly instead of
        bisecting the whole differing-price interval.
        """
        if not candidate or candidate.get('secondBoundary'):
            return None
        try:
            projected = (
                date.fromisoformat(candidate['firstBoundary'])
                + timedelta(days=candidate['cadenceDays']))
        except (KeyError, TypeError, ValueError):
            return None
        previous = (projected - timedelta(days=1)).isoformat()
        projected_day = projected.isoformat()
        if not all(
                day in window_sets[unit_index]
                for day in (previous, projected_day)):
            return None
        observed = observations[unit_index]
        if projected_day in observed and previous not in observed:
            return previous
        if previous in observed and projected_day not in observed:
            return projected_day
        return None

    def next_boundary_probe(unit_index, cadence_hint=None):
        """Choose the next response-only probe for one unit via interval search.

        With a cadence hypothesis, sample matching cycle positions one cadence
        apart. A differing pair is bisected before the hypothesis is accepted,
        allowing a hidden shorter cadence to replace it. Once one boundary is
        observed, probe the two cells around its predicted neighbor to verify
        the cadence directly. Without a cadence hypothesis, split the largest
        unresolved interval; equal distant endpoints can still conceal multiple
        changes in that mode.
        """
        days = window_dates[unit_index]
        if not days:
            return None
        observed = observations[unit_index]
        unobserved = [day for day in days if day not in observed]
        if not unobserved:
            return None
        positions = {day: index for index, day in enumerate(days)}
        observed_days = sorted(observed, key=positions.get)

        # Future availability is usually cycle day one. Test that hypothesis
        # with the two adjacent responses surrounding its first projected
        # boundary. When confirmed, those same calls populate the first and
        # second price ranges, so phase discovery adds no throwaway calls.
        for probe_day in future_availability_probe_days(
                unit_index, cadence_hint):
            if probe_day not in observed:
                return probe_day

        if not observed_days:
            return days[0]
        if cadence_hint:
            # A missing response followed later by a real price is an
            # availability-window edge, not a pricing-cycle boundary. Bisect
            # it so the active hold window can be shifted to the first date
            # Entrata actually returns for the unit.
            availability_brackets = []
            for left_day, right_day in zip(observed_days, observed_days[1:]):
                left = positions[left_day]
                right = positions[right_day]
                if right - left <= 1:
                    continue
                if ((observed[left_day] is None)
                        != (observed[right_day] is None)):
                    availability_brackets.append((
                        right - left, days[(left + right) // 2]))
            if availability_brackets:
                return min(availability_brackets)[1]

            # Resolve a response-proven internal change before attempting to
            # confirm the cadence-shifted neighbor of an observed boundary.
            # Otherwise a unit with a long constant prefix followed by daily
            # changes can make two non-consecutive boundaries look one long
            # cadence apart (for example, building 6702).
            differing_brackets = []
            for left_day, right_day in zip(observed_days, observed_days[1:]):
                left = positions[left_day]
                right = positions[right_day]
                if not (1 < right - left <= cadence_hint):
                    continue
                if (observed[left_day] is not None
                        and observed[right_day] is not None
                        and observed[left_day] != observed[right_day]):
                    differing_brackets.append((
                        right - left, days[(left + right) // 2]))
            if differing_brackets:
                return min(differing_brackets)[1]

            # One exact boundary plus its cadence-shifted neighbor is the
            # shortest proof of the supplied cadence.
            for boundary in observed_boundaries(unit_index):
                boundary_position = positions[boundary['date']]
                for expected_position in (
                        boundary_position + cadence_hint,
                        boundary_position - cadence_hint):
                    if not (1 <= expected_position < len(days)):
                        continue
                    for position in (expected_position - 1, expected_position):
                        if days[position] not in observed:
                            return days[position]

            # Probe the same relative position in consecutive cycles. Equal
            # endpoints prove the whole <= cadence interval has one price;
            # differing endpoints create the binary-search bracket above.
            anchor_positions = list(range(0, len(days), cadence_hint))
            if anchor_positions[-1] != len(days) - 1:
                anchor_positions.append(len(days) - 1)
            for position in anchor_positions:
                if days[position] not in observed:
                    return days[position]
            return None

        if len(observed_days) == 1:
            return days[-1] if days[-1] not in observed else days[0]

        differing_brackets = []
        availability_brackets = []
        unresolved_intervals = []
        for left_day, right_day in zip(observed_days, observed_days[1:]):
            left = positions[left_day]
            right = positions[right_day]
            if right - left <= 1:
                continue
            midpoint = days[(left + right) // 2]
            if ((observed[left_day] is None)
                    != (observed[right_day] is None)):
                availability_brackets.append((right - left, midpoint))
            elif (observed[left_day] is not None
                    and observed[right_day] is not None
                    and observed[left_day] != observed[right_day]):
                differing_brackets.append((right - left, midpoint))
            else:
                unresolved_intervals.append((right - left, midpoint))
        if availability_brackets:
            return min(availability_brackets)[1]
        if differing_brackets:
            return min(differing_brackets)[1]

        first_position = positions[observed_days[0]]
        last_position = positions[observed_days[-1]]
        if first_position > 0:
            unresolved_intervals.append((first_position, days[0]))
        if last_position < len(days) - 1:
            unresolved_intervals.append((
                len(days) - 1 - last_position, days[-1]))
        if not unresolved_intervals:
            return unobserved[0]
        return max(unresolved_intervals, key=lambda item: (
            item[0], item[1]))[1]

    def has_unresolved_availability_bracket(unit_index):
        """Return whether calls bracket a delayed pricing start non-adjacently."""
        days = window_dates[unit_index]
        positions = {day: index for index, day in enumerate(days)}
        observed = observations[unit_index]
        observed_days = sorted(observed, key=positions.get)
        return any(
            positions[right] - positions[left] > 1
            and ((observed[left] is None) != (observed[right] is None))
            for left, right in zip(observed_days, observed_days[1:])
        )

    def future_availability_alignment_proof(unit_index, cadence_hint):
        """Return when n+cadence-1/n+cadence proves cycle-day-one.

        For a future-available unit, two distinct non-null prices on this
        adjacent pair prove the boundary and populate both adjoining ranges.
        A separate call on the availability date would add no information.
        """
        probe_days = future_availability_probe_days(
            unit_index, cadence_hint)
        if len(probe_days) != 2 or not all(
                day in observations[unit_index] for day in probe_days):
            return None
        left, right = probe_days
        left_signature = observations[unit_index].get(left)
        right_signature = observations[unit_index].get(right)
        if (left_signature is None or right_signature is None
                or left_signature == right_signature):
            return None
        return max(call_index[left], call_index[right])

    def pricing_window_start_resolved(unit_index):
        """Require response evidence for a future unit's active start date."""
        days = window_dates[unit_index]
        if not days:
            return True
        observed = observations[unit_index]
        if days[0] in observed and observed[days[0]] is not None:
            return True
        # The optimized future-unit boundary test proves that availability is
        # cycle day one and gives a checked price in its first range. Requiring
        # another response on the availability date merely rechecks a range
        # whose value is already inferable.
        if (effective_cadence
                and future_availability_alignment_proof(
                    unit_index, effective_cadence) is not None):
            return True
        # A fully queried no-price window is terminal; it cannot provide a
        # cadence candidate but should not block other units indefinitely.
        return all(day in observed and observed[day] is None for day in days)

    def future_pricing_start_probe_needed(unit_index):
        """Detect a rejected future-start shortcut that can hide an island.

        Ordinarily a future unit's availability date is safely covered by the
        cycle-day-one alignment proof. If the boundary probe instead returns
        no price immediately before a later price, the availability date can
        contain an isolated earlier price response. Query that metadata-known
        start once; do not add a start-date call for every ordinary future
        unit whose phase was learned incidentally from another property call.
        """
        days = window_dates[unit_index]
        if (not days or not effective_cadence
                or units[unit_index].get('availabilityTiming')
                != 'Future Available'):
            return False
        observed = observations[unit_index]
        if days[0] in observed:
            return False
        probe_window = days[:min(len(days), effective_cadence + 1)]
        return (any(
            day in observed and observed[day] is None
            for day in probe_window)
            and any(
                day in observed and observed[day] is not None
                for day in probe_window))

    def cadence_candidates(required_cadence=None):
        candidates = []
        for unit_index in range(len(units)):
            boundaries = observed_boundaries(unit_index)
            positions = {
                day: index
                for index, day in enumerate(window_dates[unit_index])
            }
            for first, second in zip(boundaries, boundaries[1:]):
                gap = (
                    date.fromisoformat(second['date'])
                    - date.fromisoformat(first['date'])
                ).days
                second_previous = window_dates[unit_index][
                    positions[second['date']] - 1]
                if gap <= 0 or (
                        required_cadence is not None
                        and gap != required_cadence):
                    continue
                if not observed_equal_span_consistent(
                        unit_index, first['date'], second_previous):
                    continue
                candidates.append({
                    'cadenceDays': gap,
                    'unitIndex': unit_index,
                    'firstBoundary': first['date'],
                    'secondBoundary': second['date'],
                    'proofCall': max(first['proofCall'], second['proofCall']),
                })
        return sorted(candidates, key=lambda item: (
            item['proofCall'], item['cadenceDays'], item['secondBoundary'],
            item['unitIndex']))

    def cadence_response_contradiction(cadence_hint):
        """Disprove a cadence using only prices from normal property calls.

        Each chronologically adjacent pair of returned, distinct prices proves
        that at least one boundary lies inside that date interval. A valid
        cadence must have some unit-specific phase whose projected boundaries
        intersect every such interval. If no phase can do so, the cadence is
        impossible for that unit. No cadence-only call is needed.
        """
        if not isinstance(cadence_hint, int) or cadence_hint <= 0:
            return None
        all_phases = set(range(cadence_hint))
        for unit_index, days in enumerate(window_dates):
            positions = {day: index for index, day in enumerate(days)}
            observed = observations[unit_index]
            observed_days = sorted(
                (day for day, signature in observed.items()
                 if day in positions and signature is not None),
                key=positions.get)
            possible_phases = set(all_phases)
            evidence_calls = []
            for left_day, right_day in zip(
                    observed_days, observed_days[1:]):
                if observed[left_day] == observed[right_day]:
                    continue
                left = positions[left_day]
                right = positions[right_day]
                interval_phases = {
                    date.fromisoformat(days[offset]).toordinal()
                    % cadence_hint
                    for offset in range(left + 1, right + 1)
                }
                possible_phases &= interval_phases
                evidence_calls.extend((
                    call_index[left_day], call_index[right_day]))
                if possible_phases:
                    continue
                label = units[unit_index].get('unitId') or unit_index
                return {
                    'unitIndex': unit_index,
                    'unitId': units[unit_index].get('unitId'),
                    'atCall': max(evidence_calls),
                    'reason': (
                        f'Returned price changes for unit {label} cannot all '
                        f'be placed on one {cadence_hint}-day phase.'),
                }
        return None

    def calendar_month_evidence():
        """Return three response-proven boundaries on one monthly edge."""
        candidates = []
        pairs_by_day = {}
        for unit_index in range(len(units)):
            boundaries = observed_boundaries(unit_index)
            for first_boundary, second_boundary in zip(
                    boundaries, boundaries[1:]):
                first_date = date.fromisoformat(first_boundary['date'])
                second_date = date.fromisoformat(second_boundary['date'])
                if first_date.day != second_date.day:
                    continue
                if (second_date.year * 12 + second_date.month
                        != first_date.year * 12 + first_date.month + 1):
                    continue
                gap = (second_date - first_date).days
                if not 28 <= gap <= 31:
                    continue
                pairs_by_day.setdefault(first_date.day, []).append({
                    'unitIndex': unit_index,
                    'first': first_boundary,
                    'second': second_boundary,
                    'gap': gap,
                })
            for triple in zip(
                    boundaries, boundaries[1:], boundaries[2:]):
                parsed = [
                    date.fromisoformat(item['date']) for item in triple
                ]
                if len({item.day for item in parsed}) != 1:
                    continue
                month_indexes = [
                    item.year * 12 + item.month for item in parsed
                ]
                if not (month_indexes[1] == month_indexes[0] + 1
                        and month_indexes[2] == month_indexes[1] + 1):
                    continue
                gaps = [
                    (parsed[1] - parsed[0]).days,
                    (parsed[2] - parsed[1]).days,
                ]
                if not all(28 <= gap <= 31 for gap in gaps):
                    continue
                candidates.append({
                    'cadenceDays': min(gaps),
                    'calendarMonthDay': parsed[0].day,
                    'unitIndex': unit_index,
                    'firstBoundary': triple[0]['date'],
                    'secondBoundary': triple[1]['date'],
                    'thirdBoundary': triple[2]['date'],
                    'proofCall': max(
                        item['proofCall'] for item in triple),
                    'calendarMonth': True,
                    'ready': True,
                })
        if candidates:
            return min(candidates, key=lambda item: (
                item['proofCall'], item['unitIndex']))
        # A property call observes all units. Two independently proven monthly
        # boundary pairs on the same day-of-month provide the same property-
        # level evidence even when short unit holds prevent either unit from
        # containing three boundaries by itself.
        pair_candidates = []
        for month_day, pairs in pairs_by_day.items():
            distinct_pairs = {
                (item['first']['date'], item['second']['date']): item
                for item in pairs
            }
            pairs = list(distinct_pairs.values())
            if len(pairs) < 2:
                continue
            first_pair, second_pair = sorted(
                pairs, key=lambda item: (
                    max(item['first']['proofCall'],
                        item['second']['proofCall']),
                    item['unitIndex']))[:2]
            pair_candidates.append({
                'cadenceDays': min(
                    first_pair['gap'], second_pair['gap']),
                'calendarMonthDay': month_day,
                'unitIndex': first_pair['unitIndex'],
                'firstBoundary': first_pair['first']['date'],
                'secondBoundary': first_pair['second']['date'],
                'corroboratingUnitIndex': second_pair['unitIndex'],
                'proofCall': max(
                    first_pair['first']['proofCall'],
                    first_pair['second']['proofCall'],
                    second_pair['first']['proofCall'],
                    second_pair['second']['proofCall']),
                'calendarMonth': True,
                'crossUnitEvidence': True,
                'ready': True,
            })
        return min(pair_candidates, key=lambda item: (
            item['proofCall'], item['unitIndex'])) if pair_candidates else None

    def calendar_month_probe_days(candidate):
        """Return one adjacent pair at the next same-day monthly edge."""
        if not candidate:
            return []
        try:
            first = date.fromisoformat(candidate['firstBoundary'])
            second = date.fromisoformat(candidate['secondBoundary'])
        except (KeyError, TypeError, ValueError):
            return []
        gap = (second - first).days
        if not (28 <= gap <= 31 and first.day == second.day):
            return []
        next_month = 1 if second.month == 12 else second.month + 1
        next_year = second.year + 1 if second.month == 12 else second.year
        following_month = 1 if next_month == 12 else next_month + 1
        following_year = next_year + 1 if next_month == 12 else next_year
        month_end = (
            date(following_year, following_month, 1)
            - timedelta(days=1)).day
        projected = date(
            next_year, next_month, min(second.day, month_end))
        previous = projected - timedelta(days=1)
        return [
            day.isoformat() for day in (previous, projected)
            if day.isoformat() in property_dates
        ]

    def calendar_month_response_contradiction():
        """Disprove any unit-specific calendar-day monthly model."""
        for unit_index, days in enumerate(window_dates):
            positions = {day: index for index, day in enumerate(days)}
            observed = observations[unit_index]
            observed_days = sorted(
                (day for day, signature in observed.items()
                 if day in positions and signature is not None),
                key=positions.get)
            possible_month_days = set(range(1, 32))
            evidence_calls = []
            for left_day, right_day in zip(
                    observed_days, observed_days[1:]):
                if observed[left_day] == observed[right_day]:
                    continue
                left = positions[left_day]
                right = positions[right_day]
                possible_month_days &= {
                    date.fromisoformat(days[offset]).day
                    for offset in range(left + 1, right + 1)
                }
                evidence_calls.extend((
                    call_index[left_day], call_index[right_day]))
                if possible_month_days:
                    continue
                label = units[unit_index].get('unitId') or unit_index
                return {
                    'unitIndex': unit_index,
                    'unitId': units[unit_index].get('unitId'),
                    'atCall': max(evidence_calls),
                    'reason': (
                        f'Returned price changes for unit {label} cannot all '
                        'be placed on one calendar day-of-month phase.'),
                }
        return None

    def equal_interval_dates(unit_index, cadence_hint):
        """Dates proven equal by response pairs no farther than one cadence."""
        return set(equal_interval_values(unit_index, cadence_hint))

    def equal_interval_values(unit_index, cadence_hint):
        """Map dates to the signature proven by nearby equal responses."""
        if not cadence_hint:
            return {}
        days = window_dates[unit_index]
        observed = observations[unit_index]
        positions = {day: index for index, day in enumerate(days)}
        observed_days = sorted(observed, key=positions.get)
        covered = {}
        for left_day, right_day in zip(observed_days, observed_days[1:]):
            left = positions[left_day]
            right = positions[right_day]
            if right - left > cadence_hint:
                continue
            left_signature = observed[left_day]
            right_signature = observed[right_day]
            if (left_signature is None or right_signature is None
                    or left_signature != right_signature):
                continue
            for day in days[left:right + 1]:
                covered[day] = left_signature
        return covered

    def endpoint_inferred_dates(unit_index):
        return (set(window_dates[unit_index])
                if unit_index in endpoint_equal_at_call else set())

    def largest_observed_equal_range():
        largest = 0
        for unit_index, days in enumerate(window_dates):
            observed = observations[unit_index]
            current_signature = object()
            current_length = 0
            for day in days:
                if day not in observed or observed[day] is None:
                    current_signature = object()
                    current_length = 0
                    continue
                if observed[day] == current_signature:
                    current_length += 1
                else:
                    current_signature = observed[day]
                    current_length = 1
                largest = max(largest, current_length)
        return largest

    effective_cadence = (
        supplied_cadence if cadence_mode in ('known', 'trusted') else None)
    cadence_known_at = 0 if effective_cadence else None
    cadence_verified_at = None
    cadence_evidence = None
    cadence_ready_at = 0 if cadence_mode == 'trusted' else None
    phase_known_at = {}
    unit_phases = {}
    boundary_not_required = set()
    phase_probe_exhausted = set()
    discovery_is_lower_bound = False
    future_discovery_exhausted = set()
    calendar_month_day = None

    def response_derived_groups(days, cadence_days, phase):
        if calendar_month_day is None:
            return _dynamic_pricing_date_groups(
                days, cadence_days, phase)
        groups = []
        current_key = None
        current_dates = []
        for day in days:
            parsed = date.fromisoformat(day)
            month_index = parsed.year * 12 + parsed.month
            if parsed.day < phase:
                month_index -= 1
            if current_key is not None and month_index != current_key:
                groups.append(current_dates)
                current_dates = []
            current_key = month_index
            current_dates.append(day)
        if current_dates:
            groups.append(current_dates)
        return groups

    if cadence_mode == 'trusted' and effective_cadence:
        for unit_index, days in enumerate(window_dates):
            if (days and not cadence_is_lower_bound
                    and effective_cadence > len(days)):
                # The trusted domain assumption says a cadence longer than the
                # entire requested hold cannot introduce an interior boundary.
                # A reported lower bound is not an exact cadence and cannot
                # safely support that shortcut.
                boundary_not_required.add(unit_index)
                phase_known_at[unit_index] = 0
                unit_phases[unit_index] = (
                    date.fromisoformat(days[0]).toordinal()
                    % effective_cadence)

    def refresh_cadence():
        nonlocal effective_cadence, cadence_known_at
        nonlocal cadence_verified_at, cadence_evidence, cadence_ready_at
        nonlocal calendar_month_day
        if cadence_ready_at is not None:
            return
        if cadence_mode == 'known':
            candidates = cadence_candidates(supplied_cadence)
        else:
            monthly_evidence = calendar_month_evidence()
            monthly_contradiction = (
                calendar_month_response_contradiction()
                if monthly_evidence else None)
            if monthly_evidence and not monthly_contradiction:
                cadence_evidence = monthly_evidence
                effective_cadence = monthly_evidence['cadenceDays']
                calendar_month_day = monthly_evidence['calendarMonthDay']
                cadence_known_at = monthly_evidence['proofCall']
                cadence_verified_at = monthly_evidence['proofCall']
                cadence_ready_at = monthly_evidence['proofCall']
                return
            future_indexes = [
                unit_index for unit_index in range(len(units))
                if is_future_cycle_start_candidate(unit_index)
            ]
            future_candidates = [
                candidate for unit_index in future_indexes
                if (candidate := future_discovery_candidate(unit_index))
                and candidate['ready']
            ]
            future_candidates = [
                candidate for candidate in future_candidates
                if candidate.get('cadenceDays') not in rejected_cadences
            ]
            eligible_candidates = []
            for candidate in future_candidates:
                contradiction = cadence_response_contradiction(
                    candidate['cadenceDays'])
                if contradiction is None:
                    eligible_candidates.append(candidate)
                    continue
                rejected_cadences.add(candidate['cadenceDays'])
                rejection_key = (
                    candidate['cadenceDays'], contradiction['unitIndex'])
                if not any(
                        (item.get('cadenceDays'), item.get('unitIndex'))
                        == rejection_key
                        for item in cadence_candidate_rejections):
                    cadence_candidate_rejections.append({
                        'cadenceDays': candidate['cadenceDays'],
                        'atCall': max(
                            candidate['proofCall'],
                            contradiction['atCall']),
                        'unitIndex': contradiction['unitIndex'],
                        'unitId': contradiction['unitId'],
                        'reason': contradiction['reason'],
                    })
            future_candidates = eligible_candidates
            strong_candidates = [
                candidate for candidate in future_candidates
                if not candidate.get('singleBoundaryAssumption')
            ]
            future_scan_complete = bool(future_indexes) and all(
                pricing_window_start_resolved(unit_index)
                and
                not has_unresolved_availability_bracket(unit_index)
                and (
                    unit_index in endpoint_equal_at_call
                    or unit_index in future_discovery_exhausted
                    or any(candidate['unitIndex'] == unit_index
                           for candidate in future_candidates)
                )
                for unit_index in future_indexes)
            if strong_candidates:
                # Two adjacent response-proven boundaries establish an exact
                # cadence for this unit immediately. Accept it now; if a later
                # property-wide response exposes an incompatible shorter
                # cadence, the contradiction detector rejects it and restarts
                # discovery with every prior response preserved.
                chosen = min(strong_candidates, key=lambda item: (
                    item['cadenceDays'], item['proofCall'], item['unitIndex']))
                candidates = [chosen]
            elif future_candidates and future_scan_complete:
                # One-boundary candidates at least half a hold long are valid
                # assumptions, but first give every future unit a chance to
                # provide the stronger two-boundary proof.
                # Prefer the smallest response-supported candidate whenever
                # property-wide calls have exposed more than one.
                chosen = min(future_candidates, key=lambda item: (
                    item['cadenceDays'], item['proofCall'], item['unitIndex']))
                chosen = dict(chosen)
                chosen['proofCall'] = len(call_sequence)
                candidates = [chosen]
            elif not future_indexes:
                candidates = [
                    candidate for candidate in cadence_candidates()
                    if candidate.get('cadenceDays') not in rejected_cadences
                ]
            else:
                candidates = []
        if not candidates:
            return
        cadence_evidence = candidates[0]
        if cadence_mode == 'unknown':
            effective_cadence = cadence_evidence['cadenceDays']
            cadence_known_at = cadence_evidence['proofCall']
        cadence_verified_at = cadence_evidence['proofCall']
        cadence_ready_at = cadence_evidence['proofCall']

    def refresh_phases():
        if not effective_cadence or cadence_ready_at is None:
            return
        for unit_index in range(len(units)):
            if unit_index in unit_phases:
                continue
            if (unit_index in adjusted_window_at_call
                    and window_dates[unit_index]):
                # An adjacent no-price -> priced response proves the exact
                # start of a delayed unit pricing window. Once cadence is
                # accepted, that start is also the first cycle-group edge;
                # searching for the next price boundary would only re-prove
                # a range whose cells are already inferable.
                first_day = date.fromisoformat(window_dates[unit_index][0])
                unit_phases[unit_index] = (
                    first_day.day if calendar_month_day is not None
                    else first_day.toordinal() % effective_cadence)
                phase_known_at[unit_index] = max(
                    adjusted_window_at_call[unit_index], cadence_ready_at)
                continue
            boundaries = observed_boundaries(unit_index)
            if not boundaries:
                continue
            boundary = min(boundaries, key=lambda item: (
                item['proofCall'], item['date']))
            boundary_date = date.fromisoformat(boundary['date'])
            unit_phases[unit_index] = (
                boundary_date.day if calendar_month_day is not None
                else boundary_date.toordinal() % effective_cadence)
            phase_known_at[unit_index] = max(
                boundary['proofCall'], cadence_ready_at)

    # When a provisional cadence is invalidated, restart the state machine
    # with every prior response already known. Replaying these seed calls only
    # reconstructs causal state; query() de-duplicates them before any new API
    # call is selected.
    for seed_step in (_seed_call_steps or []):
        query(
            seed_step.get('date'),
            seed_step.get('stage') or 'Discover cadence',
            seed_step.get('reason') or 'Previously retrieved API response.')

    # Candidate scan blocks are ranked entirely from unit metadata. Discovery
    # begins with future-available units because their availability date is the
    # cycle-start hypothesis; it receives no cadence value as input.
    scan_blocks = []
    for unit_index, days in enumerate(window_dates):
        if not days:
            continue
        overlap_score = sum(
            len(window_sets[unit_index] & other_days)
            for other_days in window_sets
        )
        # Future-available units are the strongest phase candidates because
        # their retrieval window usually begins on cycle day one. Always scan
        # every such unit before an already-available unit, even when its hold
        # is too short for the usual n+cadence boundary probe. Property-level
        # responses may resolve the already-available units along the way.
        future_probe_priority = (
            0 if units[unit_index].get('availabilityTiming')
            == 'Future Available' else 1)
        priority_score = (
            -date.fromisoformat(days[0]).toordinal()
            if future_probe_priority == 0 else -overlap_score)
        scan_blocks.append((
            future_probe_priority, priority_score, days[0], -len(days),
            unit_index, days))
    scan_blocks.sort()

    if cadence_mode != 'trusted':
        cadence_stage = (
            'Verify known cadence' if cadence_mode == 'known'
            else ('Rediscover cadence' if cadence_invalidations
                  else 'Discover cadence'))
        # Give every future unit its inexpensive first chance, then revisit
        # rejected future-availability hypotheses before touching any
        # already-available unit. This preserves the future-first ordering
        # while avoiding an adaptive search on one exception when another
        # future unit can reveal the boundary in the preferred two calls.
        future_scan_blocks = [
            block for block in scan_blocks if block[0] == 0
        ]
        current_scan_blocks = [
            block for block in scan_blocks if block[0] != 0
        ]
        retry_future_blocks = [
            (2, *block[1:]) for block in future_scan_blocks
        ]
        ordered_scan_blocks = (
            future_scan_blocks + retry_future_blocks + current_scan_blocks)
        for (_future_priority, _score, _start, _length,
             unit_index, days) in ordered_scan_blocks:
            label = units[unit_index].get('unitId') or unit_index
            while True:
                discovery_candidate = (
                    future_discovery_candidate(unit_index)
                    if cadence_mode == 'unknown' else None)
                discovery_inferred = (
                    endpoint_inferred_dates(unit_index)
                    | set(lower_bound_inference_calls(unit_index)))
                lower_bound_mode = (
                    cadence_mode == 'unknown'
                    or (cadence_mode == 'known' and cadence_is_lower_bound))
                cadence_proof_incomplete = (
                    cadence_mode == 'unknown'
                    and is_future_cycle_start_candidate(unit_index)
                    and discovery_candidate is not None
                    and not discovery_candidate['ready'])
                if (not cadence_proof_incomplete
                        and lower_bound_mode and all(
                        day in observations[unit_index]
                        or day in discovery_inferred
                        for day in window_dates[unit_index])
                        and (not is_future_cycle_start_candidate(unit_index)
                             or pricing_window_start_resolved(unit_index))):
                    day = None
                elif (cadence_mode == 'unknown'
                      and is_future_cycle_start_candidate(unit_index)):
                    rejected_hint = min((
                        item['cadenceDays']
                        for item in cadence_candidate_rejections
                        if item.get('unitIndex') == unit_index
                    ), default=None)
                    if rejected_hint:
                        # This unit already disproved a longer candidate using
                        # property-wide responses. Bisect those existing
                        # differing-price intervals directly instead of
                        # reopening its availability-to-hold endpoint search.
                        day = next_boundary_probe(
                            unit_index, rejected_hint)
                    elif discovery_candidate and not discovery_candidate['ready']:
                        calendar_probes = (
                            discovery_candidate.get('calendarProbeDays') or [])
                        day = next((probe for probe in calendar_probes
                                    if probe not in observations[unit_index]),
                                   None)
                        if day is None:
                            day = next_candidate_boundary_confirmation_probe(
                                unit_index, discovery_candidate)
                        if day is None:
                            property_lower_bound = (
                                current_response_cadence_lower_bound(
                                    unit_index))
                            cadence_hint = max(
                                discovery_candidate['cadenceDays'],
                                property_lower_bound)
                            if (cadence_hint
                                    > discovery_candidate['cadenceDays']
                                    and cadence_response_contradiction(
                                        cadence_hint)):
                                # A long equal window on another unit is only
                                # a provisional property lower bound. If
                                # normal responses already make it impossible,
                                # continue from this unit's tighter boundary.
                                cadence_hint = (
                                    discovery_candidate['cadenceDays'])
                            day = next_boundary_probe(
                                unit_index, cadence_hint)
                    else:
                        day = next_future_discovery_probe(unit_index)
                else:
                    day = next_boundary_probe(
                        unit_index,
                        (supplied_cadence if cadence_mode == 'known'
                         else current_response_cadence_lower_bound(
                             unit_index) or None))
                if day is None:
                    if (cadence_mode == 'unknown'
                            and is_future_cycle_start_candidate(unit_index)):
                        future_discovery_exhausted.add(unit_index)
                        refresh_cadence()
                        if cadence_ready_at is not None:
                            refresh_phases()
                    break
                future_probe = day in future_availability_probe_days(
                    unit_index, supplied_cadence)
                if cadence_mode == 'unknown' and is_future_cycle_start_candidate(
                        unit_index):
                    search_reason = (
                        f'Compare the first and last pricing dates for future '
                        f'unit {label}, then bisect every proven differing-price '
                        'interval until consecutive boundaries establish the '
                        'cadence')
                elif future_probe:
                    search_reason = (
                        f'Test whether future availability is cycle day one '
                        f'for unit {label}')
                elif cadence_mode == 'known' and cadence_is_lower_bound:
                    search_reason = (
                        f'Probe supplied cadence-lower-bound intervals for '
                        f'unit {label} and infer equal endpoints without '
                        'sequential calls')
                elif cadence_mode == 'known':
                    search_reason = (
                        f'Probe cadence-spaced anchors and bisect a differing '
                        f'interval for unit {label}')
                else:
                    search_reason = (
                        f'Probe cadence-lower-bound intervals for unit {label} '
                        'and infer equal endpoints without sequential calls')
                query(
                    day, cadence_stage,
                    f'{search_reason}; evaluate every unit returned by each '
                    'property call.')
                refresh_cadence()
                if cadence_ready_at is not None:
                    refresh_phases()
                    break
                future_probe_days = future_availability_probe_days(
                    unit_index, supplied_cadence)
                if (cadence_mode == 'known'
                        and _future_priority == 0
                        and future_probe_days
                        and all(day in observations[unit_index]
                                for day in future_probe_days)
                        and observations[unit_index].get(
                            future_probe_days[0])
                        == observations[unit_index].get(
                            future_probe_days[1])):
                    # This unit is an exception to the cycle-day-one pattern.
                    # Try the next future unit before adaptively searching it.
                    break
            if cadence_ready_at is not None:
                break

        # A supplied cadence may be impossible to verify within every unit's
        # horizon. Complete retrieval is then the only safe known-mode result.
        # Stop early if the fallback responses happen to expose the proof.
        if cadence_ready_at is None:
            for day in property_dates:
                if day in call_index:
                    continue
                if (cadence_mode == 'unknown'
                        or (cadence_mode == 'known'
                            and cadence_is_lower_bound)) and all(
                        day not in window_sets[unit_index]
                        or day in observations[unit_index]
                        or day in endpoint_inferred_dates(unit_index)
                        or day in lower_bound_inference_calls(unit_index)
                        for unit_index in range(len(units))):
                    continue
                query(
                    day, 'Daily fallback',
                    ('Cadence is still unresolved; retrieve the next property '
                     'date without assuming an unobserved boundary.'))
                refresh_cadence()
                if cadence_ready_at is not None:
                    refresh_phases()
                    break

        if cadence_mode == 'unknown' and cadence_ready_at is None:
            endpoint_lower_bound = max((
                len(window_dates[index])
                for index, _proof_call
                in shared_endpoint_lower_bound_evidence()
                if len(window_dates[index]) not in rejected_cadences
            ), default=0)
            observed_lower_bound = largest_observed_equal_range()
            lower_bound = max(endpoint_lower_bound, observed_lower_bound)
            if lower_bound and lower_bound not in rejected_cadences:
                effective_cadence = lower_bound
                discovery_is_lower_bound = True
                cadence_evidence = {
                    'cadenceDays': lower_bound,
                    'proofCall': len(call_sequence),
                    'lowerBound': True,
                }

    # A 28-31 day fixed candidate supported by same-day-of-month boundaries
    # is ambiguous with a calendar-month schedule. Resolve that ambiguity once
    # at the property level before locating unit phases. The two responses also
    # populate the adjacent matrix ranges, so this is not repeated per unit.
    if (cadence_mode == 'unknown' and cadence_ready_at is not None
            and calendar_month_day is None):
        monthly_probe_days = calendar_month_probe_days(cadence_evidence)
        if len(monthly_probe_days) == 2:
            for day in monthly_probe_days:
                query(
                    day, 'Verify property calendar cadence',
                    'Check the next same-day-of-month boundary once for the '
                    'property; distinguish a calendar-month schedule from a '
                    'fixed 28-31 day cadence without per-unit rechecks.')
            monthly_evidence = calendar_month_evidence()
            if (monthly_evidence
                    and not calendar_month_response_contradiction()):
                cadence_evidence = monthly_evidence
                effective_cadence = monthly_evidence['cadenceDays']
                calendar_month_day = monthly_evidence['calendarMonthDay']
                cadence_known_at = monthly_evidence['proofCall']
                cadence_verified_at = monthly_evidence['proofCall']
                cadence_ready_at = monthly_evidence['proofCall']
                unit_phases.clear()
                phase_known_at.clear()
                refresh_phases()
        elif cadence_evidence:
            try:
                first_month_boundary = date.fromisoformat(
                    cadence_evidence['firstBoundary'])
                second_month_boundary = date.fromisoformat(
                    cadence_evidence['secondBoundary'])
            except (KeyError, TypeError, ValueError):
                first_month_boundary = second_month_boundary = None
            if (first_month_boundary and second_month_boundary
                    and first_month_boundary.day == second_month_boundary.day
                    and 28 <= (
                        second_month_boundary
                        - first_month_boundary).days <= 31):
                # The proving unit may end before a third month is available.
                # Cover the same calendar edge across the property horizon.
                # These are shared property calls, never one check per unit,
                # and they directly populate every ambiguous monthly range.
                for day in property_dates:
                    if (date.fromisoformat(day).day
                            != first_month_boundary.day):
                        continue
                    query(
                        day, 'Cover property calendar edges',
                        'Retrieve the possible same-day-of-month price edge '
                        'once for the property because the proving unit ends '
                        'before a third monthly boundary can be checked.')
                monthly_evidence = calendar_month_evidence()
                if (monthly_evidence
                        and not calendar_month_response_contradiction()):
                    cadence_evidence = monthly_evidence
                    effective_cadence = monthly_evidence['cadenceDays']
                    calendar_month_day = (
                        monthly_evidence['calendarMonthDay'])
                    cadence_known_at = monthly_evidence['proofCall']
                    cadence_verified_at = monthly_evidence['proofCall']
                    cadence_ready_at = monthly_evidence['proofCall']
                    unit_phases.clear()
                    phase_known_at.clear()
                    refresh_phases()

    def cadence_contradiction(cadence_hint):
        """Return the first response-only contradiction of a cadence belief."""
        if not cadence_hint:
            return None
        if calendar_month_day is None:
            response_contradiction = cadence_response_contradiction(
                cadence_hint)
            if response_contradiction:
                return response_contradiction
        else:
            response_contradiction = (
                calendar_month_response_contradiction())
            if response_contradiction:
                return response_contradiction
        for unit_index, days in enumerate(window_dates):
            boundaries = observed_boundaries(unit_index)
            if len(boundaries) >= 2:
                phases = {
                    (date.fromisoformat(boundary['date']).day
                     if calendar_month_day is not None
                     else date.fromisoformat(
                         boundary['date']).toordinal() % cadence_hint)
                    for boundary in boundaries
                }
                if len(phases) > 1:
                    proof_call = max(
                        boundary['proofCall'] for boundary in boundaries)
                    return {
                        'unitIndex': unit_index,
                        'unitId': units[unit_index].get('unitId'),
                        'atCall': proof_call,
                        'reason': (
                            f'Observed boundaries for unit '
                            f'{units[unit_index].get("unitId") or unit_index} '
                            f'do not share one {cadence_hint}-day phase.'),
                    }

            phase = unit_phases.get(unit_index)
            if phase is None:
                continue
            for group in response_derived_groups(
                    days, cadence_hint, phase):
                observed_group = [
                    (day, observations[unit_index][day])
                    for day in group
                    if day in observations[unit_index]
                    and observations[unit_index][day] is not None
                ]
                if len({signature for _day, signature in observed_group}) <= 1:
                    continue
                proof_call = max(
                    call_index[day] for day, _signature in observed_group)
                return {
                    'unitIndex': unit_index,
                    'unitId': units[unit_index].get('unitId'),
                    'atCall': proof_call,
                    'reason': (
                        f'Unit {units[unit_index].get("unitId") or unit_index} '
                        f'returned distinct prices inside one projected '
                        f'{cadence_hint}-day group.'),
                }
        return None

    # Once cadence is trusted or response-verified, scan metadata-defined unit
    # windows until each unit either exposes one exact boundary or every one of
    # its dates has been retrieved. Each call can resolve several units at once.
    if cadence_ready_at is not None and effective_cadence:
        refresh_phases()
        live_contradiction = None
        while True:
            unresolved = [
                index for index, days in enumerate(window_dates)
                if (index not in unit_phases
                    or has_unresolved_availability_bracket(index)
                    or (
                        units[index].get('availabilityTiming')
                        != 'Future Available'
                        and not pricing_window_start_resolved(index))
                    or future_pricing_start_probe_needed(index))
                and index not in phase_probe_exhausted
                and not all(
                    day in observations[index]
                    or day in endpoint_inferred_dates(index)
                    or day in lower_bound_inference_calls(index)
                    or day in equal_interval_dates(index, effective_cadence)
                    for day in days)
                and any(day not in observations[index] for day in days)
            ]
            if not unresolved:
                break
            ranked = []
            for unit_index in unresolved:
                remaining = [
                    day for day in window_dates[unit_index]
                    if day not in observations[unit_index]
                ]
                coverage = sum(
                    sum(day in window_sets[other] for other in unresolved)
                    for day in remaining
                )
                availability_priority = (
                    0 if units[unit_index].get('availabilityTiming')
                    == 'Future Available' else 1)
                ranked.append((
                    availability_priority, -coverage, remaining[0],
                    len(remaining), unit_index, remaining))
            (_availability, _coverage, _first, _count, focus_index,
             _remaining) = min(ranked)
            label = units[focus_index].get('unitId') or focus_index
            while True:
                day = next_boundary_probe(focus_index, effective_cadence)
                if day is None:
                    # Never requeue an unchanged unit. This can occur when its
                    # metadata window begins before Entrata starts returning a
                    # price and every useful cadence anchor has been exhausted.
                    phase_probe_exhausted.add(focus_index)
                    break
                future_alignment_probe = day in future_availability_probe_days(
                    focus_index, effective_cadence)
                queried = query(
                    day,
                    ('Verify availability-cycle alignment'
                     if future_alignment_probe else 'Locate unit cycles'),
                    (f'Test n+cadence-1 and n+cadence for future-available '
                     f'unit {label}; if distinct, both first ranges are also '
                     'populated.'
                     if future_alignment_probe
                     else f'Probe cadence-spaced anchors for unit {label}, '
                          'then bisect only an interval proven to contain a '
                          'boundary.'))
                if not queried:
                    phase_probe_exhausted.add(focus_index)
                    break
                phase_probe_exhausted.discard(focus_index)
                refresh_phases()
                if cadence_mode == 'unknown':
                    live_contradiction = cadence_contradiction(
                        effective_cadence)
                    if live_contradiction:
                        break
                if (focus_index in unit_phases
                        and not has_unresolved_availability_bracket(
                            focus_index)
                        and (
                            (units[focus_index].get('availabilityTiming')
                             == 'Future Available'
                             and not future_pricing_start_probe_needed(
                                 focus_index))
                            or pricing_window_start_resolved(focus_index))):
                    break
            if live_contradiction:
                break

        # Cycle groups now come only from an observed phase, supplied/discovered
        # cadence, and the metadata-defined pricing window.
        target_ranges = []
        if not live_contradiction:
            for unit_index, phase in unit_phases.items():
                inferred_dates = (
                    endpoint_inferred_dates(unit_index)
                    | set(lower_bound_inference_calls(unit_index))
                    | equal_interval_dates(
                        unit_index, effective_cadence))
                for days in response_derived_groups(
                        window_dates[unit_index], effective_cadence, phase):
                    if (not any(
                            observations[unit_index].get(day) is not None
                            for day in days)
                            and not all(
                                day in inferred_dates for day in days)):
                        target_ranges.append({
                            'start': days[0], 'end': days[-1]})
            for day in _dynamic_pricing_minimum_range_dates([
                    {'priceRanges': target_ranges}]):
                query(
                    day, 'Fill matrix',
                    'Retrieve one response inside each cycle group derived '
                    'from observed phase and the available cadence.')
                if cadence_mode == 'unknown':
                    live_contradiction = cadence_contradiction(
                        effective_cadence)
                    if live_contradiction:
                        break
    else:
        live_contradiction = None

    contradiction = (
        live_contradiction or cadence_contradiction(effective_cadence))
    if (cadence_mode == 'unknown' and contradiction
            and effective_cadence not in rejected_cadences):
        accepted_at = (
            cadence_known_at
            or (cadence_evidence or {}).get('proofCall')
            or contradiction['atCall'])
        invalidation = {
            'cadenceDays': effective_cadence,
            'acceptedAtCall': accepted_at,
            'atCall': max(accepted_at, contradiction['atCall']),
            'unitIndex': contradiction['unitIndex'],
            'unitId': contradiction['unitId'],
            'reason': contradiction['reason'],
        }
        return _dynamic_pricing_observation_only_plan(
            units, None, 'unknown', cadence_is_lower_bound=False,
            _seed_call_steps=call_steps,
            _rejected_cadences=(
                rejected_cadences | {effective_cadence}),
            _cadence_invalidations=(
                cadence_invalidations + [invalidation]),
            _cadence_candidate_rejections=cadence_candidate_rejections)

    # If cadence could not be verified/discovered, the scan blocks have queried
    # every metadata-defined property date. This is an explicit full-retrieval
    # result, not a sparse plan chosen with hindsight.
    total = correct = 0
    incorrect_cells = []
    for unit_index, unit in enumerate(units):
        signatures = truth[unit_index]
        groups = []
        if effective_cadence and unit_index in unit_phases:
            groups = response_derived_groups(
                window_dates[unit_index], effective_cadence,
                unit_phases[unit_index])
        group_by_day = {
            day: group for group in groups for day in group
        }
        equal_values = equal_interval_values(unit_index, effective_cadence)
        endpoint_signature = None
        if unit_index in endpoint_equal_at_call and window_dates[unit_index]:
            endpoint_signature = observations[unit_index].get(
                window_dates[unit_index][0])
        lower_bound_values = {
            day: evidence['signature']
            for day, evidence in lower_bound_inference_evidence(
                unit_index).items()
        }
        for day in unit.get('pricingDates') or []:
            total += 1
            predicted_signature = None
            prediction_available = False
            if day in api_responses[unit_index]:
                predicted_signature = api_responses[unit_index][day]
                prediction_available = True
            elif endpoint_signature is not None:
                predicted_signature = endpoint_signature
                prediction_available = True
            elif day in lower_bound_values:
                predicted_signature = lower_bound_values[day]
                prediction_available = True
            elif day in equal_values:
                predicted_signature = equal_values[day]
                prediction_available = True
            if not prediction_available:
                group = group_by_day.get(day) or []
                inferred_from = next((
                    candidate for candidate in group
                    if observations[unit_index].get(candidate) is not None
                ), None)
                if inferred_from is not None:
                    predicted_signature = observations[unit_index][inferred_from]
                    prediction_available = True
            reconstructed = (
                prediction_available
                and predicted_signature == signatures.get(day))
            if reconstructed:
                correct += 1
            else:
                incorrect_cells.append({
                    'unitIndex': unit_index,
                    'unitId': units[unit_index].get('unitId'),
                    'date': day,
                })

    if cadence_mode == 'trusted':
        strategy = (
            'Trust supplied cadence; adaptively locate only necessary phases; '
            'cover cycles')
        cadence_status = 'Accepted without verification'
    elif (cadence_ready_at is None and cadence_mode == 'known'
          and cadence_is_lower_bound):
        strategy = (
            'Retain supplied cadence lower bound; infer bounded equal '
            'intervals; retrieve only unresolved dates')
        cadence_status = (
            f'Lower bound ≥ {effective_cadence} days retained; exact cadence '
            'not verifiable from the retrieved horizon')
    elif cadence_ready_at is None and discovery_is_lower_bound:
        strategy = (
            'Infer equal future-unit endpoint windows; retain a cadence lower '
            'bound; retrieve remaining unresolved dates')
        cadence_status = (
            f'Lower bound ≥ {effective_cadence} days from retrieved responses')
    elif cadence_ready_at is None:
        strategy = (
            'Cadence not observable from responses; retrieve every property date')
        cadence_status = (
            'Not verifiable from retrieved horizon' if cadence_mode == 'known'
            else 'Not discoverable from retrieved horizon')
    elif cadence_mode == 'known':
        strategy = (
            'Adaptively verify supplied cadence; locate phases by bisection; '
            'cover cycles')
        cadence_status = f'Verified at call {cadence_verified_at}'
    else:
        strategy = (
            'Adaptively discover cadence; locate phases by bisection; cover cycles')
        if (cadence_evidence or {}).get('calendarMonth'):
            strategy = (
                'Discover calendar-month cadence from three property-level '
                'boundaries; locate phases; cover monthly cycles')
            cadence_status = (
                f'Discovered calendar-month cadence at call '
                f'{cadence_known_at} (day {calendar_month_day}; '
                f'{effective_cadence}-31 day ranges)')
        elif (cadence_evidence or {}).get('singleBoundaryAssumption'):
            cadence_status = (
                f'Assumed {effective_cadence}-day cadence at call '
                f'{cadence_known_at} from one boundary spanning at least half '
                'the unit hold with a constant observed tail')
        else:
            cadence_status = (
                f'Discovered {effective_cadence}-day cadence at call '
                f'{cadence_known_at}')

    if cadence_candidate_rejections:
        rejected = ', '.join(
            str(item.get('cadenceDays'))
            for item in cadence_candidate_rejections)
        strategy = (
            f'Reject impossible cadence candidate ({rejected}) from existing '
            f'property responses; {strategy[0].lower() + strategy[1:]}')
        cadence_status = (
            f'{cadence_status}; rejected candidate {rejected} without an '
            'additional cadence-check call')

    if cadence_invalidations:
        invalidated = ', '.join(
            str(item.get('cadenceDays'))
            for item in cadence_invalidations)
        strategy = (
            f'Invalidate contradicted cadence ({invalidated}); re-enter '
            f'discovery; {strategy[0].lower() + strategy[1:]}')
        cadence_status = (
            f'{cadence_status}; invalidated prior cadence '
            f'{invalidated} from later unit responses')

    unit_cycle_boundaries = {}
    future_availability_alignment = {}
    if effective_cadence:
        for unit_index, phase in unit_phases.items():
            unit_cycle_boundaries[str(unit_index)] = (
                [] if unit_index in boundary_not_required else [
                    day for day in window_dates[unit_index]
                    if ((date.fromisoformat(day).day == phase)
                        if calendar_month_day is not None
                        else (date.fromisoformat(day).toordinal()
                              % effective_cadence == phase))
                ])
        for unit_index in range(len(units)):
            proof_call = future_availability_alignment_proof(
                unit_index, effective_cadence)
            probe_days = future_availability_probe_days(
                unit_index, effective_cadence)
            if not probe_days or not all(
                    day in observations[unit_index] for day in probe_days):
                continue
            confirmed = proof_call is not None
            future_availability_alignment[str(unit_index)] = {
                'status': 'Confirmed' if confirmed else 'Rejected',
                'atCall': (proof_call if confirmed else max(
                    call_index[day] for day in probe_days)),
            }
    return {
        'calls': call_sequence,
        'steps': call_steps,
        'accuracy': round(100 * correct / total, 3) if total else 0.0,
        'incorrectCells': incorrect_cells,
        'cadenceKnownAtCall': cadence_known_at,
        'cadenceVerifiedAtCall': cadence_verified_at,
        'cadenceReadyAtCall': cadence_ready_at,
        'effectiveCadenceDays': effective_cadence,
        'cadenceEvidence': cadence_evidence,
        'cadenceInvalidations': cadence_invalidations,
        'cadenceCandidateRejections': cadence_candidate_rejections,
        'calendarMonthDay': calendar_month_day,
        'cadenceStatus': cadence_status,
        'phaseKnownAtCall': phase_known_at,
        'unitCyclePhases': {
            str(index): phase for index, phase in unit_phases.items()
        },
        'unitCycleBoundaryDates': unit_cycle_boundaries,
        'unitBoundaryNotRequired': sorted(boundary_not_required),
        'unitFutureAvailabilityAlignment': future_availability_alignment,
        'unitEndpointEqualityAtCall': {
            str(index): call
            for index, call in endpoint_equal_at_call.items()
        },
        'unitLowerBoundInferenceAtCall': {
            str(index): inference
            for index in range(len(units))
            if (inference := lower_bound_inference_calls(index))
        },
        'unitWindowAdjustedAtCall': {
            str(index): call
            for index, call in adjusted_window_at_call.items()
        },
        'unitPlannedPricingWindows': {
            str(index): {
                'start': days[0] if days else None,
                'end': days[-1] if days else None,
                'days': len(days),
            }
            for index, days in enumerate(window_dates)
        },
        'strategy': strategy,
        'cadenceIsLowerBound': (
            cadence_is_lower_bound or discovery_is_lower_bound),
    }


def _dynamic_pricing_date_groups(days, cadence_days, phase):
    """Partition metadata-defined dates using a response-derived cycle phase."""
    groups = []
    current_key = None
    current_dates = []
    for day in days:
        cycle_key = (
            date.fromisoformat(day).toordinal() - phase) // cadence_days
        if current_key is not None and cycle_key != current_key:
            groups.append(current_dates)
            current_dates = []
        current_key = cycle_key
        current_dates.append(day)
    if current_dates:
        groups.append(current_dates)
    return groups


def _dynamic_pricing_visualizer_metadata(
        units, cadence_days, cadence_is_lower_bound=False):
    """Attach compact step-through metadata before signatures are discarded."""
    for unit_index, unit in enumerate(units):
        unit['holdTimeDays'] = unit.get('pricingWindowDayCount') or 0
        unit['visualPricingDates'] = list(
            unit.get('_initialPricingDates') or [])
        unit['visualStartDate'] = (
            unit['visualPricingDates'][0]
            if unit['visualPricingDates'] else unit.get('firstPricingDate'))
        signature_ids = {}
        signature_indexes = {}
        for day in unit.get('pricingDates') or []:
            signature = (unit.get('_pricingSignatures') or {}).get(day)
            if signature not in signature_indexes:
                signature_indexes[signature] = len(signature_indexes)
            signature_ids[day] = signature_indexes[signature]
        unit['pricingSignatureIds'] = signature_ids


def _dynamic_pricing_analyze_payload(
        community, payload, latest_sync=None, snapshot_link='',
        unit_details=None, unknown_only=False):
    """Summarize the matrix corresponding to one Entrata community's sync."""
    matrices = payload.get('priceMatrices') if isinstance(payload, dict) else []
    if not isinstance(matrices, list):
        matrices = []
    valid_value = payload.get('isValid', True) if isinstance(payload, dict) else False
    payload_valid = (
        valid_value is True
        or str(valid_value).strip().casefold() in ('true', '1', 'yes')
    )
    unit_details = unit_details or {}
    units = []
    for ordinal, matrix in enumerate(matrices, 1):
        unit = _dynamic_pricing_unit_result(matrix, ordinal)
        if unit:
            details = unit_details.get(str(unit.get('sourceUnitId') or '')) or {}
            unit_number = details.get('unit_number') or details.get('unitNumber')
            if unit_number not in (None, ''):
                unit['unitId'] = str(unit_number)
            unit['availableDate'] = _dynamic_pricing_iso_date(
                details.get('date_available') or details.get('dateAvailable'))
            units.append(unit)

    # A matrix with no forward-looking range offers no cadence or API-call
    # savings to analyze. Exclude the community when every unit has at most
    # its initial pricing day.
    excluded = not payload_valid or not units or all(
        unit['pricingDateCount'] <= 1 for unit in units)

    pricing_does_not_change = bool(units) and all(
        len(unit.get('observedChangeDates') or []) <= 1 for unit in units)
    cadence_evidence = [
        (unit, price_range.get('lengthDays'))
        for unit in units
        for price_range in (unit.get('priceRanges') or [])[1:-1]
        if isinstance(price_range.get('lengthDays'), int)
        and price_range.get('lengthDays') > 0
    ]
    cadence_lengths = [length for _unit, length in cadence_evidence]
    observed_range_lengths = [
        price_range.get('lengthDays')
        for unit in units
        for price_range in (unit.get('priceRanges') or [])
        if isinstance(price_range.get('lengthDays'), int)
        and price_range.get('lengthDays') > 0
    ]
    cadence_is_lower_bound = not cadence_lengths and bool(
        observed_range_lengths)
    cadence_days = (
        max(observed_range_lengths) if cadence_is_lower_bound
        else (min(cadence_lengths) if cadence_lengths else None)
    )
    cadence_evidence_units = len({
        str(unit.get('sourceUnitId') or unit.get('unitId') or '')
        for unit, _length in cadence_evidence
    })
    cadence_is_consistent = bool(cadence_days) and all(
        length % cadence_days == 0 for length in cadence_lengths)
    can_project_cycle = bool(
        cadence_days and cadence_is_consistent and not cadence_is_lower_bound)
    if cadence_is_lower_bound and pricing_does_not_change:
        cadence_confidence = 'No Changes Observed; Lower Bound Only'
    elif cadence_is_lower_bound:
        cadence_confidence = 'Lower Bound Only'
    elif not cadence_lengths:
        cadence_confidence = 'Insufficient Data'
    elif len(cadence_lengths) == 1:
        cadence_confidence = 'Limited Evidence'
    elif cadence_is_consistent:
        cadence_confidence = 'Reliable'
    else:
        cadence_confidence = 'Mixed'

    sync_date = latest_sync.astimezone(timezone.utc).date() if isinstance(
        latest_sync, datetime) else None
    cycle_phases = set()
    predictable_units = 0
    future_units = future_starts_at_availability = 0
    already_units = already_starts_at_sync = 0

    # The ranges remain the exact observed runs of equal pricing. Cadence is
    # inferred only from complete interior runs; the first and last runs can
    # be truncated by the unit's availability and the retrieved horizon.
    for unit in units:
        unit['cadenceDays'] = cadence_days
        unit['cadence'] = (
            f'>= {cadence_days}' if cadence_is_lower_bound and cadence_days
            else (str(cadence_days) if cadence_days else None))
        ranges = unit.get('priceRanges') or []
        first_range = ranges[0] if ranges else {}
        last_range = ranges[-1] if ranges else {}
        first_pricing_date = unit['pricingDates'][0]
        last_pricing_date = unit['pricingDates'][-1]
        available_date = unit.get('availableDate')
        unit['firstPricingDate'] = first_pricing_date
        unit['lastPricingDate'] = last_pricing_date
        unit['firstRangeDays'] = first_range.get('lengthDays')
        unit['lastRangeDays'] = last_range.get('lengthDays')

        available_day = (date.fromisoformat(available_date)
                         if available_date else None)
        initial_start = (
            sync_date.isoformat() if sync_date is not None
            else first_pricing_date)
        if available_day is not None and sync_date is not None:
            initial_start = max(available_day, sync_date).isoformat()
        elif available_day is not None:
            initial_start = available_day.isoformat()
        initial_start_day = date.fromisoformat(initial_start)
        hold_time_days = unit.get('pricingWindowDayCount') or 0
        unit['_initialPricingDates'] = [
            (initial_start_day + timedelta(days=offset)).isoformat()
            for offset in range(hold_time_days)
        ]
        if available_day is None or sync_date is None:
            unit['availabilityTiming'] = 'Unknown'
        elif available_day > sync_date:
            unit['availabilityTiming'] = 'Future Available'
            future_units += 1
        else:
            unit['availabilityTiming'] = 'Already Available'
            already_units += 1

        if available_date and first_pricing_date == available_date:
            unit['pricingWindowStartsAt'] = 'Availability Date'
            if unit['availabilityTiming'] == 'Future Available':
                future_starts_at_availability += 1
        elif sync_date and first_pricing_date == sync_date.isoformat():
            unit['pricingWindowStartsAt'] = 'Sync Date'
            if unit['availabilityTiming'] == 'Already Available':
                already_starts_at_sync += 1
        else:
            unit['pricingWindowStartsAt'] = 'Other / Unknown'

        next_change = ranges[1].get('start') if len(ranges) > 1 else None
        unit['nextObservedPriceChangeDate'] = next_change
        unit['cycleDayAtWindowStart'] = None
        unit['nextProjectedCycleDate'] = None
        unit['_cyclePhase'] = None
        if can_project_cycle and next_change:
            first_length = first_range.get('lengthDays')
            if isinstance(first_length, int) and first_length > 0:
                offset = (cadence_days - (first_length % cadence_days)) % cadence_days
                unit['cycleDayAtWindowStart'] = offset + 1
            for price_range in ranges[1:]:
                try:
                    observed_phase = (
                        date.fromisoformat(price_range['start']).toordinal()
                        % cadence_days)
                    cycle_phases.add(observed_phase)
                    if unit['_cyclePhase'] is None:
                        unit['_cyclePhase'] = observed_phase
                except (KeyError, TypeError, ValueError):
                    continue
            try:
                projected = date.fromisoformat(last_range['start'])
                last_day = date.fromisoformat(last_range['end'])
                while projected <= last_day:
                    projected += timedelta(days=cadence_days)
                unit['nextProjectedCycleDate'] = projected.isoformat()
            except (KeyError, TypeError, ValueError):
                pass
            predictable_units += 1

        if pricing_does_not_change and cadence_is_lower_bound:
            unit['predictionStatus'] = (
                'No changes observed; use the observed range as a cadence lower bound')
        elif pricing_does_not_change:
            unit['predictionStatus'] = 'No price changes observed'
        elif not cadence_days:
            unit['predictionStatus'] = 'Observed ranges only; cadence unavailable'
        elif not cadence_is_consistent:
            unit['predictionStatus'] = 'Observed ranges only; cadence evidence is mixed'
        elif next_change:
            unit['predictionStatus'] = 'Cycle phase inferred from an observed change'
        else:
            unit['predictionStatus'] = (
                'Availability date alone does not establish cycle phase')

    if pricing_does_not_change:
        cycle_alignment = 'No Observed Changes'
    elif not can_project_cycle or not cycle_phases:
        cycle_alignment = 'Unknown'
    elif len(cycle_phases) == 1:
        cycle_alignment = 'Community-Aligned'
    else:
        cycle_alignment = f'Unit-Specific ({len(cycle_phases)} phases)'

    inconsistent_input_units = [
        unit.get('unitId')
        for unit in units
        if (unit.get('firstPricingDate')
            not in set(unit.get('_initialPricingDates') or []))
    ]

    all_pricing_dates = sorted({
        day for unit in units for day in unit['_initialPricingDates']
    })
    current_calls = len(all_pricing_dates)

    def finalized_plan(mode):
        plan = _dynamic_pricing_observation_only_plan(
            units,
            cadence_days if mode in ('known', 'trusted') else None,
            mode,
            cadence_is_lower_bound=(
                cadence_is_lower_bound if mode in ('known', 'trusted')
                else False))
        calls = plan['calls']
        calls_saved = current_calls - len(calls)
        return {
            'mode': mode,
            'bootstrapApiCallDates': calls,
            'bootstrapApiCalls': len(calls),
            'apiCallsSaved': calls_saved,
            'apiCallsSavedPct': round(
                100 * calls_saved / current_calls, 1) if current_calls else 0.0,
            'reconstructionAccuracyPct': plan['accuracy'],
            'incorrectCells': plan.get('incorrectCells') or [],
            'retrievalStrategy': plan['strategy'],
            'cadenceKnownAtCall': plan['cadenceKnownAtCall'],
            'cadenceVerifiedAtCall': plan['cadenceVerifiedAtCall'],
            'cadenceReadyAtCall': plan['cadenceReadyAtCall'],
            'effectiveCadenceDays': plan['effectiveCadenceDays'],
            'cadenceEvidence': plan['cadenceEvidence'],
            'cadenceInvalidations': plan['cadenceInvalidations'],
            'cadenceCandidateRejections': (
                plan['cadenceCandidateRejections']),
            'calendarMonthDay': plan['calendarMonthDay'],
            'cadenceStatus': plan['cadenceStatus'],
            'cadenceIsLowerBound': plan['cadenceIsLowerBound'],
            'algorithmCallSteps': plan['steps'],
            'unitPhaseKnownAtCall': {
                str(index): call
                for index, call in plan['phaseKnownAtCall'].items()
            },
            'unitCyclePhases': plan['unitCyclePhases'],
            'unitCycleBoundaryDates': plan['unitCycleBoundaryDates'],
            'unitBoundaryNotRequired': plan['unitBoundaryNotRequired'],
            'unitFutureAvailabilityAlignment': (
                plan['unitFutureAvailabilityAlignment']),
            'unitEndpointEqualityAtCall': plan['unitEndpointEqualityAtCall'],
            'unitLowerBoundInferenceAtCall': (
                plan['unitLowerBoundInferenceAtCall']),
            'unitWindowAdjustedAtCall': plan['unitWindowAdjustedAtCall'],
            'unitPlannedPricingWindows': plan['unitPlannedPricingWindows'],
        }

    plan_modes = ('unknown',) if unknown_only else (
        'known', 'trusted', 'unknown')
    retrieval_plans = {
        mode: finalized_plan(mode) for mode in plan_modes
    }
    unknown_plan = retrieval_plans['unknown']
    # Full validation consumes only Unknown-mode fields. Preserve the normal
    # response shape without calculating two plans that the job discards;
    # opening a saved result rebuilds all three modes on demand.
    known_plan = retrieval_plans.get('known', unknown_plan)
    trusted_plan = retrieval_plans.get('trusted', unknown_plan)
    _dynamic_pricing_visualizer_metadata(
        units, cadence_days, cadence_is_lower_bound)

    # Comparable price signatures are an internal verification aid, not
    # report data. Removing them also keeps large report payloads manageable.
    for unit in units:
        unit.pop('_pricingSignatures', None)
        unit.pop('_cyclePhase', None)
        unit.pop('_initialPricingDates', None)
    return {
        'buildingId': str(community.get('BUILDING_ID') or ''),
        'buildingName': community.get('BUILDING_NAME') or '',
        'orgId': community.get('ORG_ID'),
        'orgName': community.get('ORG_NAME') or '',
        'cadenceDays': cadence_days,
        'cadence': (
            f'>= {cadence_days}' if cadence_is_lower_bound and cadence_days
            else (str(cadence_days) if cadence_days else 'Insufficient Data')),
        'cadenceIsLowerBound': cadence_is_lower_bound,
        'cadenceLowerBoundDays': (
            cadence_days if cadence_is_lower_bound else None),
        'pricingDoesNotChange': pricing_does_not_change,
        'cadenceConfidence': cadence_confidence,
        'cadenceEvidenceRangeCount': len(cadence_lengths),
        'cadenceEvidenceUnitCount': cadence_evidence_units,
        'cadenceEvidenceLengths': sorted(set(cadence_lengths)),
        'cycleAlignment': cycle_alignment,
        'algorithmInputComplete': not inconsistent_input_units,
        'algorithmInputIssueUnits': inconsistent_input_units,
        'predictableUnitCount': predictable_units,
        'predictionCoveragePct': round(
            100 * predictable_units / len(units), 1) if units else 0,
        'futureUnitCount': future_units,
        'futureStartsAtAvailabilityCount': future_starts_at_availability,
        'alreadyAvailableUnitCount': already_units,
        'alreadyAvailableStartsAtSyncCount': already_starts_at_sync,
        'unitCount': len(units),
        'priceChangeDates': known_plan['bootstrapApiCallDates'],
        'newApiCalls': known_plan['bootstrapApiCalls'],
        'currentApiCalls': current_calls,
        'knownBootstrapApiCallDates': known_plan['bootstrapApiCallDates'],
        'knownBootstrapApiCalls': known_plan['bootstrapApiCalls'],
        'knownApiCallsSaved': known_plan['apiCallsSaved'],
        'knownApiCallsSavedPct': known_plan['apiCallsSavedPct'],
        'knownReconstructionAccuracyPct': (
            known_plan['reconstructionAccuracyPct']),
        'knownCadenceStatus': known_plan['cadenceStatus'],
        'trustedBootstrapApiCallDates': (
            trusted_plan['bootstrapApiCallDates']),
        'trustedBootstrapApiCalls': trusted_plan['bootstrapApiCalls'],
        'trustedApiCallsSaved': trusted_plan['apiCallsSaved'],
        'trustedApiCallsSavedPct': trusted_plan['apiCallsSavedPct'],
        'trustedReconstructionAccuracyPct': (
            trusted_plan['reconstructionAccuracyPct']),
        'unknownBootstrapApiCallDates': unknown_plan['bootstrapApiCallDates'],
        'unknownBootstrapApiCalls': unknown_plan['bootstrapApiCalls'],
        'unknownApiCallsSaved': unknown_plan['apiCallsSaved'],
        'unknownApiCallsSavedPct': unknown_plan['apiCallsSavedPct'],
        'unknownReconstructionAccuracyPct': (
            unknown_plan['reconstructionAccuracyPct']),
        'unknownCadenceStatus': unknown_plan['cadenceStatus'],
        'retrievalPlans': retrieval_plans,
        # Keep the known-cadence values for saved reports and older clients.
        'apiCallsSaved': known_plan['apiCallsSaved'],
        'apiCallsSavedPct': known_plan['apiCallsSavedPct'],
        'bootstrapApiCallDates': known_plan['bootstrapApiCallDates'],
        'bootstrapApiCalls': known_plan['bootstrapApiCalls'],
        'bootstrapApiCallsSaved': known_plan['apiCallsSaved'],
        'reconstructionAccuracyPct': known_plan['reconstructionAccuracyPct'],
        'retrievalStrategy': known_plan['retrievalStrategy'],
        'cadenceMode': 'known',
        'cadenceKnownAtCall': known_plan['cadenceKnownAtCall'],
        'cadenceVerifiedAtCall': known_plan['cadenceVerifiedAtCall'],
        'algorithmCallSteps': known_plan['algorithmCallSteps'],
        'latestSync': (
            latest_sync.isoformat() if hasattr(latest_sync, 'isoformat')
            else latest_sync),
        'snapshotLink': snapshot_link,
        'units': units,
        'excluded': excluded,
        'error': None,
    }


def _dynamic_pricing_latest_mits_sync(community):
    """Return the latest successful Entrata MITS snapshot name and timestamp."""
    building_id = str(community.get('BUILDING_ID') or '')
    entity = f'building_{building_id}'
    entity_prefix = f'{ROOT}Entrata/{entity}/'
    snapshot = _latest_snapshot_seeked(
        entity_prefix, _cutoff_stamps(), full_fallback=True)
    if not snapshot:
        return None, None, ''
    try:
        sync_at = _snapshot_dt(snapshot)
    except (TypeError, ValueError):
        return None, None, ''
    return snapshot, sync_at, _snapshot_link(
        entity, snapshot, community.get('ORG_ID'))


def _dynamic_pricing_snapshot_unit_details(building_id, snapshot):
    """Read point-in-time unit metadata from the same Entrata MITS snapshot."""
    if not snapshot:
        return {}
    key = (f'{ROOT}Entrata/building_{building_id}/{snapshot}/'
           'unit-details.json.gz')
    try:
        response = s3().get_object(Bucket=BUCKET, Key=key)
        raw = response['Body'].read()
        if raw[:2] == b'\x1f\x8b':
            raw = gzip_module.decompress(raw)
        payload = json.loads(raw.decode('utf-8'))
    except Exception:
        # Availability context is diagnostic enrichment. A valid pricing
        # matrix remains reportable when its companion details file is absent.
        return {}

    if isinstance(payload, dict):
        details = {}
        for source_id, value in payload.items():
            if not isinstance(value, dict):
                continue
            unit_id = value.get('id')
            details[str(unit_id if unit_id not in (None, '') else source_id)] = value
        return details
    if isinstance(payload, list):
        return {
            str(value.get('id')): value
            for value in payload
            if isinstance(value, dict) and value.get('id') not in (None, '')
        }
    return {}


def _dynamic_pricing_matrix_version_for_sync(key, sync_at):
    """Find the matrix version closest to a MITS sync on the same UTC date.

    Entrata writes the versioned dynamic-pricing object immediately after its
    MITS snapshot. Restricting the match to the sync's UTC calendar date avoids
    silently substituting a newer matrix when a community has stopped syncing.
    """
    target_date = sync_at.astimezone(timezone.utc).date()
    kwargs = {
        'Bucket': DYNAMIC_PRICING_BUCKET,
        'Prefix': key,
        'MaxKeys': PAGE_SIZE,
    }
    best = None
    while True:
        response = s3().list_object_versions(**kwargs)
        page_dates = []
        for version in response.get('Versions', []):
            if version.get('Key') != key:
                continue
            modified = version.get('LastModified')
            if not isinstance(modified, datetime):
                continue
            if modified.tzinfo is None:
                modified = modified.replace(tzinfo=timezone.utc)
            modified = modified.astimezone(timezone.utc)
            page_dates.append(modified.date())
            if modified.date() != target_date:
                continue
            # Prefer the smallest timestamp gap. An equally close post-sync
            # version wins because pricing matrices are normally written just
            # after the MITS snapshot is committed.
            rank = (abs((modified - sync_at).total_seconds()),
                    modified < sync_at, modified)
            if best is None or rank < best[0]:
                best = (rank, version)

        # Versions are returned newest first. Once a page has crossed below
        # the target date, no later page can contain a same-day candidate.
        if page_dates and min(page_dates) < target_date:
            break
        if not response.get('IsTruncated'):
            break
        kwargs['KeyMarker'] = response.get('NextKeyMarker')
        next_version_marker = response.get('NextVersionIdMarker')
        if next_version_marker:
            kwargs['VersionIdMarker'] = next_version_marker
    return best[1] if best else None


def _dynamic_pricing_fetch_community(community, unknown_only=False):
    """GET the matrix version corresponding to the latest Entrata MITS sync."""
    building_id = str(community.get('BUILDING_ID') or '')
    latest_sync = None
    snapshot_link = ''
    try:
        snapshot, latest_sync, snapshot_link = (
            _dynamic_pricing_latest_mits_sync(community))
        if latest_sync is None:
            return {
                'buildingId': building_id,
                'buildingName': community.get('BUILDING_NAME') or '',
                'excluded': True,
                'error': None,
            }
        return _dynamic_pricing_fetch_community_snapshot(
            community, snapshot, latest_sync, snapshot_link,
            unknown_only=unknown_only)
    except ClientError as exc:
        code = str((exc.response.get('Error') or {}).get('Code') or '')
        if code in ('NoSuchKey', '404', 'NotFound'):
            return {
                'buildingId': building_id,
                'buildingName': community.get('BUILDING_NAME') or '',
                'excluded': True,
                'error': None,
            }
        return {
            'buildingId': building_id,
            'buildingName': community.get('BUILDING_NAME') or '',
            'orgId': community.get('ORG_ID'),
            'orgName': community.get('ORG_NAME') or '',
            'cadenceDays': None,
            'cadence': 'Unavailable',
            'unitCount': 0,
            'priceChangeDates': [],
            'newApiCalls': 0,
            'currentApiCalls': 0,
            'apiCallsSaved': 0,
            'latestSync': (
                latest_sync.isoformat()
                if hasattr(latest_sync, 'isoformat') else latest_sync),
            'snapshotLink': snapshot_link,
            'units': [],
            'excluded': False,
            'error': str(exc),
        }
    except (ValueError, TypeError, UnicodeError, gzip_module.BadGzipFile):
        return {
            'buildingId': building_id,
            'buildingName': community.get('BUILDING_NAME') or '',
            'excluded': True,
            'error': None,
        }
    except Exception as exc:
        return {
            'buildingId': building_id,
            'buildingName': community.get('BUILDING_NAME') or '',
            'orgId': community.get('ORG_ID'),
            'orgName': community.get('ORG_NAME') or '',
            'cadenceDays': None,
            'cadence': 'Unavailable',
            'unitCount': 0,
            'priceChangeDates': [],
            'newApiCalls': 0,
            'currentApiCalls': 0,
            'apiCallsSaved': 0,
            'latestSync': (
                latest_sync.isoformat()
                if hasattr(latest_sync, 'isoformat') else latest_sync),
            'snapshotLink': snapshot_link,
            'units': [],
            'excluded': False,
            'error': str(exc),
        }


def _dynamic_pricing_fetch_community_snapshot(
        community, snapshot, latest_sync, snapshot_link='',
        unknown_only=False):
    """Analyze one community using a specific successful MITS snapshot."""
    building_id = str(community.get('BUILDING_ID') or '')
    key = f'building_{building_id}.json'
    version = _dynamic_pricing_matrix_version_for_sync(key, latest_sync)
    if version is None:
        return {
            'buildingId': building_id,
            'buildingName': community.get('BUILDING_NAME') or '',
            'excluded': True,
            'error': None,
        }
    response = s3().get_object(
        Bucket=DYNAMIC_PRICING_BUCKET,
        Key=key,
        VersionId=version['VersionId'])
    raw = response['Body'].read()
    if raw[:2] == b'\x1f\x8b':
        raw = gzip_module.decompress(raw)
    payload = json.loads(raw.decode('utf-8'))
    unit_details = _dynamic_pricing_snapshot_unit_details(
        building_id, snapshot)
    return _dynamic_pricing_analyze_payload(
        community, payload, latest_sync, snapshot_link, unit_details,
        unknown_only=unknown_only)


def _dynamic_pricing_fetch_saved_validation_community(summary):
    """Rebuild visualizer data from the exact sync recorded in validation."""
    building_id = str(summary.get('buildingId') or '')
    raw_sync = summary.get('latestSync')
    if not building_id or not raw_sync:
        raise ValueError('saved validation row has no sync reference')
    latest_sync = datetime.fromisoformat(
        str(raw_sync).replace('Z', '+00:00'))
    if latest_sync.tzinfo is None:
        latest_sync = latest_sync.replace(tzinfo=timezone.utc)
    else:
        latest_sync = latest_sync.astimezone(timezone.utc)

    entity = f'building_{building_id}'
    entity_prefix = f'{ROOT}Entrata/{entity}/'
    snapshot_prefix = _snapshot_prefix_nearest(
        entity_prefix, latest_sync, max_skew_minutes=1)
    if not snapshot_prefix:
        raise ValueError('the saved MITS snapshot is no longer available')
    snapshot = snapshot_prefix[len(entity_prefix):].rstrip('/')
    snapshot_sync = _snapshot_dt(snapshot)
    if abs((snapshot_sync - latest_sync).total_seconds()) > 60:
        raise ValueError('could not match the saved MITS sync exactly')

    community = {
        'BUILDING_ID': building_id,
        'BUILDING_NAME': summary.get('buildingName') or '',
        'ORG_ID': summary.get('orgId'),
        'ORG_NAME': summary.get('orgName') or '',
    }
    snapshot_link = (
        summary.get('snapshotLink')
        or _snapshot_link(entity, snapshot, summary.get('orgId')))
    row = _dynamic_pricing_fetch_community_snapshot(
        community, snapshot, snapshot_sync, snapshot_link)
    if row.get('excluded'):
        raise ValueError('the saved sync has no valid multi-day pricing matrix')
    if row.get('error'):
        raise ValueError(row['error'])
    try:
        _dynamic_pricing_apply_unit_numbers([row])
    except Exception:
        # Snapshot unit numbers are normally already present. Falling back to
        # source IDs should not prevent algorithm playback.
        pass
    return row


def _dynamic_pricing_sorted_rows(rows):
    return sorted(rows, key=lambda row: (
        -(row.get('apiCallsSaved') or 0),
        (row.get('buildingName') or '').casefold(),
        row.get('buildingId') or '',
    ))


def _dynamic_pricing_search_communities(
        limit: int, org_ids=None, community_ids=None):
    """Return the configured Entrata dynamic-pricing community population."""
    org_ids = org_ids or []
    community_ids = community_ids or []
    search_predicates = []
    query_params = []
    if org_ids:
        placeholders = ', '.join('%s' for _ in org_ids)
        search_predicates.append(f'b.ORG_ID IN ({placeholders})')
        query_params.extend(org_ids)
    if community_ids:
        placeholders = ', '.join('%s' for _ in community_ids)
        search_predicates.append(f'b.ID IN ({placeholders})')
        query_params.extend(community_ids)
    search_filter = (
        f"AND ({' OR '.join(search_predicates)})"
        if search_predicates else '')
    return snowflake_db.query(
        _DYNAMIC_PRICING_COMMUNITIES_SQL.format(
            search_filter=search_filter, limit=int(limit)),
        params=query_params or None,
        timeout=SYNC_ISSUES_QUERY_TIMEOUT)


def _dynamic_pricing_validation_row(row):
    """Keep the evidence needed to inspect one Unknown-mode validation."""
    unknown_plan = ((row.get('retrievalPlans') or {}).get('unknown') or {})
    incorrect_cell_count = len(unknown_plan.get('incorrectCells') or [])
    return {
        'buildingId': row.get('buildingId'),
        'buildingName': row.get('buildingName'),
        'orgId': row.get('orgId'),
        'orgName': row.get('orgName'),
        'latestSync': row.get('latestSync'),
        'snapshotLink': row.get('snapshotLink'),
        'cadence': row.get('cadence'),
        'cadenceDays': row.get('cadenceDays'),
        'cadenceIsLowerBound': bool(row.get('cadenceIsLowerBound')),
        'unitCount': row.get('unitCount') or 0,
        'currentApiCalls': row.get('currentApiCalls') or 0,
        'unknownBootstrapApiCalls': row.get('unknownBootstrapApiCalls') or 0,
        'unknownApiCallsSaved': row.get('unknownApiCallsSaved') or 0,
        'unknownApiCallsSavedPct': row.get('unknownApiCallsSavedPct'),
        'unknownReconstructionAccuracyPct': (
            row.get('unknownReconstructionAccuracyPct')),
        'matrixCells': sum(
            unit.get('pricingDateCount') or 0
            for unit in (row.get('units') or [])),
        'incorrectCellCount': incorrect_cell_count,
        'unknownCadenceStatus': row.get('unknownCadenceStatus'),
        'unknownCadenceCandidateRejections': (
            ((row.get('retrievalPlans') or {}).get('unknown') or {}).get(
                'cadenceCandidateRejections') or []),
        'unknownCadenceInvalidations': (
            ((row.get('retrievalPlans') or {}).get('unknown') or {}).get(
                'cadenceInvalidations') or []),
    }


def _dynamic_pricing_fetch_validation_community(community):
    """Fetch and score one matrix, returning only batch-validation fields."""
    row = _dynamic_pricing_fetch_community(community, True)
    if row.get('excluded') or row.get('error'):
        return {
            'excluded': bool(row.get('excluded')),
            'error': row.get('error'),
        }
    summary = _dynamic_pricing_validation_row(row)
    plan = ((row.get('retrievalPlans') or {}).get('unknown') or {})
    return {
        'excluded': False,
        'error': None,
        'summary': summary,
        'cadenceDays': row.get('cadenceDays'),
        'algorithmInputComplete': row.get('algorithmInputComplete', True),
        'hasMissingAvailability': any(
            not unit.get('availableDate') for unit in (row.get('units') or [])),
        'matrixCells': summary['matrixCells'],
        'incorrectCells': plan.get('incorrectCells') or [],
        'cadenceEvidence': plan.get('cadenceEvidence'),
    }


def _dynamic_pricing_write_validation_result(job_id, result):
    """Persist a validation result atomically for later UI inspection."""
    os.makedirs(EXPORT_DIR, exist_ok=True)
    path = os.path.join(EXPORT_DIR, f'{job_id}.json')
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as fh:
        json.dump(result, fh, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def _dynamic_pricing_apply_unit_numbers(rows):
    """Replace matrix unit IDs with unit numbers from Snowflake in batches."""
    source_ids = sorted({
        int(unit['sourceUnitId'])
        for row in rows
        for unit in (row.get('units') or [])
        if str(unit.get('sourceUnitId') or '').isdigit()
        and str(unit.get('unitId') or '') == str(unit.get('sourceUnitId') or '')
    })
    number_by_id = {}
    chunk_size = 1000
    for offset in range(0, len(source_ids), chunk_size):
        chunk = source_ids[offset:offset + chunk_size]
        placeholders = ', '.join('%s' for _ in chunk)
        mapped = snowflake_db.query(
            'SELECT ID AS UNIT_ID, UNIT_NUMBER '
            'FROM ELISE.FANSCAN_LOGICAL_PUBLIC.UNIT_DETAILS '
            f'WHERE ID IN ({placeholders})',
            params=chunk,
            timeout=SYNC_ISSUES_QUERY_TIMEOUT)
        for item in mapped:
            unit_number = item.get('UNIT_NUMBER')
            if unit_number not in (None, ''):
                number_by_id[str(item.get('UNIT_ID'))] = str(unit_number)
    for row in rows:
        for unit in (row.get('units') or []):
            source_id = str(unit.get('sourceUnitId') or '')
            unit['unitId'] = number_by_id.get(source_id, unit['unitId'])


def _run_dynamic_pricing_job(
        job_id: str, limit: int, org_ids=None, community_ids=None):
    try:
        _job_update(job_id, note='Finding Entrata communities in Snowflake…')
        communities = _dynamic_pricing_search_communities(
            limit, org_ids, community_ids)
        total = len(communities)
        _job_update(job_id, total=total,
                    note=(f'Matching the latest successful MITS sync to a pricing '
                          f'matrix for {total} communities…'))

        rows = []
        progress = {'done': 0, 'excluded': 0}
        lock = threading.Lock()

        def fetch(community):
            row = _dynamic_pricing_fetch_community(community)
            with lock:
                progress['done'] += 1
                if row.get('excluded'):
                    progress['excluded'] += 1
                else:
                    rows.append(row)
                done = progress['done']
                ordered = _dynamic_pricing_sorted_rows(rows)
                errors = sum(1 for item in rows if item.get('error'))
                _job_update(job_id, done=done, result={
                    'partial': True,
                    'rows': ordered,
                    'communities': total,
                    'analyzed': done,
                    'excluded': progress['excluded'],
                    'errors': errors,
                }, note=f'{done}/{total} communities analyzed')

        max_workers = min(DYNAMIC_PRICING_WORKERS, max(total, 1))
        with ThreadPoolExecutor(max_workers=max_workers) as pool:
            list(pool.map(fetch, communities))

        unit_number_error = None
        try:
            _job_update(job_id, note='Resolving unit numbers in Snowflake…')
            _dynamic_pricing_apply_unit_numbers(rows)
        except Exception as exc:
            # The report remains useful with matrix IDs if this optional label
            # lookup fails, so keep the successfully analyzed pricing rows.
            unit_number_error = str(exc)

        ordered = _dynamic_pricing_sorted_rows(rows)
        errors = sum(1 for item in ordered if item.get('error'))
        _job_update(job_id, status='done', done=total,
                    finished=time.time(), result={
                        'partial': False,
                        'rows': ordered,
                        'communities': total,
                        'analyzed': total,
                        'excluded': progress['excluded'],
                        'errors': errors,
                        'unitNumberError': unit_number_error,
                    }, note=f'{total} communities analyzed')
    except Exception as exc:
        _job_update(job_id, status='error', error=str(exc),
                    finished=time.time())


def _run_dynamic_pricing_validation_job(
        job_id: str, limit: int, org_ids=None, community_ids=None):
    """Test Unknown mode causally across the complete selected population."""
    started = time.time()
    try:
        _job_update(
            job_id,
            note='Finding Entrata dynamic-pricing communities in Snowflake…')
        candidates = _dynamic_pricing_search_communities(
            limit + 1, org_ids, community_ids)
        population_truncated = len(candidates) > limit
        communities = candidates[:limit]
        total = len(communities)
        _job_update(
            job_id, total=total,
            note=(f'Validating Unknown mode against {total} latest-sync '
                  'pricing matrices, including cadence = 1…'))

        rows = []
        completed = excluded = errors = cadence_one_tested = no_cadence = 0
        missing_availability = 0
        counterexample = None
        counterexamples = []
        matrices_passed = matrices_failed = 0
        cells_tested = incorrect_cells = 0

        def result_payload(partial):
            cadence_corrections = [
                {
                    'buildingId': row.get('buildingId'),
                    'buildingName': row.get('buildingName'),
                    'orgId': row.get('orgId'),
                    'orgName': row.get('orgName'),
                    'candidateRejections': row.get(
                        'unknownCadenceCandidateRejections') or [],
                    'invalidations': row.get(
                        'unknownCadenceInvalidations') or [],
                }
                for row in rows
                if (row.get('unknownCadenceCandidateRejections')
                    or row.get('unknownCadenceInvalidations'))
            ]
            if partial:
                validation_status = 'running'
                confidence = 'Validation is still running.'
            elif counterexample is not None:
                validation_status = 'failed'
                confidence = (
                    f'{matrices_failed:,} counterexample'
                    f'{"s" if matrices_failed != 1 else ""} found across '
                    f'all {len(rows):,} tested matrices. Unknown mode did not '
                    'reconstruct every complete matrix at 100% accuracy.')
            elif errors:
                validation_status = 'incomplete'
                confidence = (
                    f'No counterexample found in {len(rows):,} tested '
                    f'matrices, but {errors:,} retrieval error'
                    f'{"s" if errors != 1 else ""} prevented full confidence.')
            elif population_truncated:
                validation_status = 'sample-passed'
                confidence = (
                    f'No counterexample found in the configured sample of '
                    f'{len(rows):,} matrices with an available cadence.')
            else:
                validation_status = 'passed'
                confidence = (
                    f'No counterexample found across all {len(rows):,} '
                    'input-complete matrices with an available cadence in the selected '
                    'latest-sync population. Matrices missing required unit '
                    'availability metadata are reported separately.')
            return {
                'kind': 'dynamic_pricing_validation',
                'partial': partial,
                'validationStatus': validation_status,
                'confidence': confidence,
                'communitiesConsidered': total,
                'communitiesCompleted': completed,
                'matricesTested': len(rows),
                'matricesPassed': matrices_passed,
                'matricesFailed': matrices_failed,
                'cellsTested': cells_tested,
                'incorrectCells': incorrect_cells,
                'overallReconstructionAccuracyPct': round(
                    100 * (cells_tested - incorrect_cells) / cells_tested, 6)
                    if cells_tested else 0.0,
                'cadenceOneSkipped': 0,
                'cadenceOneTested': cadence_one_tested,
                'cadenceUnavailableSkipped': no_cadence,
                'missingAvailabilitySkipped': missing_availability,
                'excluded': excluded,
                'errors': errors,
                'populationTruncated': population_truncated,
                'stoppedOnCounterexample': False,
                'counterexample': counterexample,
                'counterexamples': counterexamples,
                'cadenceCorrections': cadence_corrections,
                'rows': sorted(rows, key=lambda item: (
                    item.get('orgName') or '',
                    item.get('buildingName') or '',
                    item.get('buildingId') or '')),
                'startedAt': datetime.fromtimestamp(
                    started, timezone.utc).isoformat(),
                'finishedAt': (None if partial else datetime.now(
                    timezone.utc).isoformat()),
                'durationSeconds': round(time.time() - started, 1),
            }

        max_workers = min(
            DYNAMIC_PRICING_VALIDATION_WORKERS, max(total, 1))
        pool = ProcessPoolExecutor(max_workers=max_workers)
        pending = {}
        iterator = iter(communities)

        def submit_next():
            try:
                community = next(iterator)
            except StopIteration:
                return False
            pending[pool.submit(
                _dynamic_pricing_fetch_validation_community,
                community)] = community
            return True

        for _ in range(max_workers):
            if not submit_next():
                break

        while pending:
            finished, _waiting = wait(
                tuple(pending), return_when=FIRST_COMPLETED)
            for future in finished:
                community = pending.pop(future, None)
                completed += 1
                try:
                    result = future.result()
                except Exception:
                    errors += 1
                    submit_next()
                    continue
                row = result.get('summary') or {}
                if result.get('excluded'):
                    excluded += 1
                elif result.get('error'):
                    errors += 1
                else:
                    cadence = result.get('cadenceDays')
                    if not isinstance(cadence, (int, float)):
                        no_cadence += 1
                    elif (not result.get('algorithmInputComplete', True)
                          or result.get('hasMissingAvailability')):
                        # Availability date is an explicit algorithm input. A
                        # matrix with missing metadata, or pricing that begins
                        # entirely after the availability-derived hold window,
                        # cannot be reconstructed causally from the permitted
                        # inputs. Report it separately from algorithm accuracy.
                        missing_availability += 1
                    else:
                        if cadence == 1:
                            cadence_one_tested += 1
                        rows.append(row)
                        accuracy = row.get('unknownReconstructionAccuracyPct')
                        matrix_cells = result.get('matrixCells') or 0
                        matrix_incorrect = len(
                            result.get('incorrectCells') or [])
                        cells_tested += matrix_cells
                        incorrect_cells += matrix_incorrect
                        if accuracy != 100:
                            matrices_failed += 1
                            if counterexample is None:
                                counterexample = dict(row)
                                counterexample['incorrectCells'] = (
                                    result.get('incorrectCells') or [])
                                counterexample['cadenceEvidence'] = (
                                    result.get('cadenceEvidence'))
                            counterexamples.append({
                                'buildingId': row.get('buildingId'),
                                'buildingName': row.get('buildingName'),
                                'orgId': row.get('orgId'),
                                'orgName': row.get('orgName'),
                                'cadence': row.get('cadence'),
                                'cadenceDays': row.get('cadenceDays'),
                                'reconstructionAccuracyPct': accuracy,
                                'incorrectCells': matrix_incorrect,
                            })
                        else:
                            matrices_passed += 1
                submit_next()

            partial = result_payload(True)
            _job_update(
                job_id, done=completed, result=partial,
                note=(f'{completed}/{total} communities checked · '
                      f'{len(rows)} matrices tested'))

        pool.shutdown(wait=True, cancel_futures=True)

        final = result_payload(False)
        _dynamic_pricing_write_validation_result(job_id, final)
        _history_record(
            job_id, 'dynamic_pricing_validation', final, {
                'validationStatus': final['validationStatus'],
                'communitiesConsidered': total,
                'matricesTested': final['matricesTested'],
                'cadenceOneSkipped': 0,
                'cadenceOneTested': cadence_one_tested,
                'missingAvailabilitySkipped': missing_availability,
                'errors': errors,
                'populationTruncated': population_truncated,
            })
        _job_update(
            job_id, status='done', done=completed, finished=time.time(),
            result=final,
            note=(f'{final["matricesTested"]} matrices tested · '
                  f'{final["validationStatus"].replace("-", " ")}'))
    except Exception as exc:
        _job_update(job_id, status='error', error=str(exc),
                    finished=time.time())


def _run_sync_issues_analyze_job(job_id: str, syncs: list):
    """
    For each sync result, run availability rules and aggregate reasons for
    stage-9 predictions.  Uses pre-loaded local index files to avoid per-building
    S3 list operations, and deduplicates syncs by building so each building is
    only downloaded once regardless of how many syncs it appears in.
    """
    try:
        _job_update(job_id, total=len(syncs), note='Loading integration indexes…')

        # ── Pre-load rules and index files once (fast local reads) ────────────
        all_rules = _availability_rules().get('integrations', {})
        integration_indexes: dict[str, dict] = {}
        missing_from_index: set[str] = set()
        for intg in all_rules:
            data = _index_load(intg)
            if data:
                integration_indexes[intg] = data.get('entities', {})

        # Indexes for the supplemental PMS feeds (e.g. Voyager AllUnits_Login),
        # used to tell "dropped from the RentCafe feed" apart from "blank status".
        supplemental_indexes: dict[str, dict] = {}
        for _r in all_rules.values():
            for rel in (_r.get('supplemental_units') or {}).get('integrations') or []:
                if rel not in supplemental_indexes:
                    rel_data = _index_load(rel)
                    supplemental_indexes[rel] = (
                        (rel_data or {}).get('entities', {})
                        if isinstance(rel_data, dict) else {})

        # ── Deduplicate by building_id so each building is processed once ─────
        seen: set[str] = set()
        deduped: list[dict] = []
        for s in syncs:
            bid = str(s.get('BUILDING_ID') or '')
            if bid and bid not in seen:
                seen.add(bid)
                deduped.append(s)
        n_total = len(deduped)
        dedup_saved = len(syncs) - n_total

        dedup_note = (f'Deduplicated to {n_total} unique buildings'
                      f' (skipping {dedup_saved} duplicate syncs)')
        _job_update(job_id, total=n_total, note=dedup_note)

        # ── Rollout / building metadata (matches the Availability Agent) ──────
        # Overrides such as AppFolio "Not Posted to Website" and RealPage
        # "Exclude Not Rent Ready Units" read org-level rollout variants and
        # building flags that only Snowflake/DynamoDB can answer.  Resolve them
        # once, up front, so each probe thread reads a plain dict.
        meta_entities: dict[str, datetime] = {}
        rollout_names_needed: set[str] = set()
        for _s in deduped:
            _intg, _entity, _as_of = _sync_issues_target(_s)
            if not _intg or not _entity:
                continue
            _r = all_rules.get(_intg) or {}
            _names = list(_r.get('rollouts') or {})
            if _names or (_r.get('building_fields') or []):
                meta_entities[_entity] = _as_of or datetime.now(timezone.utc)
                rollout_names_needed.update(_names)

        building_meta: dict = {}
        rollout_values: dict = {}
        rollout_error = None
        enrich_error = None
        if meta_entities:
            _job_update(job_id, note=(
                f'Loading building metadata for {len(meta_entities)} '
                f'rollout-dependent buildings…'))
            building_meta, col_map, enrich_error = _enrich_with_snowflake(
                job_id, list(meta_entities),
                timeout=SYNC_ISSUES_ENRICH_TIMEOUT)
            building_meta = building_meta or {}
            if rollout_names_needed:
                org_ids = {}
                if enrich_error:
                    rollout_error = (
                        f'organization lookup unavailable: {enrich_error}')
                elif building_meta and col_map and col_map.get('org'):
                    org_ids = {e: d.get(col_map['org'])
                               for e, d in building_meta.items()}
                try:
                    rollout_values = snowflake_db.rollout_variants(
                        list(meta_entities), sorted(rollout_names_needed),
                        meta_entities, org_ids)
                except Exception as exc:
                    # Keep the run usable, but leave rollout state unknown so a
                    # rollout-dependent override is not applied speculatively.
                    rollout_error = (str(exc) if not rollout_error
                                     else f'{rollout_error}; {exc}')

        reason_counts: dict[str, int] = {}
        reason_counts_new: dict[str, int] = {}
        by_integration: dict[str, int] = {}
        by_integration_new: dict[str, int] = {}
        building_details: dict[str, dict] = {}
        total_analyzed = 0
        stage_9_count = 0
        newly_marked_count = 0
        baseline_missing = 0
        skipped = 0
        lock = threading.Lock()
        counter = {'n': 0}

        def _finish(sync, skip_reason=None, local_analyzed=0, local_stage9=0,
                    local_reasons=None, local_units=None, intg=None,
                    snapshot=None, local_reasons_new=None, local_new=0,
                    baseline_snapshot=None, baseline_available=False):
            """Thread-safe counter / progress — called once per probe call."""
            nonlocal total_analyzed, stage_9_count, skipped
            nonlocal newly_marked_count, baseline_missing
            with lock:
                counter['n'] += 1
                if skip_reason:
                    skipped += 1
                else:
                    total_analyzed += local_analyzed
                    stage_9_count += local_stage9
                    newly_marked_count += local_new
                    if not baseline_available:
                        baseline_missing += 1
                    if intg:
                        by_integration[intg] = (
                            by_integration.get(intg, 0) + local_stage9)
                        by_integration_new[intg] = (
                            by_integration_new.get(intg, 0) + local_new)
                    for r, c in (local_reasons or {}).items():
                        reason_counts[r] = reason_counts.get(r, 0) + c
                    for r, c in (local_reasons_new or {}).items():
                        reason_counts_new[r] = reason_counts_new.get(r, 0) + c

                bid = str(sync.get('BUILDING_ID') or f'_{counter["n"]}')
                building_details[bid] = _sync_issues_building_detail(
                    sync, integration=intg, snapshot=snapshot,
                    skip_reason=skip_reason, stage_9=local_stage9,
                    analyzed=local_analyzed, reasons=local_reasons,
                    units=local_units, reasons_new=local_reasons_new,
                    newly_marked=local_new,
                    baseline_snapshot=baseline_snapshot,
                    baseline_available=baseline_available,
                    excluded_from_issues=(
                        skip_reason == 'No pre-sync snapshot found'))

                # Publish a live partial result on every completion so the
                # frontend can render an updating distribution table.
                partial = _sync_issues_partial_result(
                    reason_counts, by_integration, stage_9_count,
                    total_analyzed, counter['n'], n_total, skipped,
                    buildings=building_details,
                    reason_counts_new=reason_counts_new,
                    newly_marked_count=newly_marked_count,
                    by_integration_new=by_integration_new,
                    baseline_missing=baseline_missing,
                    rollout_error=rollout_error, enrich_error=enrich_error)
                _job_update(
                    job_id, done=counter['n'], result=partial,
                    note=(f'{counter["n"]}/{n_total} buildings · '
                          f'{newly_marked_count} newly marked / '
                          f'{stage_9_count} unavailable units'
                          + (f' · {len(missing_from_index)} not in index'
                             if missing_from_index else '')))

        def probe(sync):
            sources = str(sync.get('SOURCES') or '')
            integration, entity, as_of = _sync_issues_target(sync)
            if not integration:
                _finish(sync, skip_reason=(
                    f'No availability rules for source "{sources}"'))
                return

            rules = all_rules.get(integration)
            if not rules:
                _finish(sync, skip_reason=(
                    f'No availability rules for integration "{integration}"'))
                return

            source_integration = _availability_source_integration(integration)
            entity_prefix = f'{ROOT}{source_integration}/{entity}/'

            # ── Snapshot selection ────────────────────────────────────────────
            # Always resolve the snapshot by the sync completion timestamp so
            # we analyse the state at the time of the sync, not today's (which
            # may have recovered and have no stage-9 units).  The local index
            # is kept only as a fallback for when we lack a valid timestamp.
            snapshot = None
            snapshot_files = None
            supp_as_of = as_of   # cutoff for the supplemental PMS snapshot

            if as_of is not None:
                # Look for the snapshot that existed just after the sync ran.
                try:
                    snap_prefix = _snapshot_prefix_before(entity_prefix, as_of)
                except Exception:
                    snap_prefix = None
                if snap_prefix:
                    snapshot = snap_prefix[len(entity_prefix):].rstrip('/')
                    try:
                        snapshot_files = _snapshot_files(entity_prefix, snapshot)
                    except Exception:
                        snapshot = None

            if snapshot is None:
                # Fall back to the index's latest snapshot when we can't resolve
                # by time (missing timestamp or no S3 result).
                idx_entry = integration_indexes.get(integration, {}).get(entity)
                if idx_entry:
                    snapshot, snapshot_files = idx_entry[0], list(idx_entry[1])
                else:
                    missing_from_index.add(entity)
                    _finish(sync, intg=integration, skip_reason=(
                        'No snapshot found near the sync time, and the building '
                        'is not in the local index'))
                    return

            # ── Resolve file names ────────────────────────────────────────────
            primary_candidates = rules.get('primary') or []
            actual_candidates  = rules.get('actual') or []
            primary_key        = rules.get('primary_key') or []
            actual_key         = rules.get('actual_key') or []
            primary_fields = list(dict.fromkeys(
                (rules.get('fields') or []) + (rules.get('primary_key') or [])))
            actual_fields = list(dict.fromkeys(
                (rules.get('actual_fields') or
                 ['availability_stage', 'availabilityStage']) +
                (rules.get('actual_key') or []) +
                # Pulled purely for display alongside the join key.
                ['unit_number', 'unitNumber']))

            primary_files  = _availability_primary_files(
                snapshot_files, source_integration, primary_candidates)
            actual_actual  = _availability_first_file(
                snapshot_files, source_integration, actual_candidates)
            if not actual_actual:
                _finish(sync, intg=integration, snapshot=snapshot,
                        skip_reason=(f'Snapshot has no unit-details file '
                                     f'(looked for {", ".join(actual_candidates)})'))
                return

            # ── Fetch files (2 S3 GetObject calls per building) ───────────────
            s3base = f'{ROOT}{source_integration}/{entity}/{snapshot}/'
            try:
                actual_body = _fetch_text(f'{s3base}{actual_actual}')
                actual_rows = _availability_extract(actual_body, actual_fields)
            except Exception as exc:
                _finish(sync, intg=integration, snapshot=snapshot,
                        skip_reason=f'Could not read {actual_actual}: {exc}')
                return

            # A single MITS building can be backed by more than one PMS
            # property (RealPage's getunitlist_<site>, Voyager's
            # AvailableUnits_Login_<property>) -- read every variant, each
            # tagged with its own property code so identities never collide.
            # Voyager's unit_key is (file property code, @IDValue), so
            # without the tag the composite key is None for every row and
            # nothing joins.
            primary_rows = []
            for primary_actual in primary_files:
                try:
                    primary_body = _fetch_text(f'{s3base}{primary_actual}')
                    rows = _availability_extract(
                        primary_body, primary_fields,
                        voyager_units=(integration == 'Voyager'),
                        realpage_units=(integration == 'RealPage'))
                    file_property_code = _availability_file_property_code(
                        primary_actual, primary_candidates)
                    if file_property_code:
                        for row in rows:
                            row['__file_property_code'] = file_property_code
                    primary_rows.extend(rows)
                except Exception:
                    pass

            # ── Supplemental PMS feed (Voyager AllUnits_Login for RentCafe) ───
            # Units the PMS knows about but the availability feed dropped have
            # no status to be blank, so pull them in and mark them explicitly.
            supplemental_config = rules.get('supplemental_units') or {}
            supplemental_targets: list = []
            if supplemental_config:
                try:
                    targets = _availability_supplemental_targets(
                        entity, snapshot, supp_as_of, supplemental_config,
                        supplemental_indexes)
                    supplemental_targets = list(targets)
                    added: list = []
                    for rel_intg, rel_snap, rel_file in targets:
                        supp_body = _fetch_text(
                            f'{ROOT}{rel_intg}/{entity}/{rel_snap}/{rel_file}')
                        code = _availability_file_property_code(
                            rel_file, supplemental_config.get('files') or [])
                        added.extend(_availability_supplemental_rows(
                            supp_body, supplemental_config,
                            primary_rows + added, code))
                    # A legacy unsuffixed Voyager file carries no property code;
                    # inheriting one is only safe for a single-code building.
                    codes = {
                        str(c).strip()
                        for row in primary_rows
                        for c in [_availability_value(row, 'voyagerPropertyCode')]
                        if c is not None and str(c).strip()
                    }
                    if len(codes) == 1:
                        sole_code = next(iter(codes))
                        for row in added:
                            row.setdefault('voyagerPropertyCode', sole_code)
                    primary_rows.extend(added)
                except Exception:
                    # The primary analysis is still useful without the optional
                    # supplement; the rules' own "snapshot missing" reason then
                    # applies to unmatched units.
                    supplemental_targets = []

            # ── Source files declared by the rules ────────────────────────────
            # Overrides such as "Outside Availability Restriction Window" read
            # fields from these files (property_details, floorplans, ...).  The
            # rules cannot fire without them, so load and join them exactly the
            # way the Availability Agent does.
            source_configs = rules.get('sources') or []
            source_fields_map = {
                sc['file']: list(dict.fromkeys(sc.get('fields') or []))
                for sc in source_configs
            }
            source_by_key: dict = {}
            for sc in source_configs:
                # A single MITS building can be backed by more than one PMS
                # property, so every property-code variant of this source is
                # read, each tagged with its own code.
                rows_for_file: list = []
                variants = _availability_matching_files(
                    snapshot_files, source_integration, [sc['file']])
                for variant in variants:
                    try:
                        rows = _availability_extract(
                            _fetch_text(f'{s3base}{variant}'),
                            source_fields_map[sc['file']],
                            voyager_units=(
                                integration == 'Voyager' and
                                sc['file'].startswith(
                                    ('AllUnits_Login', 'AvailableUnits_Login'))),
                            realpage_units=integration == 'RealPage')
                        file_property_code = _availability_file_property_code(
                            variant, [sc['file']])
                        if file_property_code:
                            for row in rows:
                                row['__file_property_code'] = file_property_code
                        rows_for_file.extend(rows)
                    except Exception:
                        pass
                if sc.get('add_missing_as_units') and rows_for_file:
                    # e.g. RealPage's getallunits: a same-integration
                    # all-units feed that carries units getunitlist omits,
                    # keyed by the same raw UnitID.
                    primary_rows.extend(
                        _availability_promote_missing_source_units(
                            primary_rows, rows_for_file, rules))
                # Keyed by (file property code, join-key value): a
                # multi-property-code source must never let one property's
                # row enrich another property's unit just because their
                # local UnitNumber/@IDValue happens to coincide.
                keyed: dict = {}
                join_key = sc.get('join_key')
                for row in rows_for_file:
                    code = row.get('__file_property_code')
                    for key in _availability_keys(row, join_key or []):
                        keyed.setdefault((code, key), row)
                if not join_key:
                    seen_codes = set()
                    for row in rows_for_file:
                        code = row.get('__file_property_code')
                        if code in seen_codes:
                            continue
                        seen_codes.add(code)
                        keyed[(code, '__all__')] = row
                source_by_key[sc['file']] = keyed

            # ── Pre-sync baseline ─────────────────────────────────────────────
            # The snapshot immediately before the one we analysed tells us which
            # units were already unavailable going into this sync, so the caller
            # can look at newly-marked units alone.
            snap_dt  = _availability_snapshot_datetime(snapshot)
            baseline_stage9 = None      # None => baseline unavailable
            baseline_snapshot = None
            if snap_dt is not None:
                try:
                    prev_prefix = _snapshot_prefix_before(
                        entity_prefix, snap_dt - timedelta(microseconds=1),
                        lookback_hours=SYNC_ISSUES_BASELINE_LOOKBACK_HOURS)
                except Exception:
                    prev_prefix = None
                if prev_prefix:
                    prev_snapshot = prev_prefix[len(entity_prefix):].rstrip('/')
                    try:
                        prev_files = _snapshot_files(entity_prefix, prev_snapshot)
                        prev_actual = _availability_first_file(
                            prev_files, source_integration, actual_candidates)
                        if prev_actual:
                            prev_body = _fetch_text(
                                f'{ROOT}{source_integration}/{entity}/'
                                f'{prev_snapshot}/{prev_actual}')
                            prev_rows = _availability_extract(
                                prev_body, actual_fields)
                            baseline_stage9 = set()
                            for prev_row in prev_rows:
                                pv = (prev_row.get('availability_stage')
                                      or prev_row.get('availabilityStage'))
                                try:
                                    if int(pv) != 9:
                                        continue
                                except (TypeError, ValueError):
                                    continue
                                baseline_stage9.update(
                                    _availability_keys(prev_row, actual_key))
                            baseline_snapshot = prev_snapshot
                    except Exception:
                        baseline_stage9 = None
                        baseline_snapshot = None

            # A pre-sync snapshot is required to establish that this sync
            # newly caused the unavailable state.  Without that baseline the
            # Snowflake row is only an unverified candidate, not a Sync Issue.
            if baseline_stage9 is None:
                _finish(sync, intg=integration, snapshot=snapshot,
                        skip_reason='No pre-sync snapshot found')
                return

            # ── Run availability rules ────────────────────────────────────────
            ref_date = (snap_dt.date() if snap_dt
                        else datetime.now(timezone.utc).date())

            # ── Match availability-feed rows to unit_details rows ─────────────
            # Ported from the Availability Agent.  The join key is the rules'
            # composite unit_key (e.g. voyagerPropertyCode-apartmentName, which
            # is the persisted building_unique_id) — NOT the individual key
            # fields — plus the integration-specific bare-id fallbacks.
            actual_by_key: dict = {}
            for idx_a, row_a in enumerate(actual_rows):
                for key in _availability_keys(row_a, actual_key):
                    actual_by_key.setdefault(key, (idx_a, row_a))

            rentcafe_codes = {
                str(code).strip()
                for row in primary_rows
                for code in [_availability_value(row, 'voyagerPropertyCode')]
                if code is not None and str(code).strip()
            } if integration == 'RentCafe' else set()

            phase_fields = (rules.get('unit_key') or {}).get(
                'phase_prefix_when_multiple') or []
            phase_prefix_values = {
                str(v).strip().casefold()
                for row in primary_rows
                for f in phase_fields
                for v in [_availability_value(row, f)]
                if v is not None and str(v).strip()
            }

            required_key = rules.get('required_key') or primary_key
            primary_for_actual: dict = {}
            seen_primary_keys: set = set()
            claimed_actual: set = set()
            for primary_row in primary_rows:
                if required_key and not _availability_keys(primary_row, required_key):
                    continue
                # A wait-list/tour-scheduling placeholder (e.g. Voyager's
                # WAITTOUR) is a genuine row in the raw feed; let it match
                # normally like any other unit. __wait_unit is set from this
                # same raw row below, so the rules can classify it via a
                # declared override.
                unit_key_p = _availability_unit_key(
                    primary_row, rules, phase_prefix_values)
                actual_match = actual_by_key.get(unit_key_p)
                if integration == 'RentCafe':
                    is_supplemental = bool(primary_row.get('__supplemental_unit'))
                    # unit_details may persist only the bare external id; a
                    # single property code makes that unambiguous.
                    if (actual_match is None and
                            (len(rentcafe_codes) == 1 or is_supplemental)):
                        name = (_availability_value(primary_row, 'apartmentName') or
                                _availability_value(primary_row, 'ApartmentName'))
                        name_key = (str(name).strip().casefold()
                                    if name is not None else '')
                        actual_match = actual_by_key.get(name_key)
                        if actual_match is not None and is_supplemental:
                            unit_key_p = name_key
                    if not unit_key_p and not is_supplemental:
                        actual_match = None
                elif integration == 'Voyager' and actual_match is None:
                    property_codes = {
                        code for file_name in snapshot_files
                        for code in [_availability_file_property_code(
                            file_name, primary_candidates)]
                        if code
                    }
                    if len(property_codes) == 1:
                        bare_id = _availability_value(primary_row, '@IDValue')
                        if bare_id is not None:
                            actual_match = actual_by_key.get(
                                str(bare_id).strip().casefold())
                if actual_match is None:
                    continue
                # A canonical identity can repeat in a raw feed; keep the first
                # row deterministically and claim each unit_details row once.
                if unit_key_p and unit_key_p in seen_primary_keys:
                    continue
                idx_a = actual_match[0]
                if idx_a in claimed_actual:
                    continue
                if unit_key_p:
                    seen_primary_keys.add(unit_key_p)
                claimed_actual.add(idx_a)
                primary_for_actual[idx_a] = primary_row

            local_reasons: dict[str, int] = {}
            local_reasons_new: dict[str, int] = {}
            local_units: dict[str, list] = {}
            local_analyzed = 0
            local_stage_9  = 0
            local_new      = 0

            try:
                # unit_details is the canonical physical-unit feed, so iterate
                # it directly and analyse the rows already at stage 9.
                for idx_a, actual_row in enumerate(actual_rows):
                    stage_val = (actual_row.get('availability_stage')
                                 or actual_row.get('availabilityStage'))
                    try:
                        if int(stage_val) != 9:
                            continue
                    except (TypeError, ValueError):
                        continue

                    unit_key_parts = _availability_keys(actual_row, actual_key)
                    unit_key = str(unit_key_parts[0]) if unit_key_parts else None

                    local_stage_9  += 1
                    local_analyzed += 1

                    # Build the rule inputs exactly the way the Availability
                    # Agent does, so every reason comes from the rules alone.
                    p_row = primary_for_actual.get(idx_a, {})
                    if p_row:
                        values = dict(p_row)
                        values['__primary_row'] = True
                        # Wait/tour placeholders are identified from the raw
                        # feed's own identity field only (unit_name_fields),
                        # never from unit_details.
                        values['__wait_unit'] = _availability_wait_unit(
                            p_row, rules)
                        values['__current_date'] = ref_date.isoformat()
                        for k, v in p_row.items():
                            values[f'primary__{k}'] = v
                        for sc in source_configs:
                            related = _availability_source_lookup(
                                source_by_key, sc, p_row, primary_key)
                            if related:
                                for k, v in related.items():
                                    values.setdefault(k, v)
                                for k, v in related.items():
                                    values[f"{sc['file']}__{k}"] = v
                            values[f"__source_present__{sc['file']}"] = bool(related)
                    else:
                        # No primary/supplemental raw-feed match at all, so
                        # there is no raw API data to base a prediction on.
                        # `values` is deliberately NOT seeded from actual_row:
                        # unit_details is the destination this tool models,
                        # and mapping logic may only read raw API data,
                        # rollout state, or Snowflake building info -- never
                        # the destination's own fields. Only the explicit
                        # provenance flags below (derived from the raw-feed
                        # matching outcome, not from any unit_details field
                        # value) can explain such a row.
                        values = {}
                        values['__primary_row'] = False
                        values['__current_date'] = ref_date.isoformat()
                        values['__supplemental_snapshot_missing'] = (
                            not bool(supplemental_targets))
                        values['__supplemental_unit_missing'] = (
                            bool(supplemental_targets))

                    # Rollout variants and building flags, resolved up front
                    # from Snowflake/DynamoDB exactly as the agent does.  A
                    # failed lookup leaves the variant unknown rather than
                    # letting a rollout-dependent override fire speculatively.
                    building_detail = building_meta.get(entity, {})
                    for bfield in (rules.get('building_fields') or []):
                        values[f'__building__{bfield}'] = _availability_value(
                            building_detail, bfield)
                    for rollout_name, rollout_config in (
                            rules.get('rollouts') or {}).items():
                        if rollout_error:
                            variant = '__unknown__'
                        else:
                            variant = rollout_values.get(entity, {}).get(
                                rollout_name,
                                (rollout_config or {}).get('default', 'disabled'))
                        values[f'__rollout__{rollout_name}'] = variant

                    # The rules own every reason.  "Unknown" is permitted in
                    # exactly one case: the rules' predicted stage disagrees
                    # with the unit's actual stage, so they cannot account for
                    # it being unavailable.  Every other outcome must carry the
                    # rule's own reason.
                    try:
                        values['__direct_stage'] = (
                            _availability_direct_prediction(rules, values)[0])
                        predicted, reason = _availability_predict(rules, values)
                    except Exception as exc:
                        predicted = None
                        reason = f'Rule evaluation failed: {exc}'
                    if predicted != 9:
                        label = 'Unknown'          # predicted vs actual mismatch
                    else:
                        # Stages agree, so a reason must come from the rules;
                        # defaulting to "Unknown" here would hide a rules gap.
                        label = (reason or '').strip() or 'No reason given by rule'

                    local_reasons[label] = local_reasons.get(label, 0) + 1

                    # Newly marked by this sync, vs already unavailable before
                    # it.  Unknown when there is no usable baseline snapshot.
                    if baseline_stage9 is None:
                        is_new = None
                    else:
                        is_new = not any(k in baseline_stage9
                                         for k in unit_key_parts)
                    if is_new:
                        local_new += 1
                        local_reasons_new[label] = (
                            local_reasons_new.get(label, 0) + 1)

                    # Record the unit so the UI can list which units carry
                    # each reason.  Prefer a human-meaningful unit name from
                    # the primary row, falling back to the join key.
                    bucket = local_units.setdefault(label, [])
                    if len(bucket) < SYNC_ISSUES_MAX_UNITS_PER_REASON + 1:
                        unit_entry = _sync_issues_unit_label(
                            p_row, actual_row, unit_key, values)
                        unit_entry['isNew'] = is_new
                        bucket.append(unit_entry)
            except Exception:
                pass  # keep partial results; don't crash the job

            _finish(sync, local_analyzed=local_analyzed,
                    local_stage9=local_stage_9, local_reasons=local_reasons,
                    local_units=local_units, intg=integration,
                    snapshot=snapshot, local_reasons_new=local_reasons_new,
                    local_new=local_new, baseline_snapshot=baseline_snapshot,
                    baseline_available=baseline_stage9 is not None)

        max_w = min(16, max(n_total, 1))
        with ThreadPoolExecutor(max_workers=max_w) as pool:
            list(pool.map(probe, deduped))

        final = _sync_issues_partial_result(
            reason_counts, by_integration, stage_9_count,
            total_analyzed, n_total, n_total, skipped, partial=False,
            buildings=building_details, reason_counts_new=reason_counts_new,
            newly_marked_count=newly_marked_count,
            by_integration_new=by_integration_new,
            baseline_missing=baseline_missing,
            rollout_error=rollout_error, enrich_error=enrich_error)
        final['originalSyncs'] = len(syncs)
        final['deduplicatedBuildings'] = n_total
        _job_update(job_id, status='done', done=n_total,
                    finished=time.time(), result=final)
    except Exception as e:
        _job_update(job_id, status='error', error=str(e), finished=time.time())


# ── Routes ────────────────────────────────────────────────────────────────────

@app.route('/')
def index():
    return send_from_directory('static', 'index.html')


@app.route('/api/connect', methods=['POST'])
def connect():
    global _connected, _client
    load_dotenv(override=True)
    try:
        _client = None   # rebuild with refreshed credentials
        sts = boto3.client('sts', region_name=REGION)
        identity = sts.get_caller_identity()
        s3().head_bucket(Bucket=BUCKET)
        _connected = True
        _cache.clear()
        snowflake_db.reset()   # pick up any credential changes too
        return jsonify({
            'ok': True,
            'identity': identity.get('Arn', ''),
            'bucket': BUCKET,
            'region': REGION,
            'snowflake': snowflake_db.configured(),
        })
    except Exception as e:
        _connected = False
        return jsonify({'ok': False, 'error': str(e)}), 400


@app.route('/api/browse')
def browse():
    if not _connected:
        return jsonify({'error': 'Not connected'}), 401

    prefix = request.args.get('prefix', ROOT)
    if not prefix.startswith(ROOT):
        prefix = ROOT

    try:
        depth = _depth(prefix)

        # ── Entity level: auto-select the latest snapshot ──────────────────
        if depth == 2:
            cached = _cache_get(prefix + '__latest__')
            if not cached:
                snap_prefix = _latest_snapshot_prefix(prefix)
                if snap_prefix is None:
                    return jsonify({'prefix': prefix, 'folders': [], 'files': [],
                                    'noSnapshots': True})

                resp = s3().list_objects_v2(Bucket=BUCKET, Delimiter='/', Prefix=snap_prefix)
                files = [
                    {
                        'name':         obj['Key'][len(snap_prefix):],
                        'key':          obj['Key'],
                        'size':         obj['Size'],
                        'lastModified': obj['LastModified'].isoformat(),
                    }
                    for obj in resp.get('Contents', [])
                    if obj['Key'] != snap_prefix
                ]
                cached = {
                    'prefix':       snap_prefix,
                    'autoSnapshot': snap_prefix[len(prefix):].rstrip('/'),
                    'folders':      [],
                    'files':        files,
                }
                _cache_set(prefix + '__latest__', '', cached)
            return jsonify(cached)

        # ── All other depths: exhaust all S3 pages, return everything ─────
        cached = _cache_get(prefix, '')
        if not cached:
            client = s3()
            kwargs = {'Bucket': BUCKET, 'Delimiter': '/', 'Prefix': prefix,
                      'MaxKeys': PAGE_SIZE}
            folders, files = [], []
            while True:
                resp = client.list_objects_v2(**kwargs)
                folders += [
                    {'name': cp['Prefix'][len(prefix):].rstrip('/'), 'prefix': cp['Prefix']}
                    for cp in resp.get('CommonPrefixes', [])
                ]
                files += [
                    {
                        'name':         obj['Key'][len(prefix):],
                        'key':          obj['Key'],
                        'size':         obj['Size'],
                        'lastModified': obj['LastModified'].isoformat(),
                    }
                    for obj in resp.get('Contents', [])
                    if obj['Key'] != prefix
                ]
                if not resp.get('IsTruncated'):
                    break
                kwargs['ContinuationToken'] = resp['NextContinuationToken']

            cached = {'folders': folders, 'files': files}
            _cache_set(prefix, '', cached)

        return jsonify({'prefix': prefix, **cached})

    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/integrations')
def integrations():
    """Source types directly under elise-mits/ — 1 S3 call."""
    if not _connected:
        return jsonify({'error': 'Not connected'}), 401
    try:
        resp = s3().list_objects_v2(Bucket=BUCKET, Delimiter='/', Prefix=ROOT)
        names = sorted(cp['Prefix'][len(ROOT):].rstrip('/')
                       for cp in resp.get('CommonPrefixes', []))
        indexed = set()
        if os.path.isdir(INDEX_DIR):
            indexed = {f[:-len('.json.gz')] for f in os.listdir(INDEX_DIR)
                       if f.endswith('.json.gz')}
        return jsonify({'integrations': names, 'indexed': sorted(indexed),
                        'availabilityIntegrations': sorted(_availability_rules().get('integrations', {}))})
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/filenames')
def filenames():
    """
    File names available for an integration. Uses the full index when one exists;
    otherwise samples a spread of buildings so the dropdown fills in seconds.
    """
    if not _connected:
        return jsonify({'error': 'Not connected'}), 401

    integration = _safe_integration(request.args.get('integration', ''))
    if not integration:
        return jsonify({'error': 'integration required'}), 400

    try:
        data = _index_load(integration)
        if data:
            entities = data.get('entities', {})
            names = {n for _snap, files in entities.values() for n in files}
            return jsonify({'integration': integration, 'fileNames': _display_file_names(integration, names),
                            'buildings': len(entities), 'sampled': False,
                            'index': _index_meta(integration)})

        buildings = _list_buildings(integration)
        if not buildings:
            return jsonify({'integration': integration, 'fileNames': [],
                            'buildings': 0, 'sampled': False,
                            'index': {'state': 'none'}})

        step   = max(1, len(buildings) // SAMPLE_SIZE)
        sample = buildings[::step][:SAMPLE_SIZE]
        stamps = _cutoff_stamps()

        def sample_pass(full_fallback):
            names, hits = set(), 0
            lock = threading.Lock()

            def work(entity):
                nonlocal hits
                try:
                    found = _discover(integration, entity, stamps, full_fallback)
                except Exception:
                    return
                if found:
                    with lock:
                        hits += 1
                        names.update(found[2])

            with ThreadPoolExecutor(max_workers=INDEX_WORKERS) as pool:
                list(pool.map(work, sample))
            return names, hits

        # First pass skips the full-listing fallback so recently-snapshotted
        # integrations stay fast. If nearly every sampled building is stale we
        # learn nothing, so retry with the fallback — bounded by the sample size.
        names, hits = sample_pass(full_fallback=False)
        if hits < min(5, len(sample)):
            names, hits = sample_pass(full_fallback=True)

        return jsonify({
            'integration':  integration,
            'fileNames':    _display_file_names(integration, names),
            'buildings':    len(buildings),
            'sampled':      True,
            'sampleSize':   len(sample),
            'sampleHits':   hits,
            'index':        {'state': 'none'},
        })
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/fields-schema')
def fields_schema():
    """
    Object types (structural paths) and their scalar fields, inferred by
    sampling and parsing real files for one integration+filename — powers the
    Fields-mode dropdown. Requires an index (the sample is drawn from the
    index's building list) since without it there's no cheap way to find
    which buildings even have this file.
    """
    if not _connected:
        return jsonify({'error': 'Not connected'}), 401

    integration = _safe_integration(request.args.get('integration', ''))
    file_name   = request.args.get('filename', '')
    if not integration:
        return jsonify({'error': 'integration required'}), 400
    if not file_name or '/' in file_name:
        return jsonify({'error': 'filename required'}), 400
    file_name = _canonical_file_name(integration, file_name)
    if not _index_load(integration):
        return jsonify({'error': 'no-index'}), 409

    try:
        schema = _get_field_schema(integration, file_name,
                                   refresh=request.args.get('refresh') == '1')
        return jsonify({'integration': integration, 'filename': file_name, **schema})
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/index/status')
def index_status():
    integration = _safe_integration(request.args.get('integration', ''))
    if not integration:
        return jsonify({'error': 'integration required'}), 400
    meta = _index_meta(integration)
    job_id = _running_job_for('index', integration)
    if job_id:
        meta['job'] = _job_get(job_id)
    return jsonify(meta)


@app.route('/api/index/build', methods=['POST'])
def index_build():
    if not _connected:
        return jsonify({'error': 'Not connected'}), 401

    body = request.get_json(silent=True) or {}
    integration = _safe_integration(body.get('integration', ''))
    if not integration:
        return jsonify({'error': 'integration required'}), 400
    try:
        sample_percent = int(body.get('samplePercent', 100))
    except (TypeError, ValueError):
        return jsonify({'error': 'samplePercent must be a whole number'}), 400
    if sample_percent < 1 or sample_percent > 100:
        return jsonify({'error': 'samplePercent must be between 1 and 100'}), 400
    try:
        reference_time = _parse_cutoff(
            str(body.get('referenceTime') or '').strip())
    except ValueError as e:
        return jsonify({'error': str(e)}), 400

    existing = _running_job_for('index', integration)
    if existing:
        return jsonify({'jobId': existing, 'alreadyRunning': True})

    job_id = _job_new('index', integration)
    threading.Thread(target=_run_index_job,
                     args=(job_id, integration, sample_percent, reference_time),
                     daemon=True).start()
    return jsonify({'jobId': job_id})


@app.route('/api/index/companion', methods=['POST'])
def index_companion():
    if not _connected:
        return jsonify({'error': 'Not connected'}), 401

    body = request.get_json(silent=True) or {}
    primary = _safe_integration(body.get('integration', ''))
    if primary != 'RentCafe':
        return jsonify({'error': 'Voyager companion indexing requires RentCafe'}), 400
    primary_data = _index_load(primary)
    if not isinstance(primary_data, dict) or not (primary_data.get('entities') or {}):
        return jsonify({'error': 'no-index',
                        'message': 'Build the RentCafe index first'}), 409

    companion = 'YardiVoyager'
    existing = _running_job_for('index', companion)
    if existing:
        return jsonify({'jobId': existing, 'alreadyRunning': True})

    job_id = _job_new('index', companion)
    threading.Thread(target=_run_companion_index_job,
                     args=(job_id, primary, companion), daemon=True).start()
    return jsonify({'jobId': job_id, 'integration': companion})


@app.route('/api/search', methods=['POST'])
def search():
    if not _connected:
        return jsonify({'error': 'Not connected'}), 401

    body        = request.get_json(silent=True) or {}
    integration = _safe_integration(body.get('integration', ''))
    file_name   = body.get('filename', '')
    mode        = body.get('mode') or 'text'
    org         = (body.get('org') or '').strip()
    buildings   = (body.get('buildings') or '').strip()
    as_of_raw   = (body.get('asOf') or '').strip()
    include_students = body.get('includeStudents', False)

    if not isinstance(include_students, bool):
        return jsonify({'error': 'includeStudents must be a boolean'}), 400
    try:
        max_results = _parse_result_limit(body.get('limit'))
    except ValueError as e:
        return jsonify({'error': str(e)}), 400

    if mode not in ('text', 'fields'):
        return jsonify({'error': f'unknown mode {mode!r}'}), 400
    if not integration:
        return jsonify({'error': 'integration required'}), 400
    if not file_name or '/' in file_name:
        return jsonify({'error': 'filename required'}), 400
    file_name = _canonical_file_name(integration, file_name)
    if not _index_load(integration):
        return jsonify({'error': 'no-index'}), 409

    try:
        as_of = _parse_cutoff(as_of_raw)
    except ValueError as e:
        return jsonify({'error': str(e)}), 400

    if mode == 'fields':
        unique = body.get('unique', False)
        if not isinstance(unique, bool):
            return jsonify({'error': 'unique must be a boolean'}), 400
        raw_fields = body.get('fields') or []
        if not isinstance(raw_fields, list):
            return jsonify({'error': 'fields must be a list'}), 400
        # Each item is either a plain string (manually typed — matched by
        # name wherever it occurs) or {'name','path'} (picked from the schema
        # dropdown — matched only at that exact object type). Deduplication
        # and column-collision handling happens once, inside the job, so the
        # route and the job never disagree about what "the fields" are.
        if not any(
            (isinstance(f, str) and f.strip())
            or (isinstance(f, dict) and (f.get('name') or '').strip())
            for f in raw_fields
        ):
            return jsonify({'error': 'at least one field is required'}), 400

        try:
            primary_array_expansions = _normalize_array_expansion_requests(
                body.get('arrayExpansions') or [])
            related_files = _normalize_related_files(body.get('relatedFiles') or [], integration)
            conditions = _normalize_conditions(body.get('conditions') or [], integration, related_files)
            normalized_output_fields = _normalize_field_specs(raw_fields)
            for rel in related_files:
                _validate_join_object_scope(
                    rel['primaryJoin'], normalized_output_fields,
                    f'Primary join field for {rel["filename"]!r}')
                _validate_join_object_scope(
                    rel['relatedJoin'], rel['fields'],
                    f'Related join field for {rel["filename"]!r}')
        except ValueError as e:
            return jsonify({'error': str(e)}), 400
        if any(rel['filename'] == file_name for rel in related_files):
            return jsonify({'error': 'a related file must differ from the primary file'}), 400
        missing_related_indexes = sorted({rel['integration'] for rel in related_files
                                          if not _index_load(rel['integration'])})
        if missing_related_indexes:
            return jsonify({'error': 'no-index',
                            'message': 'Build an index for related integration(s): ' +
                                       ', '.join(missing_related_indexes)}), 409

        job_id = _job_new('fields', integration)
        threading.Thread(target=_run_fields_job,
                         args=(job_id, integration, file_name, raw_fields, org, buildings, as_of,
                               include_students, max_results, unique,
                               primary_array_expansions, related_files,
                               body.get('conditions') or []),
                         daemon=True).start()
        return jsonify({'jobId': job_id, 'asOf': as_of.isoformat() if as_of else None})

    text = body.get('text', '')
    if not text:
        return jsonify({'error': 'text required'}), 400

    job_id = _job_new('search', integration)
    threading.Thread(target=_run_search_job,
                     args=(job_id, integration, file_name, text, org, buildings, as_of,
                           include_students, max_results),
                     daemon=True).start()
    return jsonify({'jobId': job_id, 'asOf': as_of.isoformat() if as_of else None})


@app.route('/api/availability', methods=['POST'])
def availability_agent():
    if not _connected:
        return jsonify({'error': 'Not connected'}), 401
    body = request.get_json(silent=True) or {}
    integration = _safe_integration(body.get('integration', ''))
    supported = _availability_rules().get('integrations', {})
    run_all = integration == '__all__'
    if not run_all and integration not in supported:
        return jsonify({'error': 'Availability Agent does not support this integration'}), 400
    index_scope = sorted(supported) if run_all else [integration]
    index_states = {
        name: _availability_index_freshness(name)[0]
        for name in index_scope
    }
    missing = [name for name, state in index_states.items()
               if state == 'missing']
    if missing:
        return jsonify({
            'error': 'index-required',
            'message': 'Index required (not indexed: ' + ', '.join(missing) + ')',
            'integrations': missing,
        }), 409
    try:
        as_of = _parse_cutoff((body.get('asOf') or '').strip())
    except ValueError as e:
        return jsonify({'error': str(e)}), 400
    show_unknown = body.get('showUnknown', False)
    if not isinstance(show_unknown, bool):
        return jsonify({'error': 'showUnknown must be a boolean'}), 400
    include_students = body.get('includeStudents', False)
    include_applications = body.get('includeApplications', False)
    include_not_launched_on_leasing = body.get('includeNotLaunchedOnLeasing', False)
    if (not isinstance(include_students, bool) or
            not isinstance(include_applications, bool) or
            not isinstance(include_not_launched_on_leasing, bool)):
        return jsonify({'error': ('includeStudents, includeApplications, and '
                                  'includeNotLaunchedOnLeasing must be '
                                  'booleans')}), 400
    try:
        max_results = _parse_result_limit(body.get('limit'))
    except ValueError as e:
        return jsonify({'error': str(e)}), 400

    job_kind = 'availability_batch' if run_all else 'availability'
    existing = _running_job_for(job_kind, integration)
    if existing:
        return jsonify({'jobId': existing, 'alreadyRunning': True})
    job_id = _job_new(job_kind, integration)
    common_args = ((body.get('org') or '').strip(),
                   (body.get('buildings') or '').strip(), as_of, show_unknown,
                   include_students, include_applications,
                   include_not_launched_on_leasing, max_results)
    if run_all:
        threading.Thread(
            target=_run_availability_batch_job,
            args=(job_id, sorted(supported), *common_args),
            daemon=True).start()
    else:
        threading.Thread(target=_run_availability_job,
                         args=(job_id, integration, *common_args),
                         daemon=True).start()
    return jsonify({'jobId': job_id, 'asOf': as_of.isoformat() if as_of else None})


@app.route('/api/history')
def history():
    return jsonify({'entries': _history_entries()})


@app.route('/api/history/<job_id>/favorite', methods=['POST'])
def favorite_history(job_id):
    if not re.fullmatch(r'[0-9a-f]{6,32}', job_id or ''):
        return jsonify({'error': 'invalid job id'}), 400
    payload = request.get_json(silent=True) or {}
    favorite = payload.get('favorite')
    if not isinstance(favorite, bool):
        return jsonify({'error': 'favorite must be a boolean'}), 400
    with _history_lock:
        entries = _history_read()
        entry = next((item for item in entries if item.get('id') == job_id), None)
        if entry is None:
            return jsonify({'error': 'history entry not found'}), 404
        entry['favorite'] = favorite
        _history_write(entries)
    return jsonify({'ok': True, 'favorite': favorite})


@app.route('/api/history/<job_id>/rename', methods=['POST'])
def rename_history(job_id):
    if not re.fullmatch(r'[0-9a-f]{6,32}', job_id or ''):
        return jsonify({'error': 'invalid job id'}), 400
    payload = request.get_json(silent=True) or {}
    name = payload.get('name')
    if not isinstance(name, str) or not name.strip():
        return jsonify({'error': 'name must not be empty'}), 400
    name = name.strip()
    if len(name) > 120:
        return jsonify({'error': 'name must be 120 characters or fewer'}), 400
    with _history_lock:
        entries = _history_read()
        entry = next((item for item in entries if item.get('id') == job_id), None)
        if entry is None:
            return jsonify({'error': 'history entry not found'}), 404
        entry['name'] = name
        _history_write(entries)
    return jsonify({'ok': True, 'name': name})


@app.route('/api/history/<job_id>', methods=['DELETE'])
def delete_history(job_id):
    if not re.fullmatch(r'[0-9a-f]{6,32}', job_id or ''):
        return jsonify({'error': 'invalid job id'}), 400
    with _history_lock:
        entries = _history_read()
        if not any(item.get('id') == job_id for item in entries):
            return jsonify({'error': 'history entry not found'}), 404
        _history_write([item for item in entries if item.get('id') != job_id])
    for extension in ('.csv', '.json'):
        path = os.path.join(EXPORT_DIR, f'{job_id}{extension}')
        try:
            os.remove(path)
        except FileNotFoundError:
            pass
        except OSError as exc:
            return jsonify({'error': f'could not delete export: {exc}'}), 500
    return jsonify({'ok': True})


@app.route('/api/sync-issues/query', methods=['POST'])
def sync_issues_query():
    """Run the Snowflake query and return matching syncs."""
    body = request.get_json(silent=True) or {}

    # Date range
    start_raw = (body.get('startDate') or '').strip()
    end_raw = (body.get('endDate') or '').strip()
    if not start_raw or not end_raw:
        return jsonify({'error': 'startDate and endDate are required'}), 400
    try:
        start_dt = datetime.strptime(start_raw, '%Y-%m-%d').date()
        end_dt   = datetime.strptime(end_raw,   '%Y-%m-%d').date()
    except ValueError:
        return jsonify({'error': 'startDate / endDate must be YYYY-MM-DD'}), 400
    if end_dt < start_dt:
        return jsonify({'error': 'endDate must be on or after startDate'}), 400

    # Integration filter (empty list means all). Accepts the new plural
    # `integrations` array; falls back to the old singular `integration`
    # string for any caller still using the single-select shape.
    integrations_raw = body.get('integrations')
    if integrations_raw is None:
        single = (body.get('integration') or '').strip()
        integrations_raw = [single] if single else []
    if not isinstance(integrations_raw, list):
        return jsonify({'error': 'integrations must be an array of strings'}), 400
    integrations = [str(n).strip() for n in integrations_raw if str(n).strip()]

    # Unavailability threshold (0–1 fraction, default 0.20)
    try:
        threshold = float(body.get('threshold', 0.20))
        if not (0.0 < threshold <= 1.0):
            raise ValueError()
    except (TypeError, ValueError):
        return jsonify({'error': 'threshold must be a number between 0 and 1'}), 400

    # New-import window in minutes (default 1440)
    try:
        new_import_window = int(body.get('newImportWindowMinutes', 1440))
        if new_import_window < 0:
            raise ValueError()
    except (TypeError, ValueError):
        return jsonify({'error': 'newImportWindowMinutes must be a non-negative integer'}), 400

    # Result limit (default 100, max 500)
    try:
        limit = int(body.get('limit', 100))
        limit = max(1, min(limit, 500))
    except (TypeError, ValueError):
        limit = 100

    integration_clause, integration_params = _sync_issues_integration_clause(integrations)

    try:
        import snowflake_db
        rows = snowflake_db.query(
            _SYNC_ISSUES_SQL.format(limit=limit, integration_clause=integration_clause),
            params=(
                start_dt, end_dt,
                *integration_params,
                new_import_window,
                threshold,
            ),
            timeout=SYNC_ISSUES_QUERY_TIMEOUT,
        )
    except Exception as exc:
        return jsonify({'error': str(exc)}), 500

    # Serialize datetime objects so JSON encoding works
    serialized = []
    for row in rows:
        r = {}
        for k, v in row.items():
            if hasattr(v, 'isoformat'):
                r[k] = v.isoformat()
            else:
                r[k] = v
        serialized.append(r)

    return jsonify({'syncs': serialized, 'count': len(serialized)})


@app.route('/api/sync-issues/analyze', methods=['POST'])
def sync_issues_analyze():
    """Start an async job that runs the Availability Agent over a list of syncs."""
    body = request.get_json(silent=True) or {}
    syncs = body.get('syncs')
    if not isinstance(syncs, list) or not syncs:
        return jsonify({'error': 'syncs must be a non-empty array'}), 400
    if len(syncs) > 500:
        return jsonify({'error': 'at most 500 syncs per analysis run'}), 400

    job_id = _job_new('sync_issues_analyze', '')
    threading.Thread(
        target=_run_sync_issues_analyze_job,
        args=(job_id, syncs),
        daemon=True,
    ).start()
    return jsonify({'jobId': job_id})


@app.route('/api/dynamic-pricing/analyze', methods=['POST'])
def dynamic_pricing_analyze():
    """Analyze the pricing matrix matched to each site's latest MITS sync."""
    body = request.get_json(silent=True) or {}
    try:
        limit = int(body.get('limit', 25))
    except (TypeError, ValueError):
        return jsonify({'error': 'limit must be an integer'}), 400
    if not (1 <= limit <= DYNAMIC_PRICING_MAX_COMMUNITIES):
        return jsonify({
            'error': ('limit must be between 1 and '
                      f'{DYNAMIC_PRICING_MAX_COMMUNITIES}')
        }), 400

    raw_org_ids = body.get('orgIds', [])
    if raw_org_ids in (None, ''):
        raw_org_ids = []
    if not isinstance(raw_org_ids, list) or len(raw_org_ids) > 5000:
        return jsonify({
            'error': 'orgIds must be a list of at most 5,000 organization IDs'
        }), 400
    org_ids = []
    seen_org_ids = set()
    for value in raw_org_ids:
        text = str(value).strip()
        if not re.fullmatch(r'\d+', text) or int(text) <= 0:
            return jsonify({
                'error': 'orgIds must contain only positive integer organization IDs'
            }), 400
        org_id = int(text)
        if org_id not in seen_org_ids:
            seen_org_ids.add(org_id)
            org_ids.append(org_id)

    raw_community_ids = body.get('communityIds', [])
    if raw_community_ids in (None, ''):
        raw_community_ids = []
    if (not isinstance(raw_community_ids, list)
            or len(raw_community_ids) > 5000):
        return jsonify({
            'error': ('communityIds must be a list of at most 5,000 '
                      'community IDs')
        }), 400
    community_ids = []
    seen_community_ids = set()
    for value in raw_community_ids:
        text = str(value).strip()
        if not re.fullmatch(r'\d+', text) or int(text) <= 0:
            return jsonify({
                'error': ('communityIds must contain only positive integer '
                          'community IDs')
            }), 400
        community_id = int(text)
        if community_id not in seen_community_ids:
            seen_community_ids.add(community_id)
            community_ids.append(community_id)

    job_id = _job_new('dynamic_pricing', '', total=0)
    threading.Thread(
        target=_run_dynamic_pricing_job,
        args=(job_id, limit, org_ids, community_ids),
        daemon=True,
    ).start()
    return jsonify({'jobId': job_id})


@app.route('/api/dynamic-pricing/validate-unknown', methods=['POST'])
def dynamic_pricing_validate_unknown():
    """Validate Unknown mode across all latest-sync matrices with cadence."""
    body = request.get_json(silent=True) or {}
    try:
        limit = int(body.get('limit', DYNAMIC_PRICING_MAX_COMMUNITIES))
    except (TypeError, ValueError):
        return jsonify({'error': 'limit must be an integer'}), 400
    if not (1 <= limit <= DYNAMIC_PRICING_MAX_COMMUNITIES):
        return jsonify({
            'error': ('limit must be between 1 and '
                      f'{DYNAMIC_PRICING_MAX_COMMUNITIES}')
        }), 400

    def positive_ids(key, label):
        raw = body.get(key, [])
        if raw in (None, ''):
            raw = []
        if not isinstance(raw, list) or len(raw) > 5000:
            raise ValueError(
                f'{key} must be a list of at most 5,000 {label} IDs')
        values = []
        seen = set()
        for value in raw:
            text = str(value).strip()
            if not re.fullmatch(r'\d+', text) or int(text) <= 0:
                raise ValueError(
                    f'{key} must contain only positive integer {label} IDs')
            parsed = int(text)
            if parsed not in seen:
                seen.add(parsed)
                values.append(parsed)
        return values

    try:
        org_ids = positive_ids('orgIds', 'organization')
        community_ids = positive_ids('communityIds', 'community')
    except ValueError as exc:
        return jsonify({'error': str(exc)}), 400

    job_id = _job_new('dynamic_pricing_validation', '', total=0)
    threading.Thread(
        target=_run_dynamic_pricing_validation_job,
        args=(job_id, limit, org_ids, community_ids),
        daemon=True,
    ).start()
    return jsonify({'jobId': job_id})


@app.route('/api/dynamic-pricing/validation/<job_id>')
def dynamic_pricing_validation_result(job_id):
    """Open one persisted Unknown-mode validation result."""
    if not re.fullmatch(r'[0-9a-f]{6,32}', job_id or ''):
        return jsonify({'error': 'invalid job id'}), 400
    path = os.path.join(EXPORT_DIR, f'{job_id}.json')
    try:
        with open(path, 'r', encoding='utf-8') as fh:
            result = json.load(fh)
    except FileNotFoundError:
        return jsonify({'error': 'validation result not found'}), 404
    except (OSError, ValueError, TypeError) as exc:
        return jsonify({'error': f'could not read validation result: {exc}'}), 500
    return jsonify(result)


@app.route('/api/dynamic-pricing/validation/<job_id>/community/<building_id>')
def dynamic_pricing_validation_community(job_id, building_id):
    """Load step-through data for one row in a saved validation result."""
    if not re.fullmatch(r'[0-9a-f]{6,32}', job_id or ''):
        return jsonify({'error': 'invalid job id'}), 400
    if not re.fullmatch(r'\d+', building_id or ''):
        return jsonify({'error': 'invalid building id'}), 400
    path = os.path.join(EXPORT_DIR, f'{job_id}.json')
    try:
        with open(path, 'r', encoding='utf-8') as fh:
            result = json.load(fh)
    except FileNotFoundError:
        return jsonify({'error': 'validation result not found'}), 404
    except (OSError, ValueError, TypeError) as exc:
        return jsonify({'error': f'could not read validation result: {exc}'}), 500

    summary = next((
        row for row in (result.get('rows') or [])
        if str(row.get('buildingId') or '') == building_id
    ), None)
    if summary is None:
        return jsonify({'error': 'community is not part of this validation'}), 404
    try:
        return jsonify(_dynamic_pricing_fetch_saved_validation_community(
            summary))
    except (ClientError, ValueError, TypeError, UnicodeError,
            gzip_module.BadGzipFile) as exc:
        return jsonify({'error': str(exc)}), 422
    except Exception as exc:
        return jsonify({'error': f'could not load community: {exc}'}), 500


@app.route('/api/search/csv/<job_id>')
def download_csv(job_id):
    # job_id comes from our own uuid4().hex[:12] generator — no path chars —
    # but validate anyway before it touches a filesystem path.
    if not re.fullmatch(r'[0-9a-f]{6,32}', job_id or ''):
        return jsonify({'error': 'invalid job id'}), 400
    path = os.path.join(EXPORT_DIR, f'{job_id}.csv')
    if not os.path.exists(path):
        return jsonify({'error': 'Export not found or expired'}), 404
    return send_from_directory(EXPORT_DIR, f'{job_id}.csv', as_attachment=True,
                               download_name=f'mits_export_{job_id}.csv')


@app.route('/api/search/csv/<job_id>/query', methods=['POST'])
def query_csv(job_id):
    """Return one filtered/sorted page from an exported CSV.

    The download endpoint remains the complete, untouched CSV. This endpoint
    exists only to keep the on-screen table responsive for large exports.
    """
    if not re.fullmatch(r'[0-9a-f]{6,32}', job_id or ''):
        return jsonify({'error': 'invalid job id'}), 400

    path = os.path.join(EXPORT_DIR, f'{job_id}.csv')
    if not os.path.exists(path):
        return jsonify({'error': 'Export not found or expired'}), 404

    payload = request.get_json(silent=True) or {}
    try:
        page = max(1, int(payload.get('page', 1)))
        page_size = min(100, max(10, int(payload.get('pageSize', 25))))
    except (TypeError, ValueError):
        return jsonify({'error': 'page and pageSize must be whole numbers'}), 400

    sort_column = payload.get('sortColumn') or ''
    sort_direction = payload.get('sortDirection', 'asc')
    if sort_direction not in ('asc', 'desc'):
        return jsonify({'error': 'sortDirection must be asc or desc'}), 400
    filters = payload.get('filters') or {}
    if not isinstance(filters, dict):
        return jsonify({'error': 'filters must be an object'}), 400

    try:
        with open(path, newline='', encoding='utf-8') as fh:
            reader = csv.DictReader(fh)
            fieldnames = reader.fieldnames or []
            if sort_column and sort_column not in fieldnames:
                return jsonify({'error': 'Unknown sort column'}), 400
            unknown_filters = [name for name in filters if name not in fieldnames]
            if unknown_filters:
                return jsonify({'error': 'Unknown filter column'}), 400

            active_filters = {
                name: str(value).strip().casefold()
                for name, value in filters.items()
                if str(value).strip()
            }
            rows = []
            for row in reader:
                if active_filters and any(
                    needle not in (row.get(name) or '').casefold()
                    for name, needle in active_filters.items()
                ):
                    continue
                rows.append(row)
    except OSError as exc:
        return jsonify({'error': str(exc)}), 500

    if sort_column:
        def sort_key(row):
            value = row.get(sort_column) or ''
            # Natural ordering keeps numeric IDs and stages intuitive while
            # still handling mixed text columns safely.
            parts = re.split(r'(\d+(?:\.\d+)?)', value.casefold())
            return tuple((0, float(part)) if re.fullmatch(r'\d+(?:\.\d+)?', part)
                         else (1, part) for part in parts)

        rows.sort(key=sort_key, reverse=sort_direction == 'desc')

    filtered_rows = len(rows)
    total_pages = max(1, (filtered_rows + page_size - 1) // page_size)
    page = min(page, total_pages)
    start = (page - 1) * page_size
    return jsonify({
        'fields': fieldnames,
        'rows': rows[start:start + page_size],
        'page': page,
        'pageSize': page_size,
        'totalRows': filtered_rows,
        'totalPages': total_pages,
    })


@app.route('/api/job')
def job_status():
    job = _job_get(request.args.get('id', ''))
    if not job:
        return jsonify({'error': 'unknown job'}), 404
    return jsonify(job)


@app.route('/api/job/stop', methods=['POST'])
def stop_job():
    body = request.get_json(silent=True) or {}
    job_id = str(body.get('id') or '')
    job = _job_get(job_id)
    if not job:
        return jsonify({'error': 'unknown job'}), 404
    if job.get('kind') not in ('availability', 'availability_batch'):
        return jsonify({'error': 'only availability jobs can be stopped'}), 400
    if job.get('status') != 'running':
        return jsonify({'ok': True, 'alreadyFinished': True})
    _job_update(job_id, stopRequested=True,
                note='Stop requested · preparing the collected rows…')
    return jsonify({'ok': True})


@app.route('/api/snowflake/health')
def snowflake_health():
    """Connection status — safe to call whether or not Snowflake is configured."""
    return jsonify(snowflake_db.health())


@app.route('/api/snowflake/credentials', methods=['POST'])
def snowflake_credentials():
    """Persist Snowflake credentials to this app's .env and reset the client."""
    body = request.get_json(silent=True) or {}
    clean = lambda key: str(body.get(key) or '').strip()
    account, user = clean('account'), clean('user')
    auth_method = clean('authMethod') or 'access_token'
    secret = str(body.get('secret') or '')

    if not account or not user:
        return jsonify({'error': 'Snowflake account and user are required'}), 400
    if '\n' in secret or '\r' in secret:
        return jsonify({'error': 'Credential values cannot contain line breaks'}), 400

    auth_values = {}
    if auth_method == 'access_token':
        if not secret:
            # The token is intentionally never displayed in the UI. Allow the
            # user to supply only the missing account/user while retaining an
            # already-configured token in the environment.
            existing_authenticator = (os.environ.get('SNOWFLAKE_AUTHENTICATOR') or '').strip().lower()
            existing_token = (os.environ.get('SNOWFLAKE_ACCESS_TOKEN') or '').strip()
            if not existing_token and not existing_authenticator:
                existing_token = (os.environ.get('SNOWFLAKE_TOKEN') or '').strip()
            if not existing_token:
                return jsonify({'error': 'A programmatic access token is required'}), 400
            auth_values['SNOWFLAKE_ACCESS_TOKEN'] = existing_token
        else:
            auth_values['SNOWFLAKE_ACCESS_TOKEN'] = secret
    elif auth_method == 'password':
        if not secret:
            return jsonify({'error': 'A Snowflake password is required'}), 400
        auth_values['SNOWFLAKE_PASSWORD'] = secret
    elif auth_method == 'externalbrowser':
        auth_values['SNOWFLAKE_AUTHENTICATOR'] = 'externalbrowser'
    elif auth_method == 'oauth':
        if not secret:
            return jsonify({'error': 'An OAuth bearer token is required'}), 400
        auth_values['SNOWFLAKE_TOKEN'] = secret
        auth_values['SNOWFLAKE_AUTHENTICATOR'] = 'oauth'
    elif auth_method == 'key_pair':
        key_path = clean('privateKeyPath')
        if not key_path:
            return jsonify({'error': 'A private key path is required'}), 400
        auth_values['SNOWFLAKE_PRIVATE_KEY_PATH'] = key_path
        if secret:
            auth_values['SNOWFLAKE_PRIVATE_KEY_PASSPHRASE'] = secret
    else:
        return jsonify({'error': 'Unknown Snowflake authentication method'}), 400

    managed = {
        'SNOWFLAKE_ACCOUNT': account,
        'SNOWFLAKE_USER': user,
        'SNOWFLAKE_ROLE': clean('role'),
        'SNOWFLAKE_WAREHOUSE': clean('warehouse'),
        'SNOWFLAKE_DATABASE': clean('database'),
        'SNOWFLAKE_SCHEMA': clean('schema'),
        # Remove stale auth modes before writing the newly selected one.
        'SNOWFLAKE_ACCESS_TOKEN': '',
        'SNOWFLAKE_TOKEN': '',
        'SNOWFLAKE_PASSWORD': '',
        'SNOWFLAKE_AUTHENTICATOR': '',
        'SNOWFLAKE_PRIVATE_KEY_PATH': '',
        'SNOWFLAKE_PRIVATE_KEY_PASSPHRASE': '',
    }
    managed.update(auth_values)

    try:
        existing = []
        if os.path.exists(ENV_PATH):
            with open(ENV_PATH, 'r', encoding='utf-8') as fh:
                existing = fh.read().splitlines()
        keys = set(managed)
        lines = [line for line in existing
                 if not (line.split('=', 1)[0].strip() in keys)]
        if lines and lines[-1].strip():
            lines.append('')
        lines.extend(f'{key}={value}' for key, value in managed.items() if value)
        tmp_path = ENV_PATH + '.tmp'
        with open(tmp_path, 'w', encoding='utf-8') as fh:
            fh.write('\n'.join(lines) + '\n')
        os.replace(tmp_path, ENV_PATH)

        for key in keys:
            os.environ.pop(key, None)
        load_dotenv(dotenv_path=ENV_PATH, override=True)
        snowflake_db.reset()
        return jsonify({'ok': True, 'configured': snowflake_db.configured()})
    except Exception as e:
        try:
            if os.path.exists(ENV_PATH + '.tmp'):
                os.remove(ENV_PATH + '.tmp')
        except Exception:
            pass
        return jsonify({'error': f'Could not update Snowflake credentials: {e}'}), 500


@app.route('/api/snowflake/schema')
def snowflake_schema():
    """Discovered columns of the building table, and how they were mapped."""
    try:
        return jsonify({
            'table':   snowflake_db.BUILDING_TABLE,
            'columns': snowflake_db.columns(refresh=True),
            'mapped':  snowflake_db.column_map(refresh=True),
        })
    except Exception as e:
        return jsonify({'error': str(e)}), 500


ORG_CACHE_PATH = os.path.join(INDEX_DIR, '_organizations.json.gz')
ORG_CACHE_TTL  = 24 * 60 * 60


@app.route('/api/organizations')
def organizations():
    """
    Organization list for the optional search filter.

    Aggregating ~1M building rows takes ~35s on a small warehouse, so the
    result is cached to disk and served instantly afterwards. Pass ?refresh=1
    to rebuild.
    """
    if not snowflake_db.configured():
        return jsonify({'organizations': [], 'available': False})

    refresh = request.args.get('refresh') == '1'
    if not refresh and os.path.exists(ORG_CACHE_PATH):
        try:
            age = time.time() - os.path.getmtime(ORG_CACHE_PATH)
            if age < ORG_CACHE_TTL:
                with gzip_module.open(ORG_CACHE_PATH, 'rt', encoding='utf-8') as fh:
                    cached = json.load(fh)
                return jsonify({'organizations': cached, 'available': True,
                                'cached': True, 'ageSeconds': int(age)})
        except Exception:
            pass  # fall through and rebuild

    try:
        orgs = snowflake_db.organizations(refresh=True)
        os.makedirs(INDEX_DIR, exist_ok=True)
        tmp = ORG_CACHE_PATH + '.tmp'
        with gzip_module.open(tmp, 'wt', encoding='utf-8') as fh:
            json.dump(orgs, fh)
        os.replace(tmp, ORG_CACHE_PATH)
        return jsonify({'organizations': orgs, 'available': True, 'cached': False})
    except Exception as e:
        return jsonify({'organizations': [], 'available': False,
                        'error': str(e)})


@app.route('/api/file')
def get_file():
    if not _connected:
        return jsonify({'error': 'Not connected'}), 401

    key = request.args.get('key', '')
    if not key:
        return jsonify({'error': 'key required'}), 400
    if not key.startswith(ROOT):
        return jsonify({'error': 'key outside allowed prefix'}), 403

    try:
        response      = s3().get_object(Bucket=BUCKET, Key=key)
        raw_bytes     = response['Body'].read()
        size          = response['ContentLength']
        last_modified = response['LastModified'].isoformat()

        if key.endswith('.gz'):
            try:
                raw_bytes = gzip_module.decompress(raw_bytes)
            except Exception:
                pass  # fall through; decode whatever we have

        raw = raw_bytes.decode('utf-8', errors='replace')

        try:
            parsed = json.loads(raw)
            return jsonify({'ok': True, 'key': key, 'size': size,
                            'lastModified': last_modified, 'contentType': 'json',
                            'content': parsed, 'raw': raw})
        except json.JSONDecodeError:
            return jsonify({'ok': True, 'key': key, 'size': size,
                            'lastModified': last_modified, 'contentType': 'text',
                            'content': raw, 'raw': raw})
    except ClientError as e:
        return jsonify({'error': e.response['Error']['Message']}), 404
    except Exception as e:
        return jsonify({'error': str(e)}), 500


if __name__ == '__main__':
    print('Starting MITS Snapshot Analyzer → http://localhost:3000')
    print(f'Bucket: {BUCKET}  Region: {REGION}  Root: {ROOT}')
    app.run(host='0.0.0.0', port=3000, debug=True, threaded=True)
