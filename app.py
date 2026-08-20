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
from concurrent.futures import (ThreadPoolExecutor, TimeoutError as FutureTimeoutError,
                                wait, FIRST_COMPLETED)
from datetime import datetime, timedelta, timezone
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

INDEX_DIR     = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'index')
INDEX_WORKERS = 64  # parallel LISTs while indexing
SEARCH_WORKERS = 48 # parallel GETs while searching
SAMPLE_SIZE   = 150 # buildings sampled to populate the file-name dropdown
RESULT_CAP    = 500 # max matches returned to the client
SNIPPET_PAD   = 70  # chars of context on each side of a match
ENRICH_TIMEOUT = 20 # seconds before Snowflake enrichment is abandoned
DEFAULT_SEARCH_LOOKBACK_HOURS = 24
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
    if not result or kind not in ('fields', 'availability'):
        return
    now = time.time()
    with _history_lock:
        entries = _history_read()
        previous = next((entry for entry in entries if entry.get('id') == job_id), {})
        entry = {
            'id': job_id,
            'kind': kind,
            'name': previous.get('name') or '',
            'integration': result.get('integration', ''),
            'createdAt': datetime.fromtimestamp(now, timezone.utc).isoformat(),
            'created': now,
            'favorite': bool(previous.get('favorite')),
            'rowCount': result.get('rowCount', 0),
            'fields': result.get('fields') or [],
            'csvFields': result.get('csvFields') or result.get('fields') or [],
            'fileName': result.get('fileName'),
            'details': details or {},
            'downloadUrl': f'/api/search/csv/{job_id}',
        }
        entries = [entry] + [item for item in entries if item.get('id') != job_id]
        entries.sort(key=lambda item: float(item.get('created') or 0), reverse=True)
        entries = entries[:HISTORY_MAX]
        _history_write(entries)


def _history_entries():
    with _history_lock:
        entries = _history_read()
    for entry in entries:
        entry['available'] = os.path.exists(
            os.path.join(EXPORT_DIR, f'{entry.get("id", "")}.csv'))
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
                                 exclude_applications: bool = False):
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
    stale_latest = 0
    freshness_cutoff = (
        datetime.now(timezone.utc) - timedelta(hours=DEFAULT_SEARCH_LOOKBACK_HOURS)
        if as_of is None else None
    )
    if as_of is None:
        targets = []
        for entity, (snapshot, files) in entities.items():
            if allowed is not None and entity not in allowed:
                continue
            try:
                created_at = _snapshot_dt(snapshot)
            except (TypeError, ValueError):
                created_at = None
            if created_at is None or created_at < freshness_cutoff:
                stale_latest += 1
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
    return targets, stale_latest


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


def _enrich_with_snowflake(job_id: str, entity_list: list):
    """
    Building name/org lookup for the rows actually being returned. Runs through
    a throwaway single-worker pool so a stuck connection (seen in practice: TCP
    SYN_SENT that never resolves, e.g. an OCSP check blocked by network/VPN
    policy) times out instead of hanging the whole job. shutdown(wait=False)
    means the stuck thread is abandoned, not joined — the caller doesn't wait
    for it to die. Returns (meta_dict_or_None, column_map_or_None, error_or_None).
    """
    if not entity_list:
        return None, None, None
    if not snowflake_db.configured():
        return None, None, 'Snowflake is not configured: missing credentials'

    _job_update(job_id, note='Loading building details…')
    pool = ThreadPoolExecutor(max_workers=1)
    try:
        future = pool.submit(snowflake_db.lookup, entity_list)
        meta = future.result(timeout=ENRICH_TIMEOUT)
        return meta, snowflake_db.column_map(), None
    except FutureTimeoutError:
        return None, None, (f'Snowflake lookup timed out after {ENRICH_TIMEOUT}s '
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

        targets, stale_latest = _build_targets(
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
                        'staleLatest': stale_latest,
                        'freshnessHours': (DEFAULT_SEARCH_LOOKBACK_HOURS
                                           if as_of is None else None),
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
    """Sweep CSV exports past EXPORT_MAX_AGE. Called opportunistically at the
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
        job_id = fn[:-4] if fn.endswith('.csv') else None
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

        targets, stale_latest = _build_targets(
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
        stale_outer = set()
        if outer_related:
            freshness_cutoff = (
                datetime.now(timezone.utc) - timedelta(hours=DEFAULT_SEARCH_LOOKBACK_HOURS)
                if as_of is None else None
            )
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
                        try:
                            rel_created_at = _snapshot_dt(rel_snapshot)
                        except (TypeError, ValueError):
                            rel_created_at = None
                        if rel_created_at is None or rel_created_at < freshness_cutoff:
                            stale_outer.add((rel['integration'], entity, rel['filename']))
                            continue
                        target_by_entity[entity] = (entity, rel_snapshot, None)
                    else:
                        target_by_entity[entity] = (entity, None, None)
            targets = sorted(target_by_entity.values())
            stale_latest += len(stale_outer)
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
                        'staleLatest':  stale_latest,
                        'freshnessHours': (DEFAULT_SEARCH_LOOKBACK_HOURS
                                           if as_of is None else None),
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


def _availability_extract(body: str, fields: list, voyager_units: bool = False):
    if voyager_units:
        return _availability_voyager_units(body, fields)
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
    if op == 'truthy':
        return bool(actual) and text.casefold() not in ('false', '0', 'none', 'null', 'no')
    if op == 'falsey':
        return not actual or text.casefold() in ('false', '0', 'none', 'null', 'no')
    if op == 'falsey_present':
        return actual is not None and text.casefold() in ('', 'false', '0', 'none', 'null', 'no')
    if op == 'invalid_rent':
        try:
            return not (100 < float(actual) < 50000)
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
            numeric = float(actual)
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
    direct_predicted, direct_reason = predicted, reason
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
            # Direct mapping wins when it already explains the final stage.
            if direct_predicted != predicted:
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
    """Exclude placeholder/wait-list unit names without inspecting status text."""
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
            return suffix.split('.', 1)[0].strip() or None
    return None


def _availability_supplemental_rows(body: str, config: dict,
                                    primary_rows: list) -> list:
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

    existing_ids = {
        str(value).strip().casefold()
        for row in primary_rows
        for value in [_availability_value(row, primary_id_field)]
        if value is not None and str(value).strip()
    }
    output_name_field = config.get('output_name_field') or 'unit_number'
    existing_names = {
        str(value).strip().casefold()
        for row in primary_rows
        for value in [_availability_value(row, output_name_field)]
        if value is not None and str(value).strip()
    }
    seen = set(existing_ids)
    seen_names = set(existing_names)
    output = []
    row_type_field = config.get('row_type_field')
    row_type_value = str(config.get('row_type_value') or '').strip().casefold()
    for source_row in _availability_extract(body, config.get('fields') or []):
        if row_type_field:
            actual_type = _availability_value(source_row, row_type_field)
            if str(actual_type or '').strip().casefold() != row_type_value:
                continue
        source_id = _availability_value(source_row, supplemental_id_field)
        source_name = _availability_value(source_row, supplemental_name_field)
        normalized_id = str(source_id or '').strip().casefold()
        normalized_name = str(source_name or '').strip().casefold()
        # Some RentCafe rows omit voyagerApartmentId even though the unit is
        # present. Unit numbers are unique within a building, so IDValue/name
        # is the safe fallback that prevents the same physical unit from being
        # re-added as a synthetic Lease Signed Voyager unit.
        if (not normalized_id or normalized_id in seen or not normalized_name or
                normalized_name in seen_names):
            continue
        seen.add(normalized_id)
        seen_names.add(normalized_name)
        output.append({
            output_name_field: source_name,
            primary_id_field: source_id,
            config.get('output_status_field') or 'status':
                config.get('output_status_value'),
            '__supplemental_unit': True,
        })
    return output


def _availability_supplemental_target(entity: str, primary_snapshot: str,
                                      as_of, config: dict,
                                      indexed_entities: dict):
    """Resolve the supplemental file, preferring its existing on-disk index."""
    integrations = config.get('integrations') or []
    files = config.get('files') or []
    if as_of is None:
        for related_integration in integrations:
            entity_data = indexed_entities.get(related_integration, {}).get(entity)
            if not entity_data:
                continue
            snapshot, snapshot_files = entity_data
            actual = _availability_first_file(
                snapshot_files, related_integration, files)
            if actual:
                return related_integration, snapshot, actual

    cutoff = as_of or _availability_snapshot_datetime(primary_snapshot)
    for related_integration in integrations:
        entity_prefix = f'{ROOT}{related_integration}/{entity}/'
        if cutoff is not None:
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
        actual = _availability_first_file(
            snapshot_files, related_integration, files)
        if actual:
            return related_integration, snapshot, actual
    return None


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
        _job_update(
            job_id,
            note=('Applying ' + ', '.join(filter_bits) + ' filters…'
                  if filter_bits else 'Preparing building scope…'))
        allowed, filter_note = _resolve_org_building_filter(
            org, building_filter,
            exclude_students=not include_students,
            exclude_applications=not include_applications)
        primary_candidates = rules.get('primary') or []
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
        stale_latest = 0
        freshness_cutoff = (
            datetime.now(timezone.utc) - timedelta(hours=24)
            if as_of is None else None)
        for entity, (snapshot, files) in entities.items():
            if allowed is not None and entity not in allowed:
                continue
            if freshness_cutoff is not None:
                created_at = _availability_snapshot_datetime(snapshot)
                if created_at is None or created_at < freshness_cutoff:
                    stale_latest += 1
                    continue
            actual = _availability_first_file(files, source_integration, primary_candidates)
            if actual:
                targets.append((entity, snapshot, actual, files))
            elif as_of is not None:
                targets.append((entity, None, None, []))
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
            entity, snapshot, primary_actual, snapshot_files = target
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
                primary_actual = _availability_first_file(
                    snapshot_files, source_integration, primary_candidates)
                if not primary_actual:
                    with lock:
                        no_snapshot += 1
                        counter['n'] += 1
                    return
            primary_s3_key = f'{ROOT}{source_integration}/{entity}/{snapshot}/{primary_actual}'
            try:
                primary_body = _fetch_text(primary_s3_key)
                primary_rows = _availability_extract(
                    primary_body, source_fields['primary'],
                    voyager_units=integration == 'Voyager')
                file_property_code = _availability_file_property_code(
                    primary_actual, primary_candidates)
                if file_property_code:
                    for row in primary_rows:
                        row['__file_property_code'] = file_property_code
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
                source_rows = {}
                for source in source_configs:
                    actual_source = _availability_file_variant(
                        snapshot_files, source_integration, source['file'])
                    if actual_source:
                        source_body = _fetch_text(
                            f'{ROOT}{source_integration}/{entity}/{snapshot}/{actual_source}')
                        source_rows[source['file']] = _availability_extract(
                            source_body, source_fields[source['file']],
                            voyager_units=(integration == 'Voyager' and
                                           source['file'].startswith(
                                               ('AllUnits_Login', 'AvailableUnits_Login'))))
                    else:
                        source_rows[source['file']] = []
                actual_actual = _availability_first_file(
                    snapshot_files, source_integration, rules.get('actual') or [])
                actual_rows = []
                if actual_actual:
                    actual_body = _fetch_text(
                        f'{ROOT}{source_integration}/{entity}/{snapshot}/{actual_actual}')
                    actual_rows = _availability_extract(actual_body, actual_fields)
            except Exception:
                with lock:
                    errors += 1
                    counter['n'] += 1
                return

            added_supplemental = []
            if supplemental_config:
                try:
                    supplemental_target = _availability_supplemental_target(
                        entity, snapshot, as_of, supplemental_config,
                        supplemental_indexes)
                    if supplemental_target:
                        related_integration, related_snapshot, related_file = supplemental_target
                        supplemental_body = _fetch_text(
                            f'{ROOT}{related_integration}/{entity}/'
                            f'{related_snapshot}/{related_file}')
                        added_supplemental = _availability_supplemental_rows(
                            supplemental_body, supplemental_config, primary_rows)
                        # Voyager's supplemental row does not carry the
                        # RentCafe property code. It is safe to inherit only
                        # when this building has one code; multi-code/CLO
                        # buildings would otherwise recreate the collision
                        # that building_unique_id is designed to prevent.
                        if len(rentcafe_codes) == 1:
                            sole_code = next(iter(rentcafe_codes))
                            for row in added_supplemental:
                                row['voyagerPropertyCode'] = sole_code
                        primary_rows.extend(added_supplemental)
                except Exception:
                    # The primary RentCafe analysis is still useful if the
                    # optional Voyager supplement is temporarily unreadable.
                    with lock:
                        supplemental_errors += 1

            actual_by_key = {}
            for row in actual_rows:
                for key in _availability_keys(row, actual_key):
                    actual_by_key.setdefault(key, row)
            source_by_key = {}
            for source in source_configs:
                keyed = {}
                join_key = source.get('join_key')
                for row in source_rows[source['file']]:
                    for key in _availability_keys(row, join_key or []):
                        keyed.setdefault(key, row)
                if not join_key and source_rows[source['file']]:
                    keyed['__all__'] = source_rows[source['file']][0]
                source_by_key[source['file']] = keyed

            produced = []
            seen_unit_keys = set()
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
                if _availability_wait_unit(primary_row, rules):
                    with lock:
                        wait_filtered += 1
                    continue
                primary_keys = _availability_keys(primary_row, primary_key)
                unit_key = _availability_unit_key(
                    primary_row, rules, phase_prefix_values)
                # A canonical external identity may occur more than once in a
                # raw feed. Retain the first row and its status deterministically.
                if unit_key in seen_unit_keys:
                    continue
                if unit_key:
                    seen_unit_keys.add(unit_key)
                actual_row = actual_by_key.get(unit_key, {})
                if integration == 'RentCafe':
                    # For a true single-property building, ILSUnit.external_id
                    # is the bare apartmentName. This fallback is deliberately
                    # forbidden when multiple Voyager property codes exist.
                    if not actual_row and len(rentcafe_codes) == 1:
                        name = (_availability_value(primary_row, 'apartmentName') or
                                _availability_value(primary_row, 'ApartmentName'))
                        name_key = str(name).strip().casefold() if name is not None else ''
                        actual_row = actual_by_key.get(name_key, {})
                    # Supplemental Voyager units on a multi-code building do
                    # not identify which RentCafe code owns them, so they
                    # cannot form a guaranteed building_unique_id.
                    if not unit_key:
                        actual_row = {}
                elif integration == 'Voyager' and not actual_row:
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
                            actual_row = actual_by_key.get(
                                str(bare_id).strip().casefold(), {})
                # unit_details is the canonical post-filter physical-unit
                # feed. Never emit raw API records — including supplemental
                # cross-integration units — when that unit was filtered out
                # before unit_details was produced.
                if not actual_row:
                    continue
                values = dict(primary_row)
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
                    source_primary_keys = _availability_keys(
                        primary_row, source.get('primary_key') or primary_key)
                    related = next((source_by_key[source['file']][key]
                                    for key in source_primary_keys
                                    if key in source_by_key[source['file']]), None)
                    if related is None:
                        related = source_by_key[source['file']].get('__all__')
                    if related:
                        for key, value in related.items():
                            values.setdefault(key, value)
                        for field, value in related.items():
                            values[f"{source['file']}__{field}"] = value
                    values[f"__source_present__{source['file']}"] = bool(related)
                values['__direct_stage'] = _availability_direct_prediction(rules, values)[0]
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
                    source_primary_keys = _availability_keys(
                        primary_row, source.get('primary_key') or primary_key)
                    related = next((source_by_key[source['file']][key]
                                    for key in source_primary_keys
                                    if key in source_by_key[source['file']]), None)
                    related = related or source_by_key[source['file']].get('__all__') or {}
                    for field in source_fields[source['file']]:
                        output[f"{source['file']}__{field}"] = _availability_value(related, field)
                for field in actual_fields:
                    output[f'unit_details__{field}'] = _availability_value(actual_row, field)
                produced.append(output)
            with lock:
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
            'staleLatest': stale_latest,
            'freshnessHours': 24 if as_of is None else None,
            'limit': max_results, 'limited': bool(max_results is not None and cap_hit['flag']),
            'stopped': _job_stop_requested(control_job_id),
            'includeStudents': include_students,
            'includeApplications': include_applications,
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
        stale_latest = 0
        supplemental_units = supplemental_errors = wait_filtered = 0
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
                include_students, include_applications, remaining, False, job_id)
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
            stale_latest += result.get('staleLatest') or 0
            supplemental_units += result.get('supplementalUnits') or 0
            supplemental_errors += result.get('supplementalErrors') or 0
            wait_filtered += result.get('waitFiltered') or 0
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
                        'staleLatest': stale_latest,
                        'freshnessHours': 24 if as_of is None else None,
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
                        'downloadUrl': f'/api/search/csv/{job_id}',
                    })
        _history_record(job_id, 'availability', _job_get(job_id)['result'], {
            'org': org,
            'buildings': building_filter,
            'asOf': as_of.isoformat() if as_of else None,
            'showUnknown': show_unknown,
            'includeStudents': include_students,
            'includeApplications': include_applications,
            'supplementalUnits': supplemental_units,
            'supplementalErrors': supplemental_errors,
            'waitFiltered': wait_filtered,
            'limit': max_results,
        })
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
    if not _index_load(primary):
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
    if (not isinstance(include_students, bool) or
            not isinstance(include_applications, bool)):
        return jsonify({'error': ('includeStudents and includeApplications '
                                  'must be booleans')}), 400
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
                   include_students, include_applications, max_results)
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
    path = os.path.join(EXPORT_DIR, f'{job_id}.csv')
    try:
        os.remove(path)
    except FileNotFoundError:
        pass
    except OSError as exc:
        return jsonify({'error': f'could not delete export: {exc}'}), 500
    return jsonify({'ok': True})


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
