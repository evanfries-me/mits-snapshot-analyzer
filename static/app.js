// ── Constants ─────────────────────────────────────────────────────────────────
const ROOT = 'elise-mits/';

// ── State ─────────────────────────────────────────────────────────────────────
const state = {
  mode:         'search',
  prefix:       ROOT,   // current S3 prefix (always within ROOT)
  autoSnapshot: null,   // snapshot name when auto-selected at entity level
  filter:       '',     // explore-mode filter string
  lastData:     null,   // last browse response, used for filter re-render
  activeKey:    null,
  rawMode:      false,
  fileContent:  null,
  highlight:    null,   // text to highlight in the preview (from a search hit)
};

const search = {
  integration: '',
  fileName:    '',
  searchBy:    'text', // 'text' | 'fields'
  text:        '',
  // Unlimited entries, in add-order. Each is {name, path, pathLabel}: `path`
  // is the exact structural location a schema-dropdown pick came from (so
  // it's matched precisely, never confused with a same-named field
  // elsewhere); null for a manually-typed field (matched by name wherever
  // it occurs — today's original, schema-free behavior).
  fields:      [],
  unique:      false,  // fields mode only: collapse to distinct value combinations
  availableFiles: [],
  availableFilesByIntegration: {},
  availableIntegrations: [],
  relatedFiles: [],   // [{integration, filename, schema, primaryJoin, relatedJoin, fields}]
  conditionGroups: [],
  org:         '',
  buildings:   '',
  asOf:        '',     // raw text: blank, a datetime, or a pasted snapshot-viewer link
  asOfValid:   true,   // false blocks the search button; only matters when asOf is non-blank
  agentAsOfValid: true,
  agentLimitValid: true,
  running:     false,
  indexing:    false,
  index:       null,   // { state, buildings, builtAt }
  results:     null,
  snowflake:   null,   // health payload
  schema:      null,   // {integration, fileName, data} — cached field schema for the dropdown
};

const historyState = { entries: [] };

let csvTable = null;
let csvTableToken = 0;
let csvFilterTimer = null;

const STALE_MS = 6 * 60 * 60 * 1000;   // index older than this is flagged stale
let filenamesToken = 0;                // guards against out-of-order responses
let schemaToken     = 0;               // guards field-schema fetches the same way

// ── Boot ─────────────────────────────────────────────────────────────────────
window.addEventListener('DOMContentLoaded', () => {
  // Mode tabs
  document.querySelectorAll('.mode-tab').forEach(tab =>
    tab.addEventListener('click', () => setMode(tab.dataset.mode))
  );
  document.querySelectorAll('.saved-toggle').forEach(toggle => {
    toggle.addEventListener('click', () => toggleSavedResults(toggle.dataset.historyKind));
  });
  document.querySelectorAll('[data-history-refresh]').forEach(button => {
    button.addEventListener('click', () => loadHistory(button.dataset.historyRefresh));
  });
  loadHistory();

  // Search form
  document.getElementById('sel-integration').addEventListener('change', onIntegrationChange);
  document.getElementById('sel-filename').addEventListener('change', e => {
    search.fileName = e.target.value;
    clearFieldSelections();   // a different file's field vocabulary doesn't carry over
    if (search.searchBy === 'fields' && search.integration && search.fileName) {
      loadFieldSchema();
    }
    syncSearchButton();
  });
  const textInput = document.getElementById('input-text');
  textInput.addEventListener('input', e => {
    search.text = e.target.value;
    syncSearchButton();
  });
  textInput.addEventListener('keydown', e => {
    if (e.key === 'Enter' && !document.getElementById('btn-run-search').disabled) runSearch();
  });
  document.getElementById('btn-run-search').addEventListener('click', runSearch);
  document.getElementById('btn-run-availability').addEventListener('click', runAvailabilityAgent);
  document.getElementById('btn-index').addEventListener('click', buildIndex);

  // Search By toggle
  document.querySelectorAll('.sb-opt').forEach(btn =>
    btn.addEventListener('click', () => setSearchBy(btn.dataset.searchBy))
  );

  // Fields mode: schema dropdown (auto-adds on pick), manual input + button,
  // remove via delegated click on chips.
  const fieldInput = document.getElementById('input-field');
  const addManualField = () => {
    const name = fieldInput.value.trim();
    if (!name || search.fields.some(f => f.name === name && !f.path)) {
      fieldInput.value = '';
      return;
    }
    search.fields.push({ name, path: null, pathLabel: null });
    fieldInput.value = '';
    renderFieldChips();
    syncSearchButton();
    fieldInput.focus();
  };
  document.getElementById('btn-add-field').addEventListener('click', addManualField);
  fieldInput.addEventListener('keydown', e => {
    if (e.key === 'Enter') { e.preventDefault(); addManualField(); }
  });

  document.getElementById('sel-field-schema').addEventListener('change', e => {
    const opt = e.target.selectedOptions[0];
    if (!opt || !opt.value) return;
    const { name, path, pathLabel } = JSON.parse(opt.value);
    const dup = search.fields.some(f => f.name === name && f.path === path);
    e.target.value = '';   // reset to placeholder regardless — picking always "consumes" the choice
    if (dup) return;
    search.fields.push({ name, path, pathLabel });
    renderFieldChips();
    syncSearchButton();
  });

  document.getElementById('field-chips').addEventListener('click', e => {
    const btn = e.target.closest('[data-remove-index]');
    if (!btn) return;
    search.fields.splice(Number(btn.dataset.removeIndex), 1);
    renderFieldChips();
    syncSearchButton();
  });

  document.getElementById('btn-add-related-file').addEventListener('click', () => {
    search.relatedFiles.push({ integration: search.integration, filename: '', schema: null, primaryJoin: null,
      relatedJoin: null, fields: [] });
    renderRelatedFiles();
    syncSearchButton();
  });
  document.getElementById('btn-add-condition-group').addEventListener('click', () => {
    search.conditionGroups.push({ logic: 'any', conditions: [{ field: null, operator: 'eq', value: '' }] });
    renderConditionGroups();
    syncSearchButton();
  });
  document.getElementById('condition-groups').addEventListener('click', e => {
    const removeGroup = e.target.closest('[data-remove-condition-group]');
    if (removeGroup) {
      search.conditionGroups.splice(Number(removeGroup.dataset.removeConditionGroup), 1);
      renderConditionGroups();
      syncSearchButton();
      return;
    }
    const addCondition = e.target.closest('[data-add-condition]');
    if (addCondition) {
      const group = search.conditionGroups[Number(addCondition.dataset.addCondition)];
      if (group) group.conditions.push({ field: null, operator: 'eq', value: '' });
      renderConditionGroups();
      syncSearchButton();
      return;
    }
    const removeCondition = e.target.closest('[data-remove-condition]');
    if (removeCondition) {
      const group = search.conditionGroups[Number(removeCondition.dataset.groupIndex)];
      if (group) group.conditions.splice(Number(removeCondition.dataset.removeCondition), 1);
      renderConditionGroups();
      syncSearchButton();
    }
  });
  document.getElementById('condition-groups').addEventListener('change', e => {
    const groupEl = e.target.closest('[data-condition-group]');
    if (!groupEl) return;
    const gi = Number(groupEl.dataset.conditionGroup);
    const group = search.conditionGroups[gi];
    if (!group) return;
    if (e.target.matches('[data-condition-logic]')) {
      group.logic = e.target.value;
    } else {
      const ci = Number(e.target.dataset.conditionIndex);
      const condition = group.conditions[ci];
      if (!condition) return;
      if (e.target.matches('[data-condition-field]')) condition.field = JSON.parse(e.target.value);
      if (e.target.matches('[data-condition-operator]')) condition.operator = e.target.value;
      if (e.target.matches('[data-condition-value]')) condition.value = e.target.value;
    }
    syncSearchButton();
  });
  document.getElementById('condition-groups').addEventListener('input', e => {
    if (!e.target.matches('[data-condition-value]')) return;
    const group = search.conditionGroups[Number(e.target.dataset.groupIndex)];
    const condition = group && group.conditions[Number(e.target.dataset.conditionIndex)];
    if (condition) condition.value = e.target.value;
    syncSearchButton();
  });
  document.getElementById('related-files').addEventListener('click', e => {
    const removeFile = e.target.closest('[data-remove-related-file]');
    if (removeFile) {
      search.relatedFiles.splice(Number(removeFile.dataset.removeRelatedFile), 1);
      renderRelatedFiles();
      syncSearchButton();
      return;
    }
    const removeField = e.target.closest('[data-remove-related-field]');
    if (removeField) {
      const rel = search.relatedFiles[Number(removeField.dataset.relatedIndex)];
      if (rel) rel.fields.splice(Number(removeField.dataset.fieldIndex), 1);
      renderRelatedFiles();
      syncSearchButton();
    }
  });
  document.getElementById('related-files').addEventListener('change', e => {
    const card = e.target.closest('[data-related-index]');
    if (!card) return;
    const index = Number(card.dataset.relatedIndex);
    const rel = search.relatedFiles[index];
    if (!rel) return;
    if (e.target.matches('[data-related-filename]')) {
      rel.filename = e.target.value;
      rel.schema = null;
      rel.primaryJoin = null;
      rel.relatedJoin = null;
      rel.fields = [];
      renderRelatedFiles();
      if (rel.filename) loadRelatedSchema(index);
    } else if (e.target.matches('[data-related-integration]')) {
      rel.integration = e.target.value;
      rel.filename = '';
      rel.schema = null;
      rel.primaryJoin = null;
      rel.relatedJoin = null;
      rel.fields = [];
      renderRelatedFiles();
      loadRelatedFileNames(index);
    } else if (e.target.matches('[data-primary-join]')) {
      rel.primaryJoin = JSON.parse(e.target.value);
      syncSearchButton();
    } else if (e.target.matches('[data-related-join]')) {
      rel.relatedJoin = JSON.parse(e.target.value);
      syncSearchButton();
    } else if (e.target.matches('[data-related-field]')) {
      if (e.target.value) {
        const field = JSON.parse(e.target.value);
        if (!rel.fields.some(f => f.name === field.name && f.path === field.path)) {
          rel.fields.push(field);
        }
        e.target.value = '';
        renderRelatedFiles();
        syncSearchButton();
      }
    }
  });

  document.getElementById('input-unique').addEventListener('change', e => {
    search.unique = e.target.checked;
  });

  document.getElementById('sel-org').addEventListener('change', e => {
    search.org = e.target.value;
  });
  document.getElementById('input-buildings').addEventListener('input', e => {
    search.buildings = e.target.value;
  });
  document.getElementById('input-asof').addEventListener('input', e => {
    search.asOf = e.target.value;
    renderAsOfFeedback();
    syncSearchButton();
  });
  document.getElementById('agent-sel-integration').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-show-unknown').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-sel-org').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-buildings').addEventListener('input', syncAvailabilityButton);
  document.getElementById('agent-asof').addEventListener('input', renderAgentAsOfFeedback);
  document.getElementById('agent-include-students').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-include-applications').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-limit').addEventListener('input', renderAgentLimitFeedback);

  // Preview actions + retry
  document.getElementById('btn-raw').addEventListener('click', toggleRaw);
  document.getElementById('btn-copy').addEventListener('click', copyContent);
  document.getElementById('btn-retry').addEventListener('click', tryConnect);
  document.getElementById('btn-cancel-credentials').addEventListener('click', closeSnowflakeCredentials);
  document.getElementById('btn-save-credentials').addEventListener('click', saveSnowflakeCredentials);
  document.getElementById('credential-auth').addEventListener('change', renderCredentialAuth);

  tryConnect();
});

async function tryConnect() {
  setStatus('spin', 'Connecting…');
  document.getElementById('error-screen').classList.remove('show');
  document.getElementById('main').style.display = 'flex';
  document.getElementById('error-detail').textContent = '';

  try {
    const res  = await fetch('/api/connect', { method: 'POST' });
    const data = await res.json();
    if (!data.ok) throw new Error(data.error || 'Connection failed');
    setStatus('ok', data.identity.split('/').pop());
    setMode('search');
    loadIntegrations();
    loadSnowflake();
  } catch (e) {
    setStatus('err', 'Not connected');
    document.getElementById('error-detail').textContent = e.message;
    document.getElementById('error-screen').classList.add('show');
    document.getElementById('main').style.display = 'none';
  }
}

// ── Mode switching ────────────────────────────────────────────────────────────
function setMode(mode) {
  if (mode !== 'search' && mode !== 'availability') mode = 'search';
  state.mode = mode;
  document.querySelectorAll('.mode-tab').forEach(t =>
    t.classList.toggle('active', t.dataset.mode === mode)
  );
  document.getElementById('pane-search').classList.toggle('active', mode === 'search');
  document.getElementById('pane-availability').classList.toggle('active', mode === 'availability');
}

// ── Explore mode ──────────────────────────────────────────────────────────────

// Enter a new directory — resets filter state
function navigateTo(prefix) {
  state.prefix       = prefix || ROOT;
  state.autoSnapshot = null;
  state.filter       = '';
  state.lastData     = null;
  document.getElementById('search-input').value = '';
  loadDirectory();
}

// Load the current directory (all items in one request)
async function loadDirectory() {
  renderBreadcrumb(state.prefix);
  renderFileList(null);  // show loading state

  try {
    const res  = await fetch(`/api/browse?prefix=${encodeURIComponent(state.prefix)}`);
    const data = await res.json();
    if (data.error) throw new Error(data.error);

    search.availableIntegrations = data.integrations || [];
    // If server auto-jumped to the latest snapshot, sync state to the real prefix
    if (data.autoSnapshot) {
      state.prefix       = data.prefix;   // snapshot prefix
      state.autoSnapshot = data.autoSnapshot;
      renderBreadcrumb(state.prefix);
    }

    renderFileList(data);
  } catch (e) {
    document.getElementById('file-list').innerHTML =
      `<div class="pane-msg">Error: ${esc(e.message)}</div>`;
  }
}

function renderFileList(data) {
  const list    = document.getElementById('file-list');
  const countEl = document.getElementById('pane-count');

  if (!data) {
    list.innerHTML      = '<div class="pane-msg">Loading…</div>';
    countEl.textContent = '';
    return;
  }

  state.lastData = data;  // store for filter re-renders

  // Apply filter
  const q          = state.filter.trim().toLowerCase();
  const allFolders = data.folders || [];
  const allFiles   = data.files   || [];
  const folders    = q ? allFolders.filter(f => f.name.toLowerCase().includes(q)) : allFolders;
  const files      = q ? allFiles.filter(f => f.name.toLowerCase().includes(q))   : allFiles;
  const total      = folders.length + files.length;
  const rawTotal   = allFolders.length + allFiles.length;

  // Count label
  if (data.autoSnapshot) {
    countEl.textContent = q
      ? `latest snapshot · ${total} of ${rawTotal} matching`
      : `latest snapshot · ${rawTotal} file${rawTotal !== 1 ? 's' : ''}`;
  } else {
    countEl.textContent = q
      ? `${total} of ${rawTotal} matching`
      : (rawTotal ? `${rawTotal} item${rawTotal !== 1 ? 's' : ''}` : '');
  }

  if (data.noSnapshots) {
    list.innerHTML = '<div class="pane-msg">No snapshots found</div>';
    return;
  }
  if (total === 0 && state.prefix === ROOT) {
    list.innerHTML = '<div class="pane-msg">elise-mits/ is empty</div>';
    return;
  }

  let html = '';

  // ── Up row (not shown at ROOT) ──
  // When auto-snapshot is active we're at depth 3 (snapshot level). Going up one
  // level would hit the entity (depth 2), which immediately auto-jumps back to
  // the same snapshot. Skip it and go straight to the source-type listing.
  const parent = state.autoSnapshot
    ? parentOf(parentOf(state.prefix))
    : parentOf(state.prefix);
  if (parent !== null) {
    html += `<div class="up-item" data-nav="${esc(parent)}">
      <span>‹</span><span>.. (up)</span>
    </div>`;
  }

  for (const f of folders) {
    html += `<div class="dir-item" data-nav="${esc(f.prefix)}">
      <span class="icon">▶</span>
      <span class="item-name">${esc(f.name)}</span>
    </div>`;
  }

  for (const f of files) {
    const active = f.key === state.activeKey ? ' active' : '';
    html += `<div class="file-item${active}" data-key="${esc(f.key)}">
      <span class="icon">◦</span>
      <span class="item-name">${esc(f.name)}</span>
      <span class="item-size">${fmtBytes(f.size)}</span>
    </div>`;
  }

  if (!html) {
    list.innerHTML = '<div class="pane-msg">Empty folder</div>';
    return;
  }

  list.innerHTML = html;

  list.querySelectorAll('[data-nav]').forEach(el =>
    el.addEventListener('click', () => navigateTo(el.dataset.nav))
  );
  list.querySelectorAll('[data-key]').forEach(el =>
    el.addEventListener('click', () => previewFile(el.dataset.key, el))
  );
}

// ── Search mode ───────────────────────────────────────────────────────────────

async function loadIntegrations() {
  const sel = document.getElementById('sel-integration');
  try {
    const res  = await fetch('/api/integrations');
    const data = await res.json();
    if (data.error) throw new Error(data.error);

    sel.innerHTML = '<option value="">Select an integration…</option>' +
      data.integrations.map(n => `<option value="${esc(n)}">${esc(n)}</option>`).join('');
    const supported = data.availabilityIntegrations || [];
    document.getElementById('agent-sel-integration').innerHTML =
      '<option value="">Select an integration…</option>' +
      '<option value="__all__">All integrations</option>' +
      supported.map(n => `<option value="${esc(n)}">${esc(n)}</option>`).join('');
    renderAgentLimitFeedback();
    syncAvailabilityButton();
  } catch (e) {
    sel.innerHTML = `<option value="">Error: ${esc(e.message)}</option>`;
  }
}

async function onIntegrationChange(e) {
  const integration = e.target.value;
  search.integration = integration;
  search.fileName    = '';
  search.index       = null;
  clearFieldSelections();   // a different integration's field vocabulary doesn't carry over

  const fileSel = document.getElementById('sel-filename');
  const hint    = document.getElementById('filename-hint');

  if (!integration) {
    fileSel.innerHTML = '<option value="">Select an integration first</option>';
    fileSel.disabled  = true;
    setSearchInputsEnabled(false);
    hint.textContent  = '';
    renderIndexStatus();
    syncSearchButton();
    return;
  }

  fileSel.disabled  = true;
  fileSel.innerHTML = '<option value="">Sampling snapshots…</option>';
  hint.textContent  = '';
  syncSearchButton();

  // Sampling can take seconds; if the user picks another integration meanwhile,
  // the stale response must not overwrite the newer one.
  const token = ++filenamesToken;

  try {
    const res  = await fetch(`/api/filenames?integration=${encodeURIComponent(integration)}`);
    const data = await res.json();
    if (token !== filenamesToken) return;
    if (data.error) throw new Error(data.error);

    search.index = data.index || { state: 'none' };
    search.availableFiles = data.fileNames || [];
    search.availableFilesByIntegration[integration] = data.fileNames || [];
    if (search.index.state === 'none') search.index.buildings = data.buildings;
    renderIndexStatus();

    if (!data.fileNames.length) {
      fileSel.innerHTML = '<option value="">No files found</option>';
      hint.textContent  = `${data.buildings} building${data.buildings !== 1 ? 's' : ''}`;
      return;
    }

    fileSel.innerHTML = '<option value="">Select a file…</option>' +
      data.fileNames.map(n => `<option value="${esc(n)}">${esc(n)}</option>`).join('');
    fileSel.disabled = false;
    setSearchInputsEnabled(true);

    const count = data.fileNames.length;
    hint.textContent = data.sampled
      ? `${count} file name${count !== 1 ? 's' : ''} from a ${data.sampleHits}-building sample of ${data.buildings}`
      : `${count} file name${count !== 1 ? 's' : ''} across ${data.buildings} indexed buildings`;
  } catch (e) {
    if (token !== filenamesToken) return;
    fileSel.innerHTML = `<option value="">Error: ${esc(e.message)}</option>`;
    renderIndexStatus();
  } finally {
    if (token === filenamesToken) syncSearchButton();
  }
}

// ── Snowflake-backed filters ──────────────────────────────────────────────────

async function loadSnowflake() {
  const note    = document.getElementById('snowflake-note');
  const filters = document.getElementById('db-filters');

  try {
    const health = await (await fetch('/api/snowflake/health')).json();
    search.snowflake = health;

    if (health.state !== 'ready') {
      filters.classList.remove('show');
      note.classList.add('show');
      const title = health.state === 'unconfigured' && health.hasAccessToken
        ? 'Snowflake connection details required'
        : health.state === 'unconfigured' ? 'Snowflake credentials required' :
        `Snowflake ${esc(health.state)}`;
      const detail = health.state === 'unconfigured'
        ? `${health.hasAccessToken ? 'Saved access token detected. ' : ''}Missing: ${esc((health.missing || []).join(', '))}`
        : esc(health.error || 'unavailable');
      const canEdit = health.state === 'unconfigured' || health.credentialIssue;
      note.innerHTML = `<b>${title}</b> — ${detail}` + (canEdit
        ? ` <button type="button" class="credential-inline-btn" id="btn-open-credentials">Enter credentials</button>`
        : '');
      if (canEdit) document.getElementById('btn-open-credentials').addEventListener('click', openSnowflakeCredentials);
      return;
    }

    note.classList.remove('show');
    filters.classList.add('show');

    // The building-id filter is usable immediately; the organization list can
    // take ~35s to build the first time, so it populates in the background
    // rather than holding up the rest of the pane.
    const sel = document.getElementById('sel-org');
    sel.innerHTML = '<option value="">Loading organizations…</option>';
    sel.disabled = true;

    const res  = await fetch('/api/organizations');
    const data = await res.json();

    if (data.error || !data.available) {
      sel.innerHTML = '<option value="">Any organization</option>';
      document.getElementById('agent-sel-org').innerHTML = '<option value="">Any organization</option>';
      sel.disabled = false;
      note.classList.add('show');
      note.innerHTML = `<b>Organization list unavailable</b> — ${esc(data.error || 'no organization column found')}`;
      return;
    }
    const orgOptions = '<option value="">Any organization</option>' +
      data.organizations.map(o => `<option value="${esc(o.value)}">${esc(o.label)}</option>`).join('');
    sel.innerHTML = orgOptions;
    document.getElementById('agent-sel-org').innerHTML = orgOptions;
    sel.disabled = false;
  } catch (e) {
    filters.classList.remove('show');
    note.classList.add('show');
    note.innerHTML = `<b>Snowflake unavailable</b> — ${esc(e.message)}`;
  }
}

function showSnowflakeCredentialPrompt(message) {
  const note = document.getElementById('snowflake-note');
  note.classList.add('show');
  note.innerHTML = `<b>Snowflake credentials need attention</b> — ${esc(message || 'Authentication failed.')} ` +
    `<button type="button" class="credential-inline-btn" id="btn-open-credentials">Update credentials</button>`;
  document.getElementById('btn-open-credentials').addEventListener('click', openSnowflakeCredentials);
}

function renderCredentialAuth() {
  const method = document.getElementById('credential-auth').value;
  const secretWrap = document.getElementById('credential-secret-wrap');
  const keyWrap = document.getElementById('credential-key-path-wrap');
  const secretLabel = document.querySelector('#credential-secret-wrap label');
  const secret = document.getElementById('credential-secret');
  const needsSecret = method === 'access_token' || method === 'password' || method === 'oauth';
  secretWrap.style.display = needsSecret ? '' : 'none';
  keyWrap.style.display = method === 'key_pair' ? '' : 'none';
  secretLabel.textContent = method === 'password' ? 'Password' :
    method === 'oauth' ? 'OAuth bearer token' : 'Programmatic access token';
  const canReuseSavedToken = method === 'access_token' && Boolean(search.snowflake?.hasAccessToken);
  secret.required = needsSecret && !canReuseSavedToken;
  secret.placeholder = canReuseSavedToken ? 'Leave blank to keep the saved token' : '';
}

function openSnowflakeCredentials() {
  const health = search.snowflake || {};
  document.getElementById('credential-account').value = health.account || '';
  document.getElementById('credential-user').value = health.user || '';
  document.getElementById('credential-secret').value = '';
  document.getElementById('credential-error').textContent = '';
  document.getElementById('snowflake-credentials').classList.add('show');
  renderCredentialAuth();
  document.getElementById('credential-account').focus();
}

function closeSnowflakeCredentials() {
  document.getElementById('snowflake-credentials').classList.remove('show');
}

async function saveSnowflakeCredentials() {
  const btn = document.getElementById('btn-save-credentials');
  const error = document.getElementById('credential-error');
  const method = document.getElementById('credential-auth').value;
  const payload = {
    account: document.getElementById('credential-account').value.trim(),
    user: document.getElementById('credential-user').value.trim(),
    authMethod: method,
    secret: document.getElementById('credential-secret').value,
    privateKeyPath: document.getElementById('credential-key-path').value.trim(),
    role: document.getElementById('credential-role').value.trim(),
    warehouse: document.getElementById('credential-warehouse').value.trim(),
    database: document.getElementById('credential-database').value.trim(),
    schema: document.getElementById('credential-schema').value.trim(),
  };
  btn.disabled = true;
  error.textContent = '';
  try {
    const res = await fetch('/api/snowflake/credentials', {
      method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(payload),
    });
    const data = await res.json();
    if (!res.ok || data.error) throw new Error(data.error || 'Could not save credentials');
    closeSnowflakeCredentials();
    await loadSnowflake();
  } catch (e) {
    error.textContent = e.message;
  } finally {
    btn.disabled = false;
  }
}

// ── Index status ──────────────────────────────────────────────────────────────

async function refreshIndexStatus() {
  if (!search.integration) return;
  try {
    const res  = await fetch(`/api/index/status?integration=${encodeURIComponent(search.integration)}`);
    const data = await res.json();
    if (!data.error) {
      search.index = data;
      renderIndexStatus();
    }
  } catch { /* status is advisory only */ }
}

function renderIndexStatus() {
  const bar  = document.getElementById('index-status');
  const text = document.getElementById('index-text');
  const btn  = document.getElementById('btn-index');

  if (!search.integration) {
    bar.classList.remove('show');
    return;
  }
  bar.classList.add('show');

  const idx = search.index || { state: 'none' };
  if (idx.state === 'ready') {
    const age   = Date.now() - idx.builtAt * 1000;
    const stale = age > STALE_MS;
    bar.className = `show ${stale ? 'stale' : 'ready'}`;
    text.textContent =
      `Indexed ${idx.buildings.toLocaleString()} buildings · ${fmtAge(age)} ago`;
    btn.textContent = 'Rebuild';
  } else {
    bar.className = 'show none';
    const n = idx.buildings ? ` (${idx.buildings.toLocaleString()} buildings)` : '';
    text.textContent = `Not indexed${n} — required to search`;
    btn.textContent  = 'Build index';
  }
  btn.disabled = search.indexing || search.running;
}

async function buildIndex() {
  if (!search.integration || search.indexing) return;
  search.indexing = true;
  renderIndexStatus();
  syncSearchButton();

  try {
    const res  = await fetch('/api/index/build', {
      method:  'POST',
      headers: { 'Content-Type': 'application/json' },
      body:    JSON.stringify({ integration: search.integration }),
    });
    const data = await res.json();
    if (data.error) throw new Error(data.error);

    await pollJob(data.jobId, 'Indexing buildings');
    await refreshIndexStatus();
    // Re-populate the dropdown from the now-complete index
    await onIntegrationChange({ target: { value: search.integration } });
  } catch (e) {
    document.getElementById('search-results').innerHTML =
      `<div class="pane-msg">Index failed: ${esc(e.message)}</div>`;
  } finally {
    search.indexing = false;
    hideProgress();
    renderIndexStatus();
    syncSearchButton();
  }
}

// Parse the "as of" field the same way the server does — a blank value, a
// bare datetime (treated as UTC, matching a snapshot-viewer link), or a
// pasted snapshot-viewer URL (only its reference_time param is read).
// This is purely for instant UI feedback; the server re-parses authoritatively.
function parseAsOfClient(raw) {
  raw = (raw || '').trim();
  if (!raw) return { ok: true, dt: null };

  let value = raw;
  if (/^https?:\/\//i.test(raw)) {
    let url;
    try {
      url = new URL(raw);
    } catch {
      return { ok: false, error: 'Not a valid URL' };
    }
    const ref = url.searchParams.get('reference_time');
    if (!ref) return { ok: false, error: 'That link has no reference_time parameter' };
    value = ref;
  }

  // A bare datetime with no explicit 'Z'/offset is UTC here (unlike the JS
  // Date parser's default of local time) — append 'Z' so preview and server
  // agree. Date-only strings ("2026-08-19") are already UTC per spec; only
  // datetime strings need the nudge.
  let iso = value;
  const hasOffset = /[zZ]$/.test(iso) || /[+-]\d{2}:?\d{2}$/.test(iso);
  if (iso.includes('T') && !hasOffset) iso += 'Z';

  const d = new Date(iso);
  if (isNaN(d.getTime())) {
    return { ok: false, error: `Could not parse "${value}" as a datetime` };
  }
  return { ok: true, dt: d };
}

function renderAsOfFeedback() {
  const hint  = document.getElementById('asof-hint');
  const input = document.getElementById('input-asof');
  const parsed = parseAsOfClient(search.asOf);
  search.asOfValid = parsed.ok;

  if (!search.asOf.trim()) {
    hint.className   = 'field-hint';
    hint.textContent = "Uses each building's latest snapshot";
  } else if (parsed.ok) {
    hint.className   = 'field-hint ok';
    hint.textContent = `→ ${fmtDateUTC(parsed.dt.toISOString())} UTC`;
  } else {
    hint.className   = 'field-hint err';
    hint.textContent = parsed.error;
  }
  input.style.borderColor = (!search.asOf.trim() || parsed.ok) ? '' : '#f85149';
}

// ── Search By: Text Match vs Fields ────────────────────────────────────────────

function setSearchBy(mode) {
  search.searchBy = mode;
  document.querySelectorAll('.sb-opt').forEach(btn =>
    btn.classList.toggle('active', btn.dataset.searchBy === mode)
  );
  document.getElementById('pane-text-match').classList.toggle('active', mode === 'text');
  document.getElementById('pane-fields').classList.toggle('active', mode === 'fields');
  document.getElementById('btn-run-search').textContent =
    mode === 'fields' ? 'Generate CSV' : 'Search latest snapshots';
  syncSearchButton();

  // Schema fetching does real GETs, so it's deferred until Fields mode is
  // actually shown rather than fetched eagerly on every file selection.
  if (mode === 'fields' && search.integration && search.fileName) {
    loadFieldSchema();
  }
}

// Fetch the field schema (object types + their fields) for the current
// integration+file and populate the dropdown, grouped by object type via
// <optgroup>. Cached per (integration, fileName) in `search.schema` so
// re-entering Fields mode for the same file doesn't refetch.
async function loadFieldSchema() {
  const sel  = document.getElementById('sel-field-schema');
  const hint = document.getElementById('field-schema-hint');

  const cached = search.schema;
  if (cached && cached.integration === search.integration && cached.fileName === search.fileName) {
    renderFieldSchemaOptions(cached.data);
    return;
  }

  const token = ++schemaToken;
  sel.disabled = true;
  sel.innerHTML = '<option value="">Finding known fields…</option>';
  hint.textContent = '';

  try {
    const url = `/api/fields-schema?integration=${encodeURIComponent(search.integration)}` +
                `&filename=${encodeURIComponent(search.fileName)}`;
    const res  = await fetch(url);
    const data = await res.json();
    if (token !== schemaToken) return;   // integration/file changed again meanwhile
    if (data.error) throw new Error(data.error);

    search.schema = { integration: search.integration, fileName: search.fileName, data };
    renderFieldSchemaOptions(data);
  } catch (e) {
    if (token !== schemaToken) return;
    sel.innerHTML = '<option value="">Type field names manually below</option>';
    sel.disabled = true;
    hint.textContent = `Couldn't load a field list: ${e.message}`;
  }
}

function renderFieldSchemaOptions(data) {
  const sel  = document.getElementById('sel-field-schema');
  const hint = document.getElementById('field-schema-hint');

  if (!data.jsonCompatible || !data.objectTypes.length) {
    sel.innerHTML = '<option value="">No field list available for this format</option>';
    sel.disabled = true;
    hint.textContent = data.jsonCompatible
      ? 'No fields found in the sampled files — type a field name manually below'
      : "This file isn't JSON — type a field name manually below";
    return;
  }

  sel.innerHTML = '<option value="">Pick a known field…</option>' + data.objectTypes.map(ot => {
    const options = ot.fields.map(f => {
      const value = JSON.stringify({ name: f.name, path: ot.path, pathLabel: ot.label });
      return `<option value='${esc(value)}'>${esc(f.name)}</option>`;
    }).join('');
    return `<optgroup label="${esc(ot.label)} (${ot.count.toLocaleString()})">${options}</optgroup>`;
  }).join('');
  sel.disabled = false;
  hint.textContent = `From a sample of ${data.sampleSize} building${data.sampleSize !== 1 ? 's' : ''} — ` +
    'a field the sample missed can still be typed manually below';
  renderRelatedFiles();
  renderConditionGroups();
}

// Enable/disable both search-by input types together — they share the same
// integration+file readiness gate, just for whichever mode is active.
function setSearchInputsEnabled(enabled) {
  document.getElementById('input-text').disabled     = !enabled;
  document.getElementById('input-field').disabled    = !enabled;
  document.getElementById('btn-add-field').disabled  = !enabled;
}

// Field chips (and the schema they were picked from) are specific to one
// integration+file's vocabulary — carrying them into a different one would
// either be meaningless or silently wrong, so both are reset together.
function clearFieldSelections() {
  search.fields = [];
  search.relatedFiles = [];
  search.schema = null;
  ++schemaToken;   // invalidate any in-flight schema fetch for the old file
  renderFieldChips();
  document.getElementById('input-field').value = '';
  const sel = document.getElementById('sel-field-schema');
  sel.innerHTML = '<option value="">Select an integration and file first</option>';
  sel.disabled = true;
  document.getElementById('field-schema-hint').textContent = '';
  renderRelatedFiles();
  renderConditionGroups();
}

function renderFieldChips() {
  const box = document.getElementById('field-chips');
  box.innerHTML = search.fields.map((f, i) => `
    <span class="field-chip${f.path ? '' : ' manual'}"
          title="${f.path ? `Scoped to ${esc(f.pathLabel)}` : 'Manually typed — matches this name wherever it occurs'}">
      <span class="chip-order">${i + 1}</span>
      <span>${esc(f.name)}</span>
      ${f.path ? `<span class="chip-path">${esc(f.pathLabel)}</span>` : ''}
      <button type="button" data-remove-index="${i}" title="Remove">×</button>
    </span>
  `).join('');
}

function schemaFields(data) {
  const out = [];
  const seen = new Set();
  for (const type of (data && data.objectTypes) || []) {
    for (const field of type.fields || []) {
      const item = { name: field.name, path: type.path, pathLabel: type.label };
      const key = `${item.name}\u0000${item.path}`;
      if (!seen.has(key)) { seen.add(key); out.push(item); }
    }
  }
  return out;
}

function schemaFieldOptions(data, placeholder, selected) {
  const fields = schemaFields(data);
  return `<option value="">${esc(placeholder)}</option>` + fields.map(field => {
    const value = JSON.stringify(field);
    const isSelected = selected && selected.name === field.name && selected.path === field.path;
    return `<option value='${esc(value)}'${isSelected ? ' selected' : ''}>` +
      `${esc(field.name)} · ${esc(field.pathLabel)}</option>`;
  }).join('');
}

function renderRelatedFiles() {
  const box = document.getElementById('related-files');
  const primarySchema = search.schema && search.schema.data;
  const allowed = new Set(search.integration === 'RentCafe'
    ? ['Voyager', 'UnitEditor'] : ['UnitEditor']);
  const integrations = search.availableIntegrations.filter(i => allowed.has(i));

  box.innerHTML = search.relatedFiles.map((rel, i) => {
    const files = search.availableFilesByIntegration[rel.integration] ||
      (rel.integration === search.integration ? search.availableFiles : []);
    const fileOptions = '<option value="">Select a file…</option>' +
      files.filter(f => !(rel.integration === search.integration && f === search.fileName)).map(f =>
        `<option value="${esc(f)}"${f === rel.filename ? ' selected' : ''}>${esc(f)}</option>`).join('');
    const ready = rel.filename && rel.schema;
    const fieldOptions = ready
      ? schemaFieldOptions(rel.schema, 'Add a field from this file…') :
        '<option value="">Select a related file first</option>';
    return `<div class="related-file-card" data-related-index="${i}">
      <div class="related-file-head">
        <select data-related-integration>
          <option value="">Select integration…</option>
          ${integrations.map(integration => `<option value="${esc(integration)}"${integration === rel.integration ? ' selected' : ''}>${esc(integration)}</option>`).join('')}
        </select>
        <select data-related-filename ${rel.integration ? '' : 'disabled'}>${fileOptions}</select>
        <button type="button" class="related-file-remove" data-remove-related-file="${i}" title="Remove">×</button>
      </div>
      ${ready ? `
        <span class="field-label">Join fields</span>
        <select data-primary-join ${primarySchema ? '' : 'disabled'}>
          ${schemaFieldOptions(primarySchema, 'Primary file field…', rel.primaryJoin)}
        </select>
        <select data-related-join>
          ${schemaFieldOptions(rel.schema, 'Related file field…', rel.relatedJoin)}
        </select>
        <select data-related-field>${fieldOptions}</select>
        <div class="related-file-fields">
          ${rel.fields.map((f, j) => `<span class="related-field-chip">${esc(f.name)}
            <button type="button" data-remove-related-field="${j}" data-related-index="${i}">×</button>
          </span>`).join('')}
        </div>
      ` : (rel.filename ? '<span class="field-hint">Loading fields…</span>' : '')}
    </div>`;
  }).join('');
}

async function loadRelatedSchema(index) {
  const rel = search.relatedFiles[index];
  if (!rel || !rel.filename || !rel.integration) return;
  try {
    const url = `/api/fields-schema?integration=${encodeURIComponent(rel.integration)}` +
                `&filename=${encodeURIComponent(rel.filename)}`;
    const data = await (await fetch(url)).json();
    if (search.relatedFiles[index] !== rel || data.error) return;
    rel.schema = data;
    renderRelatedFiles();
    renderConditionGroups();
    syncSearchButton();
  } catch { /* the card remains available for removal */ }
}

async function loadRelatedFileNames(index) {
  const rel = search.relatedFiles[index];
  if (!rel || !rel.integration) return;
  if (search.availableFilesByIntegration[rel.integration]) {
    renderRelatedFiles();
    return;
  }
  try {
    const res = await fetch(`/api/filenames?integration=${encodeURIComponent(rel.integration)}`);
    const data = await res.json();
    if (search.relatedFiles[index] !== rel || data.error) return;
    search.availableFilesByIntegration[rel.integration] = data.fileNames || [];
    renderRelatedFiles();
  } catch { /* the card remains available for removal */ }
}

function conditionFieldOptions(selected) {
  const fields = [];
  for (const field of schemaFields(search.schema && search.schema.data)) {
    fields.push({ ...field, source: 'primary', sourceLabel: 'Primary' });
  }
  search.relatedFiles.forEach((rel, index) => {
    for (const field of schemaFields(rel.schema)) {
      fields.push({ ...field, source: `related:${index}`,
        sourceLabel: `${rel.integration || 'Related'} / ${rel.filename || 'file'}` });
    }
  });
  return '<option value="">Select field…</option>' + fields.map(field => {
    const value = JSON.stringify(field);
    const isSelected = selected && selected.source === field.source &&
      selected.name === field.name && selected.path === field.path;
    return `<option value='${esc(value)}'${isSelected ? ' selected' : ''}>` +
      `${esc(field.sourceLabel)} · ${esc(field.name)} · ${esc(field.pathLabel)}</option>`;
  }).join('');
}

function renderConditionGroups() {
  const box = document.getElementById('condition-groups');
  if (!box) return;
  const operators = [
    ['eq', 'equals'], ['contains', 'contains'], ['not_contains', 'does not contain'],
    ['ne', 'does not equal'], ['gt', 'greater than'], ['lt', 'less than'],
  ];
  box.innerHTML = search.conditionGroups.map((group, gi) => `
    <div class="condition-group" data-condition-group="${gi}">
      <div class="condition-group-head">
        <span>Match</span>
        <select data-condition-logic>
          <option value="any"${group.logic === 'any' ? ' selected' : ''}>any</option>
          <option value="all"${group.logic === 'all' ? ' selected' : ''}>all</option>
        </select>
        <button type="button" data-remove-condition-group="${gi}" title="Remove group">×</button>
      </div>
      ${group.conditions.map((condition, ci) => `
        <div class="condition-row">
          <select data-condition-field data-group-index="${gi}" data-condition-index="${ci}">
            ${conditionFieldOptions(condition.field)}
          </select>
          <select data-condition-operator data-group-index="${gi}" data-condition-index="${ci}">
            ${operators.map(([value, label]) => `<option value="${value}"${condition.operator === value ? ' selected' : ''}>${label}</option>`).join('')}
          </select>
          <input type="text" data-condition-value data-group-index="${gi}" data-condition-index="${ci}"
                 value="${esc(condition.value || '')}" placeholder="Value" autocomplete="off" />
          <button type="button" data-remove-condition="${ci}" data-group-index="${gi}" title="Remove condition">×</button>
        </div>
      `).join('')}
      <button type="button" class="condition-add-btn" data-add-condition="${gi}">+ Add condition</button>
    </div>
  `).join('');
}

function syncSearchButton() {
  const base = search.integration && search.fileName
               && search.asOfValid && !search.running && !search.indexing;
  const ready = base && (search.searchBy === 'fields'
    ? search.fields.length > 0 && search.relatedFiles.every(rel =>
        rel.filename && rel.schema && rel.primaryJoin && rel.relatedJoin && rel.fields.length > 0) &&
      search.conditionGroups.every(group => group.conditions.length > 0 &&
        group.conditions.every(condition => condition.field && condition.value !== ''))
    : search.text.trim());
  document.getElementById('btn-run-search').disabled = !ready;
}

// ── Job polling ───────────────────────────────────────────────────────────────

function showProgress(note) {
  document.getElementById('progress-wrap').classList.add('show');
  document.getElementById('progress-note').textContent = note;
  document.getElementById('progress-pct').textContent  = '';
  document.getElementById('progress-fill').classList.add('indeterminate');
  document.getElementById('progress-fill').style.width = '';
}

function updateProgress(note, done, total) {
  document.getElementById('progress-note').textContent = note;
  const fill = document.getElementById('progress-fill');
  const pct  = document.getElementById('progress-pct');
  if (total > 0) {
    const p = Math.min(100, Math.round((done / total) * 100));
    fill.classList.remove('indeterminate');
    fill.style.width   = `${p}%`;
    pct.textContent    = `${done.toLocaleString()} / ${total.toLocaleString()} · ${p}%`;
  } else {
    fill.classList.add('indeterminate');
    pct.textContent = '';
  }
}

function hideProgress() {
  document.getElementById('progress-wrap').classList.remove('show');
}

// Poll a background job until it finishes; resolves with its result.
function pollJob(jobId, label) {
  showProgress(label + '…');
  return new Promise((resolve, reject) => {
    const tick = async () => {
      try {
        const res  = await fetch(`/api/job?id=${encodeURIComponent(jobId)}`);
        const job  = await res.json();
        if (job.error && !job.status) return reject(new Error(job.error));

        const note = job.note ? `${label} · ${job.note}` : `${label}…`;
        updateProgress(note, job.done || 0, job.total || 0);

        if (job.status === 'running') return setTimeout(tick, 700);
        if (job.status === 'error')   return reject(new Error(job.error || 'Job failed'));
        resolve(job.result);
      } catch (e) {
        reject(e);
      }
    };
    tick();
  });
}

async function runSearch() {
  search.running = true;
  syncSearchButton();
  renderIndexStatus();

  const btn      = document.getElementById('btn-run-search');
  const summary  = document.getElementById('search-summary');
  const results  = document.getElementById('search-results');
  const original = btn.textContent;

  const fieldsMode = search.searchBy === 'fields';
  btn.textContent   = fieldsMode ? 'Generating…' : 'Searching…';
  summary.classList.remove('show');
  results.innerHTML = '';
  clearFieldsPreview();

  const body = {
    integration: search.integration,
    filename:    search.fileName,
    mode:        search.searchBy,
    org:         search.org,
    buildings:   search.buildings,
    asOf:        search.asOf,
  };
  // Manual (no-path) entries go as bare strings; schema-picked ones carry
  // their path so the server matches the exact object type shown, not just
  // the name — the server accepts either shape per field.
  if (fieldsMode) {
    body.fields = search.fields.map(f => f.path ? { name: f.name, path: f.path } : f.name);
    body.unique = search.unique;
    body.relatedFiles = search.relatedFiles.map(rel => ({
      integration: rel.integration,
      filename: rel.filename,
      primaryJoin: rel.primaryJoin,
      relatedJoin: rel.relatedJoin,
      fields: rel.fields,
    }));
    body.conditions = search.conditionGroups.map(group => ({
      logic: group.logic,
      conditions: group.conditions.map(condition => ({
        source: condition.field.source,
        field: { name: condition.field.name, path: condition.field.path },
        operator: condition.operator,
        value: condition.value,
      })),
    }));
  } else {
    body.text = search.text;
  }

  try {
    const res = await fetch('/api/search', {
      method:  'POST',
      headers: { 'Content-Type': 'application/json' },
      body:    JSON.stringify(body),
    });
    const data = await res.json();

    if (res.status === 409 || data.error === 'no-index') {
      results.innerHTML =
        `<div class="pane-msg">${esc(data.message || 'This integration needs an index before you can search it. ' +
          'Use Build index above.')}</div>`;
      return;
    }
    if (data.error) throw new Error(data.error);

    const label  = fieldsMode ? 'Extracting fields'
                 : search.asOf.trim() ? 'Searching' : 'Reading snapshots';
    const result = await pollJob(data.jobId, label);
    search.results = result;
    if (fieldsMode) {
      renderFieldsResult(result);
      loadHistory();
    }
    else            renderSearchResults(result);
  } catch (e) {
    results.innerHTML = `<div class="pane-msg">Error: ${esc(e.message)}</div>`;
  } finally {
    search.running  = false;
    btn.textContent = original;
    hideProgress();
    renderIndexStatus();
    syncSearchButton();
  }
}

function renderAgentAsOfFeedback() {
  const raw = document.getElementById('agent-asof').value;
  const hint = document.getElementById('agent-asof-hint');
  const parsed = parseAsOfClient(raw);
  search.agentAsOfValid = parsed.ok;
  if (!raw.trim()) {
    hint.className = 'field-hint';
    hint.textContent = "Uses latest syncs created within the past 24 hours";
  } else if (parsed.ok) {
    hint.className = 'field-hint ok';
    hint.textContent = `→ ${fmtDateUTC(parsed.dt.toISOString())} UTC`;
  } else {
    hint.className = 'field-hint err';
    hint.textContent = parsed.error;
  }
  syncAvailabilityButton();
}

function renderAgentLimitFeedback() {
  const raw = document.getElementById('agent-limit').value.trim();
  const hint = document.getElementById('agent-limit-hint');
  if (!raw) {
    search.agentLimitValid = true;
    hint.className = 'field-hint';
    hint.textContent = 'No limit — evaluate all matching units';
  } else if (/^[1-9]\d*$/.test(raw) && Number(raw) <= 200000) {
    search.agentLimitValid = true;
    hint.className = 'field-hint ok';
    hint.textContent = `Stops after ${Number(raw).toLocaleString()} returned units`;
  } else {
    search.agentLimitValid = false;
    hint.className = 'field-hint err';
    hint.textContent = 'Enter a whole number from 1 to 200,000';
  }
  syncAvailabilityButton();
}

function syncAvailabilityButton() {
  const ready = document.getElementById('agent-sel-integration').value &&
    search.agentAsOfValid && search.agentLimitValid && !search.running && !search.indexing;
  document.getElementById('btn-run-availability').disabled = !ready;
}

async function runAvailabilityAgent() {
  search.running = true;
  const btn = document.getElementById('btn-run-availability');
  const original = btn.textContent;
  btn.textContent = 'Starting…';
  syncAvailabilityButton();
  const results = document.getElementById('availability-results');
  const summary = document.getElementById('availability-summary');
  clearFieldsPreview();
  results.innerHTML = '<div class="pane-msg">Starting availability analysis…</div>';
  summary.classList.remove('show');
  try {
    const integration = document.getElementById('agent-sel-integration').value;
    const requestBody = {
      integration,
      showUnknown: document.getElementById('agent-show-unknown').checked,
      includeStudents: document.getElementById('agent-include-students').checked,
      includeApplications: document.getElementById('agent-include-applications').checked,
      limit: document.getElementById('agent-limit').value.trim(),
      org: document.getElementById('agent-sel-org').value,
      buildings: document.getElementById('agent-buildings').value,
      asOf: document.getElementById('agent-asof').value,
    };
    let data;
    for (let attempt = 0; attempt < 4; attempt++) {
      const res = await fetch('/api/availability', {
        method: 'POST', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify(requestBody),
      });
      data = await res.json();
      if (res.status === 401 || data.error === 'Not connected') {
        results.innerHTML = '<div class="pane-msg">Reconnecting to the snapshot store…</div>';
        const connectRes = await fetch('/api/connect', {method: 'POST'});
        const connectData = await connectRes.json();
        if (!connectData.ok) throw new Error(connectData.error || 'Not connected');
        continue;
      }
      if (!(res.status === 409 || data.error === 'no-index')) break;

      // Availability can be the first feature used for an integration. Build
      // its persistent index here, then retry the same request automatically.
      results.innerHTML = `<div class="pane-msg">Building the ${esc(integration)} index before analyzing availability…</div>`;
      const indexRes = await fetch('/api/index/build', {
        method: 'POST', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({integration}),
      });
      const indexData = await indexRes.json();
      if (indexData.error) throw new Error(indexData.error);
      await pollJob(indexData.jobId, `Indexing ${integration}`);
    }
    if (data.error && (data.error === 'no-index' || data.error.includes('index'))) {
      throw new Error(data.message || data.error);
    }
    if (data.error) throw new Error(data.error);
    btn.textContent = 'Running…';
    results.innerHTML = '<div class="pane-msg">Availability analysis is running. Progress is shown below the mode panels.</div>';
    const result = await pollJob(data.jobId, 'Evaluating availability');
    search.results = result;
    renderAvailabilityResult(result);
    loadHistory();
  } catch (e) {
    results.innerHTML = `<div class="pane-msg">Error: ${esc(e.message)}</div>`;
  } finally {
    search.running = false;
    btn.textContent = original;
    hideProgress();
    syncAvailabilityButton();
  }
}

async function loadHistory() {
  try {
    const response = await fetch('/api/history');
    const data = await response.json();
    if (!response.ok || data.error) throw new Error(data.error || 'Could not load history');
    historyState.entries = data.entries || [];
    renderSavedHistory();
  } catch (error) {
    document.querySelectorAll('.saved-list').forEach(list => {
      list.innerHTML = `<div class="history-empty">${esc(error.message)}</div>`;
    });
  }
}

function toggleSavedResults(kind) {
  const panel = document.getElementById(kind === 'availability' ? 'saved-availability' : 'saved-search');
  const toggle = panel?.querySelector('.saved-toggle');
  if (!panel || !toggle) return;
  const open = panel.classList.toggle('open');
  toggle.setAttribute('aria-expanded', String(open));
}

function historyTitle(entry) {
  if (entry.name) return entry.name;
  return entry.kind === 'availability'
    ? `Availability · ${entry.integration || 'Unknown integration'}`
    : `Search · ${entry.fileName || entry.integration || 'CSV export'}`;
}

function renderSavedHistory() {
  ['fields', 'availability'].forEach(kind => {
    const entries = historyState.entries
      .filter(entry => entry.kind === kind)
      .sort((a, b) => Number(b.favorite) - Number(a.favorite) ||
        String(b.createdAt || '').localeCompare(String(a.createdAt || '')));
    const count = document.querySelector(`[data-history-count="${kind}"]`);
    if (count) count.textContent = `(${entries.length})`;
    renderHistoryList(kind, entries);
  });
}

function renderHistoryList(kind, entries) {
  const list = document.getElementById(kind === 'availability'
    ? 'history-availability-list' : 'history-search-list');
  if (!list) return;
  if (!entries.length) {
    list.innerHTML = `<div class="history-empty">No saved ${kind === 'availability' ? 'Availability Agent results' : 'Search results'}</div>`;
    return;
  }
  list.innerHTML = entries.map(entry => {
    const when = entry.createdAt ? new Date(entry.createdAt).toLocaleString() : '';
    const count = Number(entry.rowCount || 0).toLocaleString();
    const status = entry.available ? '' : ' · expired';
    return `<div class="history-item ${entry.available ? '' : 'expired'}" data-history-id="${esc(entry.id)}" role="button" tabindex="0">
      <button type="button" class="history-star ${entry.favorite ? 'favorite' : ''}" data-history-favorite="${esc(entry.id)}" title="${entry.favorite ? 'Unfavorite' : 'Favorite'}">${entry.favorite ? '★' : '☆'}</button>
      <div class="history-copy"><div class="history-title">${esc(historyTitle(entry))}</div>
        <div class="history-meta">${esc(entry.integration || '')} · ${count} rows · ${esc(when)}${status}</div></div>
      <button type="button" class="history-rename" data-history-rename="${esc(entry.id)}" title="Rename">✎</button>
      <button type="button" class="history-delete" data-history-delete="${esc(entry.id)}" title="Delete">×</button>
      <span class="history-open">${entry.available ? 'View' : '—'}</span>
    </div>`;
  }).join('');
  list.onclick = async event => {
    const rename = event.target.closest('[data-history-rename]');
    if (rename) {
      event.stopPropagation();
      await renameHistory(rename.dataset.historyRename);
      return;
    }
    const del = event.target.closest('[data-history-delete]');
    if (del) {
      event.stopPropagation();
      await deleteHistory(del.dataset.historyDelete);
      return;
    }
    const star = event.target.closest('[data-history-favorite]');
    if (star) {
      event.stopPropagation();
      await toggleHistoryFavorite(star.dataset.historyFavorite);
      return;
    }
    const item = event.target.closest('[data-history-id]');
    if (item) openHistoryEntry(item.dataset.historyId);
  };
  list.onkeydown = event => {
    if (event.key !== 'Enter' && event.key !== ' ') return;
    const item = event.target.closest('[data-history-id]');
    if (!item || event.target.closest('button')) return;
    event.preventDefault();
    openHistoryEntry(item.dataset.historyId);
  };
}

async function toggleHistoryFavorite(jobId) {
  const entry = historyState.entries.find(item => item.id === jobId);
  if (!entry) return;
  try {
    const response = await fetch(`/api/history/${encodeURIComponent(jobId)}/favorite`, {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({favorite: !entry.favorite}),
    });
    const data = await response.json();
    if (!response.ok || data.error) throw new Error(data.error || 'Could not update favorite');
    entry.favorite = data.favorite;
    historyState.entries.sort((a, b) => Number(b.favorite) - Number(a.favorite) ||
      String(b.createdAt || '').localeCompare(String(a.createdAt || '')));
    renderSavedHistory();
  } catch (error) {
    document.querySelectorAll('.saved-list').forEach(list => list.insertAdjacentHTML(
      'afterbegin', `<div class="history-empty">${esc(error.message)}</div>`));
  }
}

async function renameHistory(jobId) {
  const entry = historyState.entries.find(item => item.id === jobId);
  if (!entry) return;
  const name = window.prompt('Rename saved result', historyTitle(entry));
  if (name === null) return;
  const trimmed = name.trim();
  if (!trimmed) return;
  try {
    const response = await fetch(`/api/history/${encodeURIComponent(jobId)}/rename`, {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({name: trimmed}),
    });
    const data = await response.json();
    if (!response.ok || data.error) throw new Error(data.error || 'Could not rename result');
    entry.name = data.name;
    renderSavedHistory();
  } catch (error) {
    window.alert(error.message);
  }
}

async function deleteHistory(jobId) {
  const entry = historyState.entries.find(item => item.id === jobId);
  if (!entry || !window.confirm(`Delete "${historyTitle(entry)}"?`)) return;
  try {
    const response = await fetch(`/api/history/${encodeURIComponent(jobId)}`, {method: 'DELETE'});
    const data = await response.json();
    if (!response.ok || data.error) throw new Error(data.error || 'Could not delete result');
    historyState.entries = historyState.entries.filter(item => item.id !== jobId);
    renderSavedHistory();
  } catch (error) {
    window.alert(error.message);
  }
}

function openHistoryEntry(jobId) {
  const entry = historyState.entries.find(item => item.id === jobId);
  if (!entry || !entry.available) return;
  const data = {
    integration: entry.integration,
    rowCount: entry.rowCount || 0,
    fields: entry.fields || [],
    csvFields: entry.csvFields || entry.fields || [],
    fileName: entry.fileName,
    preview: [],
    downloadUrl: entry.downloadUrl || `/api/search/csv/${encodeURIComponent(jobId)}`,
  };
  const header = document.getElementById('preview-header');
  header.style.display = 'flex';
  document.getElementById('preview-key').textContent = entry.kind === 'availability'
    ? 'Availability Agent · Previous search' : 'CSV Export · Previous search';
  document.getElementById('preview-meta').textContent = `${entry.integration || ''} · ${Number(entry.rowCount || 0).toLocaleString()} rows`;
  document.getElementById('btn-raw').style.display = 'none';
  document.getElementById('btn-copy').style.display = 'none';
  renderCsvTable(data, {kind: entry.kind === 'availability' ? 'availability' : 'fields'});
}

function renderAvailabilityResult(data) {
  const summary = document.getElementById('availability-summary');
  const results = document.getElementById('availability-results');
  const bits = [
    `${data.rowCount.toLocaleString()} unit${data.rowCount !== 1 ? 's' : ''}`,
    `${data.unknownCount.toLocaleString()} prediction mismatch${data.unknownCount !== 1 ? 'es' : ''}`,
    `${data.searched.toLocaleString()} buildings searched`,
  ];
  if (data.integration === 'All integrations') {
    bits.unshift(`${(data.integrations || []).length} integrations`);
  }
  if (data.showUnknown) bits.push('showing unknown mappings only');
  if (data.includeStudents === false) bits.push('student communities excluded');
  if (data.includeApplications === false) bits.push('Applications-launched communities excluded');
  if (data.limit) bits.push(data.limited ? `limited to ${Number(data.limit).toLocaleString()}` : `limit ${Number(data.limit).toLocaleString()} not reached`);
  if (data.asOf) bits.push(`as of ${fmtDateUTC(data.asOf)} UTC`);
  if (data.errors) bits.push(`${data.errors} unreadable`);
  if (data.noSnapshot) bits.push(`${data.noSnapshot} had no snapshot that old`);
  if (data.staleLatest) bits.push(`${data.staleLatest.toLocaleString()} latest sync${data.staleLatest !== 1 ? 's' : ''} older than 24 hours excluded`);
  if (data.failedIntegrations?.length) bits.push(`failed: ${data.failedIntegrations.join(', ')}`);
  if (data.skippedIntegrations?.length) bits.push(`skipped after limit: ${data.skippedIntegrations.join(', ')}`);
  if (data.filterNote) bits.push(data.filterNote);
  if (data.rolloutError) bits.push('rollout lookup unavailable');
  if (data.enrichError) bits.push('building details unavailable');
  summary.textContent = bits.join(' · ');
  summary.classList.add('show');
  results.innerHTML = '<div class="pane-msg">CSV ready in the preview pane.</div>';
  if (data.enrichCredentialIssue) showSnowflakeCredentialPrompt(data.enrichError);
  else if (data.rolloutCredentialIssue) showSnowflakeCredentialPrompt(data.rolloutError);

  const header = document.getElementById('preview-header');
  header.style.display = 'flex';
  document.getElementById('preview-key').textContent = 'Availability Agent';
  document.getElementById('preview-meta').textContent = `${data.integration} · ${data.rowCount.toLocaleString()} units`;
  document.getElementById('btn-raw').style.display = 'none';
  document.getElementById('btn-copy').style.display = 'none';
  renderCsvTable(data, {kind: 'availability'});
}

function csvJobId(downloadUrl) {
  const match = String(downloadUrl || '').match(/\/csv\/([0-9a-f]{6,32})(?:$|[/?])/i);
  return match ? match[1] : '';
}

function csvDisplayNames() {
  return {
    entity: 'building', snapshot: 'snapshot', buildingName: 'building_name',
    orgId: 'org_id', orgName: 'org_name', snapshotLink: 'snapshot link',
    objectType: 'object_type',
  };
}

function renderCsvTable(data, options = {}) {
  const content = document.getElementById('preview-content');
  const displayNames = csvDisplayNames();
  const jobId = csvJobId(data.downloadUrl);
  const isAvailability = options.kind === 'availability';
  const hasObjectType = (data.preview || []).some(row => row.objectType != null);
  const cols = isAvailability
    ? (data.fields || [])
    : (data.csvFields || [
        'building', 'snapshot', 'building_name', 'org_id', 'org_name', 'snapshot link',
        ...(hasObjectType ? ['object_type'] : []), ...(data.fields || []),
      ]);
  csvTable = {
    jobId, cols, displayNames, data, kind: options.kind || 'fields',
    page: 1, pageSize: 25, sortColumn: '', sortDirection: 'asc', filters: {},
    totalRows: data.rowCount || 0, totalPages: Math.max(1, Math.ceil((data.rowCount || 0) / 25)),
  };
  const token = ++csvTableToken;
  const downloadText = isAvailability
    ? `<strong>${Number(data.rowCount || 0).toLocaleString()}</strong> row${data.rowCount !== 1 ? 's' : ''} — ready to download.`
    : `<strong>${Number(data.rowCount || 0).toLocaleString()}</strong> row${data.rowCount !== 1 ? 's' : ''} across ${data.fields.length} field${data.fields.length !== 1 ? 's' : ''} — ready to download.`;

  content.innerHTML = `
    <div id="fields-download"><span id="fields-download-text">${downloadText}</span>
      <a class="btn-download-csv" href="${esc(data.downloadUrl)}" download>Download CSV</a></div>
    <div id="fields-preview-wrap">
      <div class="preview-caption" id="csv-preview-caption">Loading table…</div>
      <table class="fields-preview"><thead>
        <tr class="csv-header-row">${cols.map(c => `<th class="csv-sortable"><button type="button" class="csv-sort-btn" data-csv-sort="${esc(c)}">${esc(displayNames[c] || c)}<span class="csv-sort-indicator"></span></button></th>`).join('')}</tr>
        <tr class="csv-filter-row">${cols.map(c => `<th><input class="csv-filter-input" data-csv-filter="${esc(c)}" placeholder="Filter…" aria-label="Filter ${esc(displayNames[c] || c)}"></th>`).join('')}</tr>
      </thead><tbody id="csv-preview-body"><tr><td class="csv-loading" colspan="${Math.max(cols.length, 1)}">Loading…</td></tr></tbody></table>
      <div class="csv-pagination" id="csv-pagination"></div>
    </div>`;

  content.onclick = event => {
    const button = event.target.closest('[data-csv-sort]');
    if (button && csvTable && token === csvTableToken) {
      const column = button.dataset.csvSort;
      if (csvTable.sortColumn === column) {
        csvTable.sortDirection = csvTable.sortDirection === 'asc' ? 'desc' : 'asc';
      } else {
        csvTable.sortColumn = column;
        csvTable.sortDirection = 'asc';
      }
      csvTable.page = 1;
      loadCsvTablePage(token);
      return;
    }
    const pageButton = event.target.closest('[data-csv-page]');
    if (!pageButton || pageButton.disabled || !csvTable || token !== csvTableToken) return;
    csvTable.page = Math.max(1, Number(pageButton.dataset.csvPage));
    loadCsvTablePage(token);
  };
  content.oninput = event => {
    const input = event.target.closest('[data-csv-filter]');
    if (!input || !csvTable || token !== csvTableToken) return;
    csvTable.filters[input.dataset.csvFilter] = input.value;
    csvTable.page = 1;
    clearTimeout(csvFilterTimer);
    csvFilterTimer = setTimeout(() => loadCsvTablePage(token), 220);
  };
  content.onchange = event => {
    const select = event.target.closest('[data-csv-page-size]');
    if (!select || !csvTable || token !== csvTableToken) return;
    csvTable.pageSize = Number(select.value) || 25;
    csvTable.page = 1;
    loadCsvTablePage(token);
  };
  content.onkeydown = event => {
    if (event.key !== 'Enter') return;
    const input = event.target.closest('[data-csv-filter]');
    if (!input || !csvTable || token !== csvTableToken) return;
    clearTimeout(csvFilterTimer);
    loadCsvTablePage(token);
  };
  loadCsvTablePage(token);
}

async function loadCsvTablePage(token) {
  const table = csvTable;
  if (!table || token !== csvTableToken) return;
  const body = document.getElementById('csv-preview-body');
  if (!body) return;
  body.innerHTML = `<tr><td class="csv-loading" colspan="${Math.max(table.cols.length, 1)}">Loading…</td></tr>`;
  try {
    if (!table.jobId) throw new Error('This export is not available for table paging');
    const response = await fetch(`/api/search/csv/${encodeURIComponent(table.jobId)}/query`, {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({
        page: table.page, pageSize: table.pageSize,
        sortColumn: table.sortColumn, sortDirection: table.sortDirection,
        filters: table.filters,
      }),
    });
    const result = await response.json();
    if (!response.ok || result.error) throw new Error(result.error || 'Could not load CSV rows');
    if (token !== csvTableToken) return;
    table.page = result.page;
    table.totalRows = result.totalRows;
    table.totalPages = result.totalPages;
    body.innerHTML = result.rows.length ? result.rows.map(row => `<tr>${table.cols.map(c => {
      const value = row[c] ?? '';
      return `<td class="${value === '' ? 'cell-blank' : ''}">${esc(value === '' ? '—' : value)}</td>`;
    }).join('')}</tr>`).join('')
      : `<tr><td class="csv-loading" colspan="${Math.max(table.cols.length, 1)}">No rows match these filters.</td></tr>`;
    renderCsvTableControls(result);
  } catch (error) {
    if (token !== csvTableToken) return;
    body.innerHTML = `<tr><td class="csv-loading" colspan="${Math.max(table.cols.length, 1)}">${esc(error.message)}</td></tr>`;
    renderCsvTableControls({page: table.page, pageSize: table.pageSize, totalRows: 0, totalPages: 1});
  }
}

function renderCsvTableControls(result) {
  if (!csvTable) return;
  const table = csvTable;
  const caption = document.getElementById('csv-preview-caption');
  const pagination = document.getElementById('csv-pagination');
  if (!caption || !pagination) return;
  const total = Number(result.totalRows || 0);
  const start = total ? ((table.page - 1) * table.pageSize) + 1 : 0;
  const end = total ? Math.min(start + table.pageSize - 1, total) : 0;
  caption.textContent = total
    ? `Showing ${start.toLocaleString()}–${end.toLocaleString()} of ${total.toLocaleString()} filtered row${total !== 1 ? 's' : ''}`
    : 'No rows match the current filters';
  pagination.innerHTML = `
    <button type="button" class="csv-page-btn" data-csv-page="${Math.max(1, table.page - 1)}" ${table.page <= 1 ? 'disabled' : ''}>Previous</button>
    <span>Page ${table.page.toLocaleString()} of ${Math.max(1, Number(result.totalPages || 1)).toLocaleString()}</span>
    <button type="button" class="csv-page-btn" data-csv-page="${table.page + 1}" ${table.page >= Number(result.totalPages || 1) ? 'disabled' : ''}>Next</button>
    <select class="csv-page-size" data-csv-page-size aria-label="Rows per page">
      ${[25, 50, 100].map(size => `<option value="${size}" ${table.pageSize === size ? 'selected' : ''}>${size} rows</option>`).join('')}
    </select>`;
  document.querySelectorAll('.csv-sort-btn').forEach(button => {
    const indicator = button.querySelector('.csv-sort-indicator');
    const active = button.dataset.csvSort === table.sortColumn;
    indicator.textContent = active ? (table.sortDirection === 'asc' ? '↑' : '↓') : '↕';
  });
}

function renderSearchResults(data) {
  const summary = document.getElementById('search-summary');
  const results = document.getElementById('search-results');

  const bits = [
    `${data.matchCount.toLocaleString()} match${data.matchCount !== 1 ? 'es' : ''}`,
    `${data.searched.toLocaleString()} of ${data.buildings.toLocaleString()} buildings searched`,
  ];
  if (data.asOf)        bits.push(`as of ${fmtDateUTC(data.asOf)} UTC`);
  if (data.org)         bits.push(`org filter on`);
  if (data.noSnapshot)  bits.push(`${data.noSnapshot.toLocaleString()} had no snapshot that old`);
  if (data.truncated)   bits.push(`showing first ${data.matches.length}`);
  if (data.errors)      bits.push(`${data.errors} unreadable`);
  if (data.filterNote)  bits.push(data.filterNote);
  if (data.enrichError) bits.push('building details unavailable');
  summary.textContent = bits.join(' · ');
  summary.classList.add('show');
  if (data.enrichCredentialIssue) showSnowflakeCredentialPrompt(data.enrichError);

  if (!data.matches.length) {
    results.innerHTML =
      `<div class="pane-msg">No snapshot contains “${esc(data.text)}”</div>`;
    return;
  }

  results.innerHTML = data.matches.map(m => {
    const b = m.building;
    // Lead with the building name when the database resolved one; the raw
    // entity id then moves to the subline so it's still visible.
    const title = b && b.name ? b.name : m.entity;
    const subParts = [
      b && b.name ? m.entity : null,
      b && (b.orgName || (b.org ? `org ${b.org}` : null)),
    ];
    // With a date filter, different buildings can resolve to different
    // snapshots (sync cadence varies) — show which one each match is from.
    if (data.asOf) subParts.push(snapshotLabel(m.snapshot));
    const sub = subParts.filter(Boolean).join(' · ');
    return `
    <div class="result-item" data-key="${esc(m.key)}">
      <div class="result-top">
        <span class="result-entity">${esc(title)}</span>
        <span class="result-count">${m.count}×</span>
      </div>
      ${sub ? `<div class="result-sub">${esc(sub)}</div>` : ''}
      <div class="result-snippet">${markup(m.snippet, data.text)}</div>
    </div>`;
  }).join('');

  results.querySelectorAll('[data-key]').forEach(el =>
    el.addEventListener('click', () => {
      state.highlight = data.text;
      previewFile(el.dataset.key, el);
    })
  );
}

function renderFieldsResult(data) {
  const summary = document.getElementById('search-summary');
  const results = document.getElementById('search-results');

  const bits = [
    `${data.rowCount.toLocaleString()} row${data.rowCount !== 1 ? 's' : ''}`,
    `${data.searched.toLocaleString()} of ${data.buildings.toLocaleString()} buildings searched`,
  ];
  if (data.asOf)        bits.push(`as of ${fmtDateUTC(data.asOf)} UTC`);
  if (data.org)         bits.push(`org filter on`);
  if (data.unique)      bits[0] = `${data.rowCount.toLocaleString()} unique row${data.rowCount !== 1 ? 's' : ''}`;
  if (data.noSnapshot)  bits.push(`${data.noSnapshot.toLocaleString()} had no snapshot that old`);
  if (data.truncated)   bits.push(`capped at ${data.rowCount.toLocaleString()} rows`);
  if (data.errors)      bits.push(`${data.errors} unreadable`);
  if (data.filterNote)  bits.push(data.filterNote);
  if (data.enrichError) bits.push('building details unavailable');
  summary.textContent = bits.join(' · ');
  summary.classList.add('show');
  if (data.enrichCredentialIssue) showSnowflakeCredentialPrompt(data.enrichError);

  if (!data.rowCount) {
    results.innerHTML = `<div class="pane-msg">None of the searched snapshots had a value for ` +
      `${data.fields.map(f => `“${esc(f)}”`).join(', ')}</div>`;
    renderFieldsPreview(data);
    return;
  }

  renderFieldsPreview(data);
  results.innerHTML = '<div class="pane-msg">CSV preview is shown on the right</div>';
}

function clearFieldsPreview() {
  csvTable = null;
  csvTableToken++;
  clearTimeout(csvFilterTimer);
  document.getElementById('preview-header').style.display = 'none';
  document.getElementById('btn-raw').style.display = '';
  document.getElementById('btn-copy').style.display = '';
  document.getElementById('preview-content').innerHTML =
    '<div class="pane-msg" style="flex-direction:column;gap:6px;">' +
    '<span style="font-size:24px;opacity:.3">📄</span>' +
    '<span>Click a file to preview it</span></div>';
}

function renderFieldsPreview(data) {
  const header = document.getElementById('preview-header');
  const content = document.getElementById('preview-content');
  header.style.display = 'flex';
  document.getElementById('preview-key').textContent = 'CSV Export';
  document.getElementById('preview-meta').textContent =
    `${data.fileName} · ${data.rowCount.toLocaleString()} row${data.rowCount !== 1 ? 's' : ''}`;
  document.getElementById('btn-raw').style.display = 'none';
  document.getElementById('btn-copy').style.display = 'none';

  // objectType only appears when fields came from more than one object type
  // (mixing schema-scoped picks with each other or with manual fields) — the
  // column is redundant noise in the common single-object case, so it's only
  // shown when it actually carries information.
  const hasObjectType = data.preview.some(r => r.objectType != null);
  const cols = [
    'entity', 'snapshot',
    ...(data.buildingColumns ? ['buildingName', 'orgId', 'orgName'] : []),
    'snapshotLink',
    ...(hasObjectType ? ['objectType'] : []),
    ...data.fields,
  ];
  renderCsvTable(data, {kind: 'fields'});
}

// Escape a snippet, then wrap occurrences of `needle` in <mark>
function markup(snippet, needle) {
  const safe = esc(snippet);
  if (!needle) return safe;
  return safe.replace(new RegExp(escRegex(esc(needle)), 'g'), m => `<mark>${m}</mark>`);
}

// ── File preview ─────────────────────────────────────────────────────────────
async function previewFile(key, el) {
  document.querySelectorAll('.file-item, .result-item')
    .forEach(r => r.classList.remove('active'));
  if (el) el.classList.add('active');
  state.activeKey = key;

  document.getElementById('preview-header').style.display = 'none';
  document.getElementById('preview-content').innerHTML =
    '<div class="pane-msg">Loading…</div>';

  try {
    const res  = await fetch(`/api/file?key=${encodeURIComponent(key)}`);
    const data = await res.json();
    if (!data.ok) throw new Error(data.error || 'Failed to load file');

    state.fileContent = data;
    state.rawMode     = false;
    renderPreview(data);
  } catch (e) {
    document.getElementById('preview-content').innerHTML =
      `<div class="pane-msg">⚠ ${esc(e.message)}</div>`;
  }
}

function renderPreview(data) {
  const header = document.getElementById('preview-header');
  header.style.display = 'flex';
  document.getElementById('btn-raw').style.display = '';
  document.getElementById('btn-copy').style.display = '';
  document.getElementById('preview-key').textContent  = data.key;
  document.getElementById('preview-meta').textContent =
    [fmtBytes(data.size), fmtDate(data.lastModified)].filter(Boolean).join(' · ');

  document.getElementById('btn-raw').classList.toggle('active', state.rawMode);

  const pre = document.createElement('pre');
  if (data.contentType === 'json' && !state.rawMode) {
    pre.innerHTML = withHighlight(highlight(data.content));
  } else {
    pre.innerHTML = withHighlight(esc(data.raw));
  }
  const content = document.getElementById('preview-content');
  content.innerHTML = '';
  content.appendChild(pre);

  // Jump to the first hit when the file was opened from a search result
  const first = pre.querySelector('.hit');
  if (first) first.scrollIntoView({ block: 'center' });
}

// Wrap search-hit text in already-escaped/highlighted HTML.
// Only matches inside text nodes are wrapped, so HTML tags stay intact.
function withHighlight(html) {
  if (!state.highlight) return html;
  const needle = esc(state.highlight);
  if (!needle) return html;
  const re = new RegExp(`(?![^<]*>)(${escRegex(needle)})`, 'g');
  return html.replace(re, '<span class="hit">$1</span>');
}

function toggleRaw() {
  if (!state.fileContent) return;
  state.rawMode = !state.rawMode;
  renderPreview(state.fileContent);
}

function copyContent() {
  if (!state.fileContent) return;
  const text = state.rawMode || state.fileContent.contentType !== 'json'
    ? state.fileContent.raw
    : JSON.stringify(state.fileContent.content, null, 2);
  navigator.clipboard.writeText(text).then(() => flashBtn('btn-copy', 'Copied!'));
}

function flashBtn(id, msg) {
  const b = document.getElementById(id);
  if (!b) return;
  const original = b.textContent;
  b.textContent = msg;
  setTimeout(() => b.textContent = original, 1500);
}

// ── Breadcrumb ────────────────────────────────────────────────────────────────
function renderBreadcrumb(prefix) {
  const el = document.getElementById('breadcrumb');

  const relative = prefix.startsWith(ROOT) ? prefix.slice(ROOT.length) : '';
  const parts    = relative ? relative.replace(/\/$/, '').split('/') : [];

  const segments = [
    { label: 'elise-mits', path: ROOT, current: parts.length === 0 },
    ...parts.map((part, i) => ({
      label:   part,
      path:    ROOT + parts.slice(0, i + 1).join('/') + '/',
      current: i === parts.length - 1,
    })),
  ];

  el.innerHTML = segments.map((s, i) => `
    ${i > 0 ? '<span class="bc-slash">/</span>' : ''}
    <span class="bc-seg${s.current ? ' current' : ''}" data-nav="${esc(s.path)}">${esc(s.label)}</span>
  `).join('');

  el.querySelectorAll('[data-nav]:not(.current)').forEach(node =>
    node.addEventListener('click', () => navigateTo(node.dataset.nav))
  );

  document.getElementById('pane-path').textContent =
    parts.length ? parts[parts.length - 1] + '/' : 'elise-mits';
}

// ── Helpers ───────────────────────────────────────────────────────────────────

// Returns the parent prefix, or null if already at ROOT
function parentOf(prefix) {
  if (prefix === ROOT) return null;
  const parts = prefix.replace(/\/$/, '').split('/');
  parts.pop();
  return parts.join('/') + '/';
}

function setStatus(st, text) {
  document.getElementById('status-dot').className    = st;
  document.getElementById('status-text').textContent = text;
}

function fmtBytes(n) {
  if (!n) return '';
  if (n < 1024)    return `${n} B`;
  if (n < 1048576) return `${(n / 1024).toFixed(1)} KB`;
  return `${(n / 1048576).toFixed(1)} MB`;
}

function fmtAge(ms) {
  const mins = Math.floor(ms / 60000);
  if (mins < 1)   return 'just now';
  if (mins < 60)  return `${mins}m`;
  const hrs = Math.floor(mins / 60);
  if (hrs < 24)   return `${hrs}h`;
  return `${Math.floor(hrs / 24)}d`;
}

function fmtDate(iso) {
  if (!iso) return '';
  return new Date(iso).toLocaleString('en-US', {
    month: 'short', day: 'numeric', year: 'numeric',
    hour: '2-digit', minute: '2-digit',
  });
}

// 'snapshot-2026-01-31T19:54:09.137191Z' -> a readable UTC timestamp.
function snapshotLabel(snapshotName) {
  if (!snapshotName || !snapshotName.startsWith('snapshot-')) return snapshotName || '';
  return fmtDateUTC(snapshotName.slice('snapshot-'.length)) + ' UTC';
}

// Snapshot cutoffs are always UTC — format explicitly in UTC so the preview
// never silently disagrees with what the server actually applied.
function fmtDateUTC(iso) {
  if (!iso) return '';
  return new Date(iso).toLocaleString('en-US', {
    month: 'short', day: 'numeric', year: 'numeric',
    hour: '2-digit', minute: '2-digit', second: '2-digit',
    timeZone: 'UTC',
  });
}

function esc(s) {
  return String(s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function escRegex(s) {
  return String(s).replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function highlight(obj) {
  const raw = JSON.stringify(obj, null, 2);
  return raw.replace(
    /("(?:\\.|[^"\\])*"(?=\s*:))|("(?:\\.|[^"\\])*")|(\b\d+(?:\.\d+)?(?:[eE][+-]?\d+)?\b)|(true|false)|(null)/g,
    (_, key, str, num, bool, nul) => {
      if (key)  return `<span class="jk">${esc(key)}</span>`;
      if (str)  return `<span class="js">${esc(str)}</span>`;
      if (num)  return `<span class="jn">${num}</span>`;
      if (bool) return `<span class="jb">${bool}</span>`;
      if (nul)  return `<span class="jx">null</span>`;
      return _;
    }
  );
}
