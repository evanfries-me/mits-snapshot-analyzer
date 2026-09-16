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
  relatedFiles: [],   // [{integration, filename, schema, joinType, primaryJoin, relatedJoin, fields}]
  conditionGroups: [],
  org:         '',
  buildings:   '',
  includeStudents: false,
  resultLimit: '',
  resultLimitValid: true,
  asOf:        '',     // raw text: blank, a datetime, or a pasted snapshot-viewer link
  asOfValid:   true,   // false blocks the search button; only matters when asOf is non-blank
  agentAsOfValid: true,
  agentLimitValid: true,
  agentIndex:  null,
  availabilityIntegrations: [],
  availabilityJobId: null,
  availabilityStopping: false,
  running:     false,
  indexing:    false,
  index:       null,   // { state, buildings, builtAt }
  results:     null,
  snowflake:   null,   // health payload
  schema:      null,   // {integration, fileName, data} — cached field schema for the dropdown
};

const historyState = { entries: [] };

const dynamicPricing = {
  jobId: null,
  polling: null,
  validationJobId: null,
  validationPolling: null,
  validationResultId: null,
  validationResult: null,
  validationVisualizerRows: new Map(),
  validationOpen: new Set(),
  result: null,
  open: new Set(),
  filters: {},
  sortKey: 'knownApiCallsSaved',
  sortDir: 'desc',
  validationSortKey: 'unknownApiCallsSaved',
  validationSortDir: 'desc',
  validationView: 'community',
  visualSteps: {},
  visualModes: {},
  visualFullscreen: new Set(),
  visualColorOff: new Set(),
  activeVisualizer: null,
};

let csvTable = null;
let csvTableToken = 0;
let csvFilterTimer = null;
let dpVisualizerResizeTimer = null;
let dpAlgorithmDialogTrigger = null;

const DP_ALGORITHM_DOCUMENTS = {
  known: {
    title: 'Known Mode Algorithm',
    pseudocode: `INPUT
  units: available date and hold time for every unit
  supplied cadence C: exact cadence, or a documented lower bound

STATE
  responses[date][unit] = unknown until that property date is called
  active window[unit] = max(available date, sync date) through hold time
  phase[unit] = unknown

CALL(date, reason)
  Request the property for date.
  Record only the prices returned by this response, for every unit.

  FOR EACH unit:
    IF adjacent observed dates change from no price to a real price:
      Treat this as an availability-window edge, not a price-cycle boundary.
      Move the unit's active window to that first priced date.
      Preserve the unit's full hold time.

VERIFY CADENCE
  Process future-available units before currently-available units.

  FOR EACH future unit whose window starts on its available date:
    CALL(available date + C - 1, "test predicted boundary")
    CALL(available date + C,     "test predicted boundary")

    IF both calls return real, different prices:
      The availability-date alignment hypothesis is confirmed.
    ELSE:
      Do not project a boundary from availability alone.

  UNTIL cadence C is verified:
    Probe dates at cadence-spaced anchors.

    IF two observed prices differ with unchecked dates between them:
      Bisect that proven differing-price interval.
      Continue until the exact adjacent boundary is observed.

    IF an observed internal response conflicts with an apparently equal span:
      Bisect again; do not allow a skipped shorter cycle to verify C.

    Verify exact C only when two observed adjacent price boundaries are
    separated by C and the observed responses inside the cycle are consistent.

    IF C is only a lower bound and exact cadence cannot be proven:
      Retain the lower bound and retrieve every date not safely inferable.

LOCATE UNIT PHASES
  Process future-available units first; leave currently-available units last.

  FOR EACH unresolved unit:
    Probe cadence-spaced anchors.
    Bisect only intervals whose returned prices prove they contain a change.
    Set phase[unit] only after adjacent queried dates return different prices.

    IF no valid probe remains and no state changed:
      Mark this pass exhausted instead of selecting the unit forever.
      Reconsider it if another property-wide call adds useful evidence.

INFER AND COMPLETE
  IF equal real-price responses are no farther than C apart:
    Infer the dates between them.

  IF a response-derived lower bound L is available:
    After an observed boundary, infer up to L dates on each side.

  FOR EACH unit with a proven phase:
    Partition its active window into cadence groups.

  Choose the minimum set of property dates that places at least one call
  inside every still-unfilled cadence group.

  Use the complete stored matrix only to answer CALL and score accuracy.
  API Calls Saved = Current API Calls - Known Bootstrap Calls.`,
  },
  unknown: {
    title: 'Unknown Mode Algorithm',
    pseudocode: `INPUT
  units: available date and hold time for every unit
  no cadence value

STATE
  responses[date][unit] = unknown until that property date is called
  cadence lower bound L = 0
  discovered cadence C = unknown
  phase[unit] = unknown

CALL(date, reason)
  Request the property for date.
  Record only the prices returned by this response, for every unit.

  FOR EACH unit:
    IF adjacent observed dates change from no price to a real price:
      Treat this as an availability-window edge, not a price-cycle boundary.
      Move the unit's active window to that first priced date.
      Preserve the unit's full hold time.

DISCOVER FROM FUTURE-AVAILABLE UNITS
  future units = units whose active window begins on their future available date

  FOR EACH future unit, before any currently-available unit:
    Assume provisionally that availability is cycle day 1.
    CALL(first date, "open discovery interval")
    CALL(last date,  "open discovery interval")

    IF both endpoints return the same real price:
      Infer the entire window for this unit.
      Record hold time as a provisional property lower bound L.
      Treat it as unit-local if another unit's returned prices contradict it.
      Continue with another future unit.

    IF the endpoint prices differ:
      Binary-search the interval until the first price boundary is proven by
      two adjacent calls.
      candidate cadence K = days from available date to that boundary.

      IF K >= half of the hold time:
        Check the post-boundary tail.
        IF all observed tail evidence retains one price:
          Keep K as a one-boundary candidate.
        ELSE:
          Bisect the conflicting interval to find the shorter candidate.

      IF K < half of the hold time:
        Search near boundary + K for the next boundary.
        Bisect every proven differing-price interval until adjacent.

      Accept K as an exact cadence only when:
        - two consecutive observed boundaries are K days apart, and
        - observed responses inside that complete cycle are consistent.

      Before accepting K, test every price already returned by the same
      property calls. For each unit, every observed differing-price interval
      must permit one common K-day boundary phase.

      IF no phase can intersect all of a unit's differing-price intervals:
        Reject K without another API call.
        Bisect that unit's existing intervals to expose the shorter cycle.

  Prefer any exact two-boundary candidate immediately.
  Accept a valid one-boundary candidate only after all future units have had
  an opportunity to provide stronger evidence.

CALENDAR-MONTH CADENCE
  IF a 28-31 day candidate has consecutive boundaries on the same day of month:
    Check the next monthly edge once for the property, not once per unit.
    Three same-day monthly boundaries for one unit, or two corroborating
    boundary pairs across units, establish a calendar-month cadence.
    Partition ranges by that calendar day so 30/31-day months remain exact.
    If the proving unit ends too early, retrieve that possible monthly edge
    across the property horizon; those calls directly populate the ranges.

INVALIDATE AND REDISCOVER
  Treat every discovered cadence or property lower bound as provisional.
  Do not make calls whose sole purpose is to re-check cadence per unit.
  Passively evaluate every normal property response against C.

  IF later normal responses cannot fit one C-day phase for any unit:
      Reject C (or L).
      Preserve every API response already retrieved.
      Clear phases that were projected from the rejected cadence.
      Re-enter discovery without allowing the rejected cadence to be accepted
      again from the same evidence.

DISCOVER WITHOUT FUTURE UNITS
  Adaptively probe currently-available units using interval search.
  A price-cycle boundary exists only after adjacent queried dates return
  different real prices.

  IF two consecutive boundaries are observed:
    C = distance between them.
  ELSE:
    Retain L = largest response-observed equal-price range.

PROPAGATE PARTIAL KNOWLEDGE
  Whenever equal real-price endpoints are no farther apart than L:
    Infer the dates between them.

  Whenever a boundary is observed:
    Infer up to L dates on both sides without sequential calls.

LOCATE PHASES AND COMPLETE
  IF exact cadence C was discovered:
    Process future units first and currently-available units last.
    Locate only the cycle phase or delayed active-window start still needed
    for each unit; do not independently re-verify C for that unit.
    Set phase only after an adjacent price change is queried.
    Equal responses no farther than C apart prove their intervening dates.
    Partition proven phases into cadence groups.
    Call the minimum set of dates covering every unfilled group.
  ELSE:
    Keep the lower-bound result and call every date that cannot be inferred.

  Never reuse a unit without a new valid probe or new response evidence.
  Use the complete stored matrix only to answer CALL and score accuracy.
  API Calls Saved = Current API Calls - Unknown Bootstrap Calls.`,
  },
};

const STALE_MS = 6 * 60 * 60 * 1000;   // index older than this is flagged stale
const AGENT_INDEX_MAX_AGE_MS = 24 * 60 * 60 * 1000;
let filenamesToken = 0;                // guards against out-of-order responses
let schemaToken     = 0;               // guards field-schema fetches the same way

// ── Boot ─────────────────────────────────────────────────────────────────────
window.addEventListener('DOMContentLoaded', () => {
  document.getElementById('mode-selector').addEventListener('change', event =>
    setMode(event.target.value)
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
  document.getElementById('btn-stop-availability').addEventListener('click', stopAvailabilityAgent);
  document.getElementById('btn-agent-index').addEventListener('click', buildAgentIndex);
  document.getElementById('btn-run-sync-query').addEventListener('click', runSyncIssuesQuery);
  document.getElementById('btn-run-dynamic-pricing').addEventListener('click', runDynamicPricing);
  document.getElementById('btn-validate-dynamic-pricing').addEventListener('click', runDynamicPricingValidation);
  const dpBody = document.getElementById('dp-preview-body');
  dpBody.addEventListener('click', ev => {
    const algorithm = ev.target.closest('[data-dp-algorithm]');
    if (algorithm) {
      dpOpenAlgorithmDocument(algorithm.dataset.dpAlgorithm, algorithm);
      return;
    }
    const visualizer = ev.target.closest('.dp-algorithm-viz');
    if (visualizer) dynamicPricing.activeVisualizer = visualizer.dataset.bid;
    const vizStep = ev.target.closest('[data-dp-viz-action]');
    if (vizStep) {
      dpSetVisualizerStep(vizStep.dataset.bid, vizStep.dataset.dpVizAction);
      return;
    }
    const validationViz = ev.target.closest('[data-dp-validation-viz]');
    if (validationViz) {
      dpToggleValidationVisualizer(validationViz.dataset.dpValidationViz);
      return;
    }
    const btn = ev.target.closest('.dp-expand');
    if (btn) { dpToggleCommunity(btn.dataset.bid); return; }
    const validationSort = ev.target.closest('[data-dp-validation-sort]');
    if (validationSort) {
      dpSetValidationSort(validationSort.dataset.dpValidationSort);
      return;
    }
    const validationView = ev.target.closest('[data-dp-validation-view]');
    if (validationView) {
      dpSetValidationView(validationView.dataset.dpValidationView);
      return;
    }
    const sort = ev.target.closest('[data-dp-sort]');
    if (sort) { dpSetSort(sort.dataset.dpSort); return; }
    if (ev.target.closest('[data-dp-export]')) { dpExportCsv(); return; }
    if (ev.target.closest('[data-dp-clear-filters]')) {
      dynamicPricing.filters = {};
      dpRenderResult(dynamicPricing.result, !!dynamicPricing.result?.partial);
    }
  });
  dpBody.addEventListener('input', ev => {
    const slider = ev.target.closest('[data-dp-viz-slider]');
    if (slider) {
      dynamicPricing.activeVisualizer = slider.dataset.bid;
      dynamicPricing.visualSteps[slider.dataset.bid] = Number(slider.value);
      dpRenderVisualizer(slider.dataset.bid);
      return;
    }
    const input = ev.target.closest('[data-dp-filter]');
    if (!input) return;
    const key = input.dataset.dpFilter;
    const cursor = input.selectionStart;
    dynamicPricing.filters[key] = input.value;
    dpRenderResult(dynamicPricing.result, !!dynamicPricing.result?.partial);
    const next = [...dpBody.querySelectorAll('[data-dp-filter]')]
      .find(candidate => candidate.dataset.dpFilter === key);
    if (next) {
      next.focus();
      if (cursor != null) next.setSelectionRange(cursor, cursor);
    }
  });
  dpBody.addEventListener('change', ev => {
    const mode = ev.target.closest('[data-dp-viz-mode]');
    if (!mode) return;
    const bid = mode.dataset.bid;
    dynamicPricing.activeVisualizer = bid;
    dynamicPricing.visualModes[bid] = mode.value;
    dynamicPricing.visualSteps[bid] = 0;
    dpRenderVisualizer(bid);
  });
  document.addEventListener('keydown', ev => {
    if (ev.key === 'Escape') {
      const algorithmDialog = document.getElementById('dp-algorithm-dialog');
      if (algorithmDialog.open) {
        dpCloseAlgorithmDocument();
        return;
      }
      const fullscreenBid = dynamicPricing.activeVisualizer;
      if (fullscreenBid && dynamicPricing.visualFullscreen.has(fullscreenBid)) {
        dynamicPricing.visualFullscreen.delete(fullscreenBid);
        dpRenderVisualizer(fullscreenBid);
      }
      return;
    }
    if (ev.key !== 'ArrowLeft' && ev.key !== 'ArrowRight') return;
    const target = ev.target;
    if (target instanceof HTMLElement && (
      target.isContentEditable || ['INPUT', 'TEXTAREA', 'SELECT'].includes(target.tagName))) return;
    const bid = dynamicPricing.activeVisualizer
      || [...dynamicPricing.open][0]
      || [...dynamicPricing.validationOpen][0];
    if (!bid || (!dynamicPricing.open.has(String(bid))
        && !dynamicPricing.validationOpen.has(String(bid)))) return;
    ev.preventDefault();
    dpSetVisualizerStep(String(bid), ev.key === 'ArrowLeft' ? 'prev' : 'next');
  });
  window.addEventListener('resize', () => {
    clearTimeout(dpVisualizerResizeTimer);
    dpVisualizerResizeTimer = setTimeout(() => {
      new Set([
        ...dynamicPricing.open,
        ...dynamicPricing.validationOpen,
      ]).forEach(dpRenderVisualizer);
    }, 100);
  });
  // The syncs table is re-rendered on every query, so delegate the expand click.
  const siBody = document.getElementById('si-preview-body');
  siBody.addEventListener('click', ev => {
    const btn = ev.target.closest('.si-expand-btn');
    if (btn && !btn.disabled) { siToggleBuilding(btn.dataset.bid); return; }
    const seg = ev.target.closest('.si-seg-btn');
    if (seg) { siSetScope(seg.dataset.scope === 'all'); return; }
    const th = ev.target.closest('th.si-sortable');
    if (th) { siSortSyncsBy(th.dataset.sortkey); return; }
    const dth = ev.target.closest('th.si-dist-sortable');
    if (dth) siSortDistBy(dth.dataset.sortkey);
  });
  // 'input' keeps the readout live while dragging; the repaint is cheap since
  // it only re-aggregates already-fetched data.
  siBody.addEventListener('input', ev => {
    if (ev.target.id === 'si-pct-slider') {
      siSetMinPct(parseFloat(ev.target.value) / 100);
    }
  });
  // Default date range: last 7 days
  (() => {
    const today = new Date();
    const pad = n => String(n).padStart(2, '0');
    const fmt = d => `${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())}`;
    document.getElementById('si-end-date').value = fmt(today);
    const start = new Date(today); start.setDate(start.getDate() - 7);
    document.getElementById('si-start-date').value = fmt(start);
  })();
  document.getElementById('btn-agent-companion').addEventListener('click', buildAgentCompanionIndex);
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
    const selection = JSON.parse(opt.value);
    e.target.value = '';   // reset to placeholder regardless — picking always "consumes" the choice
    if (!addSchemaSelection(search.fields, selection, search.schema && search.schema.data)) return;
    reconcileJoinSelections();
    renderFieldChips();
    renderRelatedFiles();
    syncSearchButton();
  });

  document.getElementById('field-chips').addEventListener('click', e => {
    const btn = e.target.closest('[data-remove-index]');
    if (!btn) return;
    search.fields.splice(Number(btn.dataset.removeIndex), 1);
    reconcileJoinSelections();
    renderFieldChips();
    renderRelatedFiles();
    syncSearchButton();
  });
  document.getElementById('field-chips').addEventListener('change', e => {
    if (!e.target.matches('[data-expand-primary-array]')) return;
    const selection = search.fields[Number(e.target.dataset.selectionIndex)];
    if (!selection || selection.kind !== 'object') return;
    toggleArrayExpansion(selection, e.target.dataset.expandPrimaryArray, e.target.checked);
  });

  document.getElementById('btn-add-related-file').addEventListener('click', () => {
    search.relatedFiles.push({ integration: search.integration, filename: '', schema: null, primaryJoin: null,
      relatedJoin: null, joinType: 'left', fields: [] });
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
      if (rel) rel.fields.splice(Number(removeField.dataset.removeRelatedField), 1);
      if (rel) reconcileJoinSelection(rel, 'relatedJoin', rel.fields);
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
    if (e.target.matches('[data-expand-related-array]')) {
      const selection = rel.fields[Number(e.target.dataset.selectionIndex)];
      if (selection && selection.kind === 'object') {
        toggleArrayExpansion(selection, e.target.dataset.expandRelatedArray, e.target.checked);
      }
    } else if (e.target.matches('[data-related-filename]')) {
      rel.filename = e.target.value;
      rel.schema = null;
      rel.primaryJoin = null;
      rel.relatedJoin = null;
      rel.joinType = 'left';
      rel.fields = [];
      renderRelatedFiles();
      if (rel.filename) loadRelatedSchema(index);
    } else if (e.target.matches('[data-related-integration]')) {
      rel.integration = e.target.value;
      rel.filename = '';
      rel.schema = null;
      rel.primaryJoin = null;
      rel.relatedJoin = null;
      rel.joinType = 'left';
      rel.fields = [];
      renderRelatedFiles();
      loadRelatedFileNames(index);
    } else if (e.target.matches('[data-primary-join]')) {
      rel.primaryJoin = JSON.parse(e.target.value);
      syncSearchButton();
    } else if (e.target.matches('[data-related-join]')) {
      rel.relatedJoin = JSON.parse(e.target.value);
      syncSearchButton();
    } else if (e.target.matches('[data-join-type]')) {
      rel.joinType = e.target.value;
      syncSearchButton();
    } else if (e.target.matches('[data-related-field]')) {
      if (e.target.value) {
        const selection = JSON.parse(e.target.value);
        e.target.value = '';
        if (addSchemaSelection(rel.fields, selection, rel.schema)) {
          reconcileJoinSelection(rel, 'relatedJoin', rel.fields);
          renderRelatedFiles();
          syncSearchButton();
        }
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
  document.getElementById('input-include-students').addEventListener('change', e => {
    search.includeStudents = e.target.checked;
  });
  document.getElementById('input-result-limit').addEventListener('input', e => {
    search.resultLimit = e.target.value;
    renderSearchLimitFeedback();
  });
  document.getElementById('input-asof').addEventListener('input', e => {
    search.asOf = e.target.value;
    renderAsOfFeedback();
    syncSearchButton();
  });
  document.getElementById('agent-sel-integration').addEventListener('change', onAgentIntegrationChange);
  document.getElementById('agent-show-unknown').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-sel-org').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-buildings').addEventListener('input', syncAvailabilityButton);
  document.getElementById('agent-asof').addEventListener('input', renderAgentAsOfFeedback);
  document.getElementById('agent-include-students').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-include-applications').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-include-not-launched-leasing').addEventListener('change', syncAvailabilityButton);
  document.getElementById('agent-limit').addEventListener('input', renderAgentLimitFeedback);

  // Preview actions + retry
  document.getElementById('btn-raw').addEventListener('click', toggleRaw);
  document.getElementById('btn-copy').addEventListener('click', copyContent);
  document.getElementById('btn-retry').addEventListener('click', tryConnect);
  document.getElementById('btn-cancel-credentials').addEventListener('click', closeSnowflakeCredentials);
  document.getElementById('btn-save-credentials').addEventListener('click', saveSnowflakeCredentials);
  document.getElementById('credential-auth').addEventListener('change', renderCredentialAuth);
  const algorithmDialog = document.getElementById('dp-algorithm-dialog');
  document.getElementById('dp-algorithm-close').addEventListener('click', dpCloseAlgorithmDocument);
  algorithmDialog.addEventListener('click', event => {
    if (event.target === algorithmDialog) dpCloseAlgorithmDocument();
  });
  algorithmDialog.addEventListener('close', () => {
    if (dpAlgorithmDialogTrigger?.isConnected) dpAlgorithmDialogTrigger.focus();
    dpAlgorithmDialogTrigger = null;
  });

  tryConnect();
});

function dpOpenAlgorithmDocument(mode, trigger) {
  const documentContent = DP_ALGORITHM_DOCUMENTS[mode];
  if (!documentContent) return;
  const dialog = document.getElementById('dp-algorithm-dialog');
  dpAlgorithmDialogTrigger = trigger || document.activeElement;
  document.getElementById('dp-algorithm-title').textContent = documentContent.title;
  document.getElementById('dp-algorithm-code').textContent = documentContent.pseudocode;
  if (!dialog.open) dialog.showModal();
  document.getElementById('dp-algorithm-close').focus();
}

function dpCloseAlgorithmDocument() {
  const dialog = document.getElementById('dp-algorithm-dialog');
  if (dialog.open) dialog.close();
}

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
  if (!['search', 'availability', 'sync-issues', 'dynamic-pricing'].includes(mode)) mode = 'search';
  state.mode = mode;
  document.getElementById('mode-selector').value = mode;
  document.getElementById('pane-search').classList.toggle('active', mode === 'search');
  document.getElementById('pane-availability').classList.toggle('active', mode === 'availability');
  document.getElementById('pane-sync-issues').classList.toggle('active', mode === 'sync-issues');
  document.getElementById('pane-dynamic-pricing').classList.toggle('active', mode === 'dynamic-pricing');

  // Show/hide the right-side preview areas
  const isSI = mode === 'sync-issues';
  const isDP = mode === 'dynamic-pricing';
  document.getElementById('preview-header').style.display = (isSI || isDP) ? 'none' : '';
  document.getElementById('preview-content').style.display = (isSI || isDP) ? 'none' : '';
  document.getElementById('si-preview').style.display     = isSI ? 'flex' : 'none';
  document.getElementById('dp-preview').style.display     = isDP ? 'flex' : 'none';
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
    search.availabilityIntegrations = supported;
    document.getElementById('agent-sel-integration').innerHTML =
      '<option value="">Select an integration…</option>' +
      '<option value="__all__">All integrations</option>' +
      supported.map(n => `<option value="${esc(n)}">${esc(n)}</option>`).join('');
    // Sync Issues integration filter — a checkbox per integration so any
    // number can be selected at once; none checked means all integrations.
    document.getElementById('si-integration-list').innerHTML = supported.map(n =>
      `<label class="si-integration-check">` +
        `<input type="checkbox" class="si-integration-cb" value="${esc(n)}" /> ${esc(n)}` +
      `</label>`
    ).join('');
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
    hint.textContent = 'Uses the latest snapshots recorded in the index';
  } else if (parsed.ok) {
    hint.className   = 'field-hint ok';
    hint.textContent = `→ latest sync in the 24 hours before ${fmtDateUTC(parsed.dt.toISOString())} UTC`;
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
  renderSearchLimitFeedback();
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
  const structured = data.structuredCompatible ?? data.jsonCompatible;

  if (!structured || !data.objectTypes.length) {
    sel.innerHTML = '<option value="">No field list available for this format</option>';
    sel.disabled = true;
    hint.textContent = structured
      ? 'No fields found in the sampled files — type a field name manually below'
      : "This file isn't structured JSON or XML — type a field name manually below";
    return;
  }

  sel.innerHTML = '<option value="">Pick a field or entire object…</option>' + data.objectTypes.map(ot => {
    const objectValue = JSON.stringify({ kind: 'object', path: ot.path, pathLabel: ot.label });
    const objectFieldCount = schemaObjectFields(ot).length;
    const options = ot.fields.map(f => {
      const value = JSON.stringify({ name: f.name, path: ot.path, pathLabel: ot.label });
      return `<option value='${esc(value)}'>${esc(f.name)}</option>`;
    }).join('');
    return `<optgroup label="${esc(ot.label)} (${ot.count.toLocaleString()})">` +
      `<option value='${esc(objectValue)}'>All fields from ${esc(ot.label)} (${objectFieldCount})</option>` +
      options + `</optgroup>`;
  }).join('');
  sel.disabled = false;
  const format = data.format ? `${data.format.toUpperCase()} · ` : '';
  hint.textContent = `${format}From a sample of ${data.sampleSize} building${data.sampleSize !== 1 ? 's' : ''} — ` +
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
    <div class="field-chip-wrap">
      <span class="field-chip${f.path ? '' : ' manual'}"
          title="${f.kind === 'object' ? `All known scalar fields scoped to ${esc(f.pathLabel)}` :
            f.path ? `Scoped to ${esc(f.pathLabel)}` : 'Manually typed — matches this name wherever it occurs'}">
        <span class="chip-order">${i + 1}</span>
        <span>${f.kind === 'object' ? `All fields (${f.fieldCount})` : esc(f.name)}</span>
        ${f.path ? `<span class="chip-path">${esc(f.pathLabel)}</span>` : ''}
        <button type="button" data-remove-index="${i}" title="Remove">×</button>
      </span>
      ${renderArrayExpansionOptions(f, i, 'primary')}
    </div>
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

function schemaObject(data, path) {
  return ((data && data.objectTypes) || []).find(type => type.path === path);
}

function schemaObjectFields(objectType) {
  return (objectType && (objectType.objectFields || objectType.fields)) || [];
}

function schemaObjectArrays(objectType) {
  return (objectType && objectType.arrays) || [];
}

function toggleArrayExpansion(selection, path, enabled) {
  selection.expandArrays = selection.expandArrays || [];
  if (enabled && !selection.expandArrays.includes(path)) selection.expandArrays.push(path);
  if (!enabled) selection.expandArrays = selection.expandArrays.filter(item => item !== path);
}

function renderArrayExpansionOptions(selection, selectionIndex, scope) {
  if (selection.kind !== 'object' || !(selection.arrays || []).length) return '';
  const attr = scope === 'primary' ? 'data-expand-primary-array' : 'data-expand-related-array';
  return `<div class="array-expansion-options">
    <span>Expand one-element arrays:</span>
    ${selection.arrays.map(array => `
      <label title="Expanded only when this array has exactly one entry; larger arrays are flagged">
        <input type="checkbox" ${attr}="${esc(array.path)}" data-selection-index="${selectionIndex}"
          ${(selection.expandArrays || []).includes(array.path) ? 'checked' : ''} />
        <span>${esc(array.label)} <small>(${array.fields.length} fields)</small></span>
      </label>`).join('')}
  </div>`;
}

function addSchemaSelection(target, selection, schema) {
  if (selection.kind === 'object') {
    const objectType = schemaObject(schema, selection.path);
    const objectFields = schemaObjectFields(objectType);
    if (!objectFields.length) return false;
    if (target.some(item => item.kind === 'object' && item.path === selection.path)) return false;
    // The object selection supersedes individual fields already selected from
    // that same object; keeping both would duplicate CSV columns.
    for (let i = target.length - 1; i >= 0; i--) {
      if (target[i].kind !== 'object' && target[i].path === selection.path) target.splice(i, 1);
    }
    target.push({
      ...selection,
      fieldCount: objectFields.length,
      arrays: schemaObjectArrays(objectType),
      expandArrays: [],
    });
    return true;
  }
  if (target.some(item =>
      (item.kind === 'object' && item.path === selection.path) ||
      (item.name === selection.name && item.path === selection.path))) return false;
  target.push(selection);
  return true;
}

function expandFieldSelections(selections, schema) {
  const expanded = [];
  const seen = new Set();
  for (const selection of selections) {
    const fields = selection.kind === 'object'
      ? schemaObjectFields(schemaObject(schema, selection.path)).map(field => ({
          name: field.name, path: selection.path, pathLabel: selection.pathLabel,
        }))
      : [selection];
    for (const field of fields) {
      const key = `${field.name}\u0000${field.path || ''}`;
      if (!seen.has(key)) { seen.add(key); expanded.push(field); }
    }
  }
  return expanded;
}

function arrayExpansionRequests(selections) {
  return selections.flatMap(selection => selection.kind === 'object'
    ? (selection.expandArrays || []).map(arrayPath => ({
        objectPath: selection.path, arrayPath,
      }))
    : []);
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

function selectionPaths(selections) {
  return new Set(selections.map(item => item.path ?? null));
}

function reconcileJoinSelection(rel, key, selections) {
  const join = rel[key];
  if (!join || !selections.length) return;
  const paths = selectionPaths(selections);
  if (paths.size !== 1 || !paths.has(join.path ?? null)) rel[key] = null;
}

function reconcileJoinSelections() {
  for (const rel of search.relatedFiles) {
    reconcileJoinSelection(rel, 'primaryJoin', search.fields);
    reconcileJoinSelection(rel, 'relatedJoin', rel.fields);
  }
}

function scopedSchemaFieldOptions(data, placeholder, selected, selections) {
  const paths = selectionPaths(selections);
  const restrict = selections.length > 0 && paths.size === 1;
  const fields = schemaFields(data).filter(field =>
    !restrict || paths.has(field.path ?? null));
  return `<option value="">${esc(placeholder)}</option>` + fields.map(field => {
    const value = JSON.stringify(field);
    const isSelected = selected && selected.name === field.name && selected.path === field.path;
    return `<option value='${esc(value)}'${isSelected ? ' selected' : ''}>` +
      `${esc(field.name)} · ${esc(field.pathLabel)}</option>`;
  }).join('');
}

function schemaOutputOptions(data, placeholder) {
  const objects = (data && data.objectTypes) || [];
  return `<option value="">${esc(placeholder)}</option>` + objects.map(type => {
    const objectValue = JSON.stringify({kind: 'object', path: type.path, pathLabel: type.label});
    const objectFieldCount = schemaObjectFields(type).length;
    const fieldOptions = (type.fields || []).map(field => {
      const value = JSON.stringify({name: field.name, path: type.path, pathLabel: type.label});
      return `<option value='${esc(value)}'>${esc(field.name)}</option>`;
    }).join('');
    return `<optgroup label="${esc(type.label)} (${type.count.toLocaleString()})">` +
      `<option value='${esc(objectValue)}'>All fields from ${esc(type.label)} (${objectFieldCount})</option>` +
      fieldOptions + `</optgroup>`;
  }).join('');
}

function renderRelatedFiles() {
  const box = document.getElementById('related-files');
  const primarySchema = search.schema && search.schema.data;
  const allowed = new Set([search.integration, 'UnitEditor']);
  if (search.integration === 'RentCafe') allowed.add('Voyager');
  const integrations = search.availableIntegrations.filter(i => allowed.has(i));

  box.innerHTML = search.relatedFiles.map((rel, i) => {
    const files = search.availableFilesByIntegration[rel.integration] ||
      (rel.integration === search.integration ? search.availableFiles : []);
    const fileOptions = '<option value="">Select a file…</option>' +
      files.filter(f => !(rel.integration === search.integration && f === search.fileName)).map(f =>
        `<option value="${esc(f)}"${f === rel.filename ? ' selected' : ''}>${esc(f)}</option>`).join('');
    const ready = rel.filename && rel.schema;
    const fieldOptions = ready
      ? schemaOutputOptions(rel.schema, 'Add a field or entire object…') :
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
        <span class="field-label">Join type</span>
        <select data-join-type>
          <option value="inner"${rel.joinType === 'inner' ? ' selected' : ''}>Inner join — matching rows only</option>
          <option value="left"${(rel.joinType || 'left') === 'left' ? ' selected' : ''}>Left outer join — all primary rows</option>
          <option value="right"${rel.joinType === 'right' ? ' selected' : ''}>Right outer join — all secondary rows</option>
          <option value="full"${rel.joinType === 'full' ? ' selected' : ''}>Full outer join — all rows from both files</option>
        </select>
        <span class="field-label">Join fields</span>
        <select data-primary-join ${primarySchema ? '' : 'disabled'}>
          ${scopedSchemaFieldOptions(primarySchema, 'Primary file field…', rel.primaryJoin, search.fields)}
        </select>
        <select data-related-join>
          ${scopedSchemaFieldOptions(rel.schema, 'Related file field…', rel.relatedJoin, rel.fields)}
        </select>
        <span class="field-hint">Join fields are limited to the selected output object on each side.</span>
        <select data-related-field>${fieldOptions}</select>
        <div class="related-file-fields">
          ${rel.fields.map((f, j) => `<div class="related-field-selection">
            <span class="related-field-chip">${f.kind === 'object'
              ? `All fields (${f.fieldCount}) · ${esc(f.pathLabel)}` : esc(f.name)}
              <button type="button" data-remove-related-field="${j}" data-related-index="${i}">×</button>
            </span>
            ${renderArrayExpansionOptions(f, j, 'related')}
          </div>`).join('')}
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
               && search.asOfValid && search.resultLimitValid
               && !search.running && !search.indexing;
  const ready = base && (search.searchBy === 'fields'
    ? search.fields.length > 0 && search.relatedFiles.every(rel =>
        rel.filename && rel.schema && rel.primaryJoin && rel.relatedJoin && rel.fields.length > 0) &&
      search.conditionGroups.every(group => group.conditions.length > 0 &&
        group.conditions.every(condition => condition.field && condition.value !== ''))
    : search.text.trim());
  document.getElementById('btn-run-search').disabled = !ready;
}

function renderSearchLimitFeedback() {
  const input = document.getElementById('input-result-limit');
  const hint = document.getElementById('result-limit-hint');
  if (!input || !hint) return;
  const raw = input.value.trim();
  if (!raw) {
    search.resultLimitValid = true;
    hint.className = 'field-hint';
    hint.textContent = search.searchBy === 'fields'
      ? 'Defaults to the 200,000-row CSV safety limit'
      : 'Defaults to 500 text matches';
  } else if (/^[1-9]\d*$/.test(raw) && Number(raw) <= 200000) {
    search.resultLimitValid = true;
    hint.className = 'field-hint ok';
    hint.textContent = `Stops after ${Number(raw).toLocaleString()} result${Number(raw) !== 1 ? 's' : ''}`;
  } else {
    search.resultLimitValid = false;
    hint.className = 'field-hint err';
    hint.textContent = 'Enter a whole number from 1 to 200,000';
  }
  syncSearchButton();
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
    includeStudents: search.includeStudents,
    limit:        search.resultLimit.trim(),
    asOf:        search.asOf,
  };
  // Manual (no-path) entries go as bare strings; schema-picked ones carry
  // their path so the server matches the exact object type shown, not just
  // the name — the server accepts either shape per field.
  if (fieldsMode) {
    body.fields = expandFieldSelections(search.fields, search.schema && search.schema.data)
      .map(f => f.path ? { name: f.name, path: f.path } : f.name);
    body.arrayExpansions = arrayExpansionRequests(search.fields);
    body.unique = search.unique;
    body.relatedFiles = search.relatedFiles.map(rel => ({
      integration: rel.integration,
      filename: rel.filename,
      primaryJoin: rel.primaryJoin,
      relatedJoin: rel.relatedJoin,
      joinType: rel.joinType || 'left',
      fields: expandFieldSelections(rel.fields, rel.schema)
        .map(f => f.path ? { name: f.name, path: f.path } : f.name),
      arrayExpansions: arrayExpansionRequests(rel.fields),
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

async function onAgentIntegrationChange() {
  search.agentIndex = null;
  renderAgentIndexStatus();
  syncAvailabilityButton();
  await refreshAgentIndexStatus();
}

function agentIndexState(integration, data) {
  if (!data || data.state !== 'ready' || !data.builtAt || !Number(data.buildings || 0)) {
    return {integration, state: 'none', buildings: data?.buildings || 0};
  }
  const age = Math.max(0, Date.now() - data.builtAt * 1000);
  return {...data, integration, age,
          state: age > AGENT_INDEX_MAX_AGE_MS ? 'stale' : 'ready'};
}

async function refreshAgentIndexStatus() {
  const selected = document.getElementById('agent-sel-integration').value;
  if (!selected) {
    search.agentIndex = null;
    renderAgentIndexStatus();
    syncAvailabilityButton();
    return;
  }
  const integrations = selected === '__all__'
    ? search.availabilityIntegrations : [selected];
  try {
    const states = await Promise.all(integrations.map(async integration => {
      const response = await fetch(`/api/index/status?integration=${encodeURIComponent(integration)}`);
      const data = await response.json();
      return agentIndexState(integration, data);
    }));
    if (document.getElementById('agent-sel-integration').value !== selected) return;
    const needsRefresh = states.filter(item => item.state !== 'ready');
    const missing = states.filter(item => item.state === 'none');
    if (selected === '__all__') {
      search.agentIndex = {
        state: missing.length ? 'none' : (needsRefresh.length ? 'stale' : 'ready'),
        states,
        needsRefresh: needsRefresh.map(item => item.integration),
        missing: missing.map(item => item.integration),
        buildings: states.reduce((sum, item) => sum + Number(item.buildings || 0), 0),
      };
    } else {
      search.agentIndex = {
        ...states[0],
        needsRefresh: needsRefresh.map(item => item.integration),
        missing: missing.map(item => item.integration),
      };
      // The primary index determines whether the agent can run. Render it
      // immediately; companion metadata is optional and must never leave the
      // entire panel stuck at "Checking index freshness…".
      renderAgentIndexStatus();
      syncAvailabilityButton();
      if (selected === 'RentCafe' && search.agentIndex.state !== 'none') {
        const controller = new AbortController();
        const timeout = setTimeout(() => controller.abort(), 5000);
        try {
          const response = await fetch('/api/index/status?integration=YardiVoyager', {
            signal: controller.signal,
          });
          if (!response.ok) throw new Error('Companion status unavailable');
          const data = await response.json();
          if (document.getElementById('agent-sel-integration').value !== selected) return;
          search.agentIndex.companion = agentIndexState('YardiVoyager', data);
        } catch {
          if (document.getElementById('agent-sel-integration').value === selected) {
            search.agentIndex.companion = {integration: 'YardiVoyager', state: 'none', buildings: 0};
          }
        } finally {
          clearTimeout(timeout);
        }
      }
    }
  } catch {
    if (document.getElementById('agent-sel-integration').value !== selected) return;
    search.agentIndex = {state: 'none', needsRefresh: integrations, missing: integrations};
  }
  renderAgentIndexStatus();
  syncAvailabilityButton();
}

function renderAgentIndexStatus() {
  const bar = document.getElementById('agent-index-status');
  const text = document.getElementById('agent-index-text');
  const btn = document.getElementById('btn-agent-index');
  const percent = document.getElementById('agent-index-percent');
  const companionBtn = document.getElementById('btn-agent-companion');
  const selected = document.getElementById('agent-sel-integration').value;
  companionBtn.hidden = true;
  if (!selected) {
    bar.className = '';
    return;
  }
  const idx = search.agentIndex;
  bar.className = `show ${idx?.state || 'none'}`;
  if (!idx) {
    text.textContent = 'Checking index freshness…';
    btn.textContent = selected === 'RentCafe'
      ? 'Build or refresh RentCafe index'
      : 'Build or refresh index';
  } else if (selected === '__all__') {
    const total = search.availabilityIntegrations.length;
    const expired = idx.needsRefresh || [];
    const missing = idx.missing || [];
    if (missing.length) {
      text.textContent = `Index required for ${missing.length} of ${total} integrations: ${missing.join(', ')}`;
      btn.textContent = 'Re-index all';
    } else if (expired.length) {
      text.textContent = `${expired.length} of ${total} indexes are over 24 hours old · latest indexes can still be used`;
      btn.textContent = 'Re-index all';
    } else {
      text.textContent = `All ${total} integration indexes are current · ${idx.buildings.toLocaleString()} buildings`;
      btn.textContent = 'Re-index all';
    }
  } else if (idx.state === 'ready') {
    const sample = Number(idx.stats?.samplePercent || 100);
    text.textContent = `Indexed ${Number(idx.buildings || 0).toLocaleString()} buildings${sample < 100 ? ` · ${sample}% sample` : ''} · ${fmtAge(idx.age)} ago`;
    btn.textContent = selected === 'RentCafe' ? 'Refresh RentCafe index' : 'Re-index';
  } else if (idx.state === 'stale') {
    text.textContent = `Last indexed ${fmtAge(idx.age)} ago · latest index will be used`;
    btn.textContent = selected === 'RentCafe' ? 'Refresh RentCafe index' : 'Re-index';
  } else {
    text.textContent = 'Not indexed · index required to run';
    btn.textContent = selected === 'RentCafe' ? 'Build RentCafe index' : 'Build index';
  }
  // Index maintenance must remain available even if the status request is
  // delayed or fails. With no metadata, buildAgentIndex safely does a build.
  btn.disabled = search.indexing || search.running;
  percent.disabled = search.indexing || search.running;
  if (selected === 'RentCafe' && idx && idx.state !== 'none') {
    const companion = idx.companion;
    companionBtn.hidden = false;
    if (!companion || companion.state === 'none') {
      companionBtn.textContent = 'Build Voyager companion';
      companionBtn.title = 'Index recent Voyager snapshots for the buildings in this RentCafe index';
    } else {
      companionBtn.textContent = companion.state === 'stale'
        ? 'Refresh Voyager companion'
        : `Voyager: ${Number(companion.buildings || 0).toLocaleString()} buildings`;
      companionBtn.title = `${fmtAge(companion.age)} ago · click to rebuild for the current RentCafe building scope`;
    }
    companionBtn.disabled = search.indexing || search.running || !idx;
  }
}

async function buildAgentCompanionIndex() {
  const selected = document.getElementById('agent-sel-integration').value;
  if (selected !== 'RentCafe' || search.indexing || search.running) return;
  // A companion cannot define the RentCafe building scope. If stale UI state
  // exposes this action before a primary index exists, build RentCafe first.
  if (!search.agentIndex || search.agentIndex.state === 'none') {
    await buildAgentIndex();
    return;
  }
  search.indexing = true;
  renderAgentIndexStatus();
  syncAvailabilityButton();
  const results = document.getElementById('availability-results');
  results.innerHTML = '<div class="pane-msg">Building Voyager companion index for current RentCafe buildings…</div>';
  try {
    const response = await fetch('/api/index/companion', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({integration: 'RentCafe'}),
    });
    const data = await response.json();
    if (!response.ok || data.error) throw new Error(data.message || data.error || 'Could not build Voyager companion index');
    const result = await pollJob(data.jobId, 'Building Voyager companion index');
    const unavailable = Number(result?.unavailableWithin24Hours || 0);
    results.innerHTML = `<div class="pane-msg">Voyager companion index ready · ${Number(result?.buildings || 0).toLocaleString()} buildings${unavailable ? ` · ${unavailable.toLocaleString()} without a Voyager sync in the last 24 hours` : ''}.</div>`;
  } catch (error) {
    results.innerHTML = `<div class="pane-msg">Voyager companion index failed: ${esc(error.message)}</div>`;
  } finally {
    search.indexing = false;
    hideProgress();
    await refreshAgentIndexStatus();
    renderAgentIndexStatus();
    syncAvailabilityButton();
  }
}

async function buildAgentIndex() {
  const selected = document.getElementById('agent-sel-integration').value;
  if (!selected || search.indexing || search.running) return;
  const integrations = selected === '__all__'
    ? search.availabilityIntegrations
    : [selected];
  const samplePercent = Number(document.getElementById('agent-index-percent').value || 100);
  const referenceTime = document.getElementById('agent-asof').value.trim();
  const missingIndexes = new Set(search.agentIndex?.missing ||
    (search.agentIndex?.state === 'none' && selected !== '__all__' ? [selected] : []));
  search.indexing = true;
  renderAgentIndexStatus();
  syncAvailabilityButton();
  const results = document.getElementById('availability-results');
  try {
    const rebuilt = [];
    for (const [position, integration] of integrations.entries()) {
      const action = missingIndexes.has(integration) ? 'Building new index for' : 'Re-indexing';
      results.innerHTML = `<div class="pane-msg">${action} ${esc(integration)} at ${samplePercent}% (${position + 1} of ${integrations.length})…</div>`;
      const response = await fetch('/api/index/build', {
        method: 'POST', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({integration, samplePercent, referenceTime}),
      });
      const data = await response.json();
      if (!response.ok || data.error) throw new Error(data.error || `Could not index ${integration}`);
      rebuilt.push({integration, result: await pollJob(
        data.jobId, `Indexing ${integration} · ${samplePercent}% sample`)});
    }
    const empty = rebuilt.filter(item => !Number(item.result?.buildings || 0));
    if (empty.length) {
      results.innerHTML = `<div class="pane-msg">Indexing completed, but no current snapshots were found for: ${esc(empty.map(item => item.integration).join(', '))}. The Availability Agent remains unavailable for those integrations.</div>`;
    } else {
      results.innerHTML = '<div class="pane-msg">Indexing complete. The Availability Agent is ready to run.</div>';
    }
  } catch (error) {
    results.innerHTML = `<div class="pane-msg">Index maintenance failed: ${esc(error.message)}</div>`;
  } finally {
    search.indexing = false;
    hideProgress();
    await refreshAgentIndexStatus();
    renderAgentIndexStatus();
    syncAvailabilityButton();
  }
}

function renderAgentAsOfFeedback() {
  const raw = document.getElementById('agent-asof').value;
  const hint = document.getElementById('agent-asof-hint');
  const parsed = parseAsOfClient(raw);
  search.agentAsOfValid = parsed.ok;
  if (!raw.trim()) {
    hint.className = 'field-hint';
    hint.textContent = 'Uses the latest snapshots recorded in the index';
  } else if (parsed.ok) {
    hint.className = 'field-hint ok';
    hint.textContent = `→ latest sync in the 24 hours before ${fmtDateUTC(parsed.dt.toISOString())} UTC`;
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
  const idx = search.agentIndex;
  const indexReady = idx && (idx.state === 'ready' || idx.state === 'stale');
  const ready = document.getElementById('agent-sel-integration').value &&
    indexReady && search.agentAsOfValid && search.agentLimitValid &&
    !search.running && !search.indexing;
  document.getElementById('btn-run-availability').disabled = !ready;
  const stop = document.getElementById('btn-stop-availability');
  stop.hidden = !search.running || !search.availabilityJobId;
  stop.disabled = search.availabilityStopping;
  stop.textContent = search.availabilityStopping
    ? 'Finalizing collected data…' : 'Stop and generate CSV';
}

async function stopAvailabilityAgent() {
  if (!search.availabilityJobId || search.availabilityStopping) return;
  search.availabilityStopping = true;
  syncAvailabilityButton();
  try {
    const response = await fetch('/api/job/stop', {
      method: 'POST', headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({id: search.availabilityJobId}),
    });
    const data = await response.json();
    if (!response.ok || data.error) throw new Error(data.error || 'Could not stop availability job');
    showProgress('Stop requested · generating CSV from collected data…');
  } catch (error) {
    search.availabilityStopping = false;
    syncAvailabilityButton();
    document.getElementById('availability-results').innerHTML =
      `<div class="pane-msg">Could not stop: ${esc(error.message)}</div>`;
  }
}

async function runAvailabilityAgent() {
  search.running = true;
  const btn = document.getElementById('btn-run-availability');
  const original = btn.textContent;
  btn.textContent = 'Starting…';
  renderAgentIndexStatus();
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
      includeNotLaunchedOnLeasing: document.getElementById('agent-include-not-launched-leasing').checked,
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
      break;
    }
    if (data.error && (data.error === 'no-index' || data.error.includes('index'))) {
      throw new Error(data.message || data.error);
    }
    if (data.error) throw new Error(data.error);
    search.availabilityJobId = data.jobId;
    search.availabilityStopping = false;
    syncAvailabilityButton();
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
    search.availabilityJobId = null;
    search.availabilityStopping = false;
    btn.textContent = original;
    hideProgress();
    await refreshAgentIndexStatus();
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
  const panelId = kind === 'availability'
    ? 'saved-availability'
    : (kind === 'dynamic_pricing_validation'
      ? 'saved-dynamic-pricing-validation' : 'saved-search');
  const panel = document.getElementById(panelId);
  const toggle = panel?.querySelector('.saved-toggle');
  if (!panel || !toggle) return;
  const open = panel.classList.toggle('open');
  toggle.setAttribute('aria-expanded', String(open));
}

function historyTitle(entry) {
  if (entry.name) return entry.name;
  if (entry.kind === 'dynamic_pricing_validation') {
    const status = String(entry.details?.validationStatus || '').replace('-', ' ');
    return `Unknown-mode validation${status ? ` · ${status}` : ''}`;
  }
  return entry.kind === 'availability'
    ? `Availability · ${entry.integration || 'Unknown integration'}`
    : `Search · ${entry.fileName || entry.integration || 'CSV export'}`;
}

function renderSavedHistory() {
  ['fields', 'availability', 'dynamic_pricing_validation'].forEach(kind => {
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
  const listId = kind === 'availability'
    ? 'history-availability-list'
    : (kind === 'dynamic_pricing_validation'
      ? 'history-dynamic-pricing-validation-list' : 'history-search-list');
  const list = document.getElementById(listId);
  if (!list) return;
  if (!entries.length) {
    const label = kind === 'availability'
      ? 'Availability Agent results'
      : (kind === 'dynamic_pricing_validation'
        ? 'Unknown-mode validations' : 'Search results');
    list.innerHTML = `<div class="history-empty">No saved ${label}</div>`;
    return;
  }
  list.innerHTML = entries.map(entry => {
    const when = entry.createdAt ? new Date(entry.createdAt).toLocaleString() : '';
    const count = Number(entry.rowCount || 0).toLocaleString();
    const status = entry.available ? '' : ' · expired';
    const integration = entry.kind === 'dynamic_pricing_validation'
      ? `${count} matrices tested` : `${entry.integration || ''} · ${count} rows`;
    return `<div class="history-item ${entry.available ? '' : 'expired'}" data-history-id="${esc(entry.id)}" role="button" tabindex="0">
      <button type="button" class="history-star ${entry.favorite ? 'favorite' : ''}" data-history-favorite="${esc(entry.id)}" title="${entry.favorite ? 'Unfavorite' : 'Favorite'}">${entry.favorite ? '★' : '☆'}</button>
      <div class="history-copy"><div class="history-title">${esc(historyTitle(entry))}</div>
        <div class="history-meta">${esc(integration)} · ${esc(when)}${status}</div></div>
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

async function openHistoryEntry(jobId) {
  const entry = historyState.entries.find(item => item.id === jobId);
  if (!entry || !entry.available) return;
  if (entry.kind === 'dynamic_pricing_validation') {
    await openDynamicPricingValidationHistory(entry);
    return;
  }
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
  if (data.includeNotLaunchedOnLeasing === false) bits.push('communities not launched on Leasing excluded');
  if (data.supplementalUnits) bits.push(`${data.supplementalUnits.toLocaleString()} Voyager-only unit${data.supplementalUnits !== 1 ? 's' : ''} added as Lease Signed`);
  if (data.supplementalErrors) bits.push(`${data.supplementalErrors.toLocaleString()} Voyager supplement${data.supplementalErrors !== 1 ? 's' : ''} unreadable`);
  if (data.waitFiltered) bits.push(`${data.waitFiltered.toLocaleString()} unit${data.waitFiltered !== 1 ? 's' : ''} with “wait” in the name excluded`);
  if (data.unitDetailsOnlyCount) bits.push(`${data.unitDetailsOnlyCount.toLocaleString()} unit${data.unitDetailsOnlyCount !== 1 ? 's' : ''} found only in unit-details`);
  if (data.stopped) bits.push('stopped early; CSV contains collected data');
  if (data.limit) bits.push(data.limited ? `limited to ${Number(data.limit).toLocaleString()}` : `limit ${Number(data.limit).toLocaleString()} not reached`);
  if (data.asOf) bits.push(`as of ${fmtDateUTC(data.asOf)} UTC`);
  if (data.errors) bits.push(`${data.errors} unreadable`);
  if (data.noSnapshot) bits.push(`${data.noSnapshot} had no snapshot in the preceding 24-hour window`);
  if (data.failedIntegrations?.length) bits.push(`failed: ${data.failedIntegrations.join(', ')}`);
  if (data.skippedIntegrations?.length) bits.push(`${data.stopped ? 'skipped after stop' : 'skipped after limit'}: ${data.skippedIntegrations.join(', ')}`);
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
  if (data.includeStudents === false) bits.push('student housing excluded');
  if (data.noSnapshot)  bits.push(`${data.noSnapshot.toLocaleString()} had no snapshot in the preceding 24-hour window`);
  if (data.truncated)   bits.push(`result limit reached (${data.matches.length.toLocaleString()})`);
  if (data.errors)      bits.push(`${data.errors} unreadable`);
  if (data.filterNote)  bits.push(data.filterNote);
  if (data.enrichError) bits.push('building details unavailable');
  summary.textContent = bits.join(' · ');
  summary.classList.add('show');
  if (data.enrichCredentialIssue) showSnowflakeCredentialPrompt(data.enrichError);

  if (!data.matches.length) {
    results.innerHTML =
      `<div class="pane-msg">No indexed snapshot contains “${esc(data.text)}”</div>`;
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
  if (data.includeStudents === false) bits.push('student housing excluded');
  if (data.unique)      bits[0] = `${data.rowCount.toLocaleString()} unique row${data.rowCount !== 1 ? 's' : ''}`;
  if (data.noSnapshot)  bits.push(`${data.noSnapshot.toLocaleString()} had no snapshot in the preceding 24-hour window`);
  if (data.truncated)   bits.push(`result limit reached (${data.rowCount.toLocaleString()} rows)`);
  if (data.errors)      bits.push(`${data.errors} unreadable`);
  if (data.filterNote)  bits.push(data.filterNote);
  if (data.enrichError) bits.push('building details unavailable');
  summary.textContent = bits.join(' · ');
  summary.classList.add('show');
  if (data.enrichCredentialIssue) showSnowflakeCredentialPrompt(data.enrichError);

  if (!data.rowCount) {
    results.innerHTML = `<div class="pane-msg">None of the searched indexed snapshots had a value for ` +
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

// ── Dynamic Pricing Cadence ─────────────────────────────────────────────────

const DP_REPORT_COLUMNS = [
  {key: 'orgName', label: 'Organization'},
  {key: 'buildingName', label: 'Community'},
  {key: 'buildingId', label: 'Building ID'},
  {key: 'latestSync', label: 'Latest Sync'},
  {key: 'cadenceDays', label: 'Cadence (Days)', numeric: true},
  {key: 'cadenceEvidence', label: 'Cadence Evidence'},
  {key: 'knownCadenceStatus', label: 'Known Verification'},
  {key: 'unknownCadenceStatus', label: 'Unknown Discovery'},
  {key: 'cycleAlignment', label: 'Cycle Alignment'},
  {key: 'unitCount', label: 'Units', numeric: true},
  {key: 'currentApiCalls', label: 'Current API Calls', numeric: true},
  {key: 'knownBootstrapApiCalls', label: 'Known Mode Calls', numeric: true},
  {key: 'trustedBootstrapApiCalls', label: 'Trusted Mode Calls', numeric: true},
  {key: 'unknownBootstrapApiCalls', label: 'Unknown Mode Calls', numeric: true},
  {key: 'knownApiCallsSaved', label: 'Known Mode Saved', numeric: true},
  {key: 'trustedApiCallsSaved', label: 'Trusted Mode Saved', numeric: true},
  {key: 'unknownApiCallsSaved', label: 'Unknown Mode Saved', numeric: true},
  {key: 'knownApiCallsSavedPct', label: 'Known Saved (%)', numeric: true},
  {key: 'trustedApiCallsSavedPct', label: 'Trusted Saved (%)', numeric: true},
  {key: 'unknownApiCallsSavedPct', label: 'Unknown Saved (%)', numeric: true},
  {key: 'knownReconstructionAccuracyPct', label: 'Known Accuracy (%)', numeric: true},
  {key: 'trustedReconstructionAccuracyPct', label: 'Trusted Accuracy (%)', numeric: true},
  {key: 'unknownReconstructionAccuracyPct', label: 'Unknown Accuracy (%)', numeric: true},
  {key: 'knownBootstrapApiCallDates', label: 'Known Call Dates'},
  {key: 'trustedBootstrapApiCallDates', label: 'Trusted Call Dates'},
  {key: 'unknownBootstrapApiCallDates', label: 'Unknown Call Dates'},
];
const DP_VALIDATION_COLUMNS = [
  {key: 'orgName', label: 'Organization'},
  {key: 'buildingName', label: 'Community'},
  {key: 'buildingId', label: 'Building ID', numeric: true},
  {key: 'latestSync', label: 'Latest Sync'},
  {key: 'cadenceDays', label: 'Cadence', numeric: true},
  {key: 'unitCount', label: 'Units', numeric: true},
  {key: 'currentApiCalls', label: 'Current Calls', numeric: true},
  {key: 'unknownBootstrapApiCalls', label: 'Unknown Calls', numeric: true},
  {key: 'unknownApiCallsSaved', label: 'Calls Saved', numeric: true},
  {key: 'unknownApiCallsSavedPct', label: '% Saved', numeric: true},
  {key: 'unknownReconstructionAccuracyPct', label: 'Accuracy', numeric: true},
  {key: 'unknownCadenceStatus', label: 'Cadence Result'},
];
const DP_VALIDATION_ORG_COLUMNS = [
  {key: 'orgName', label: 'Organization'},
  {key: 'orgId', label: 'Org ID', numeric: true},
  {key: 'communityCount', label: 'Communities', numeric: true},
  {key: 'currentApiCalls', label: 'Current Calls', numeric: true},
  {key: 'unknownBootstrapApiCalls', label: 'Unknown Calls', numeric: true},
  {key: 'unknownApiCallsSaved', label: 'Calls Saved', numeric: true},
  {key: 'unknownApiCallsSavedPct', label: '% Saved', numeric: true},
  {key: 'unknownReconstructionAccuracyPct', label: 'Accuracy', numeric: true},
  {key: 'matricesPassed', label: 'Passed', numeric: true},
  {key: 'matricesFailed', label: 'Failed', numeric: true},
];
const DP_PRICE_GRADIENT_START_HUE = 125;
const DP_PRICE_GRADIENT_END_HUE = 350;

function dpSetStatus(message, isError = false) {
  const el = document.getElementById('dp-status');
  el.textContent = message;
  el.style.color = isError ? '#f85149' : '#8b949e';
}

function dpFormatShortDate(value) {
  const match = String(value || '').match(/^(\d{4})-(\d{2})-(\d{2})/);
  return match ? `${Number(match[2])}/${Number(match[3])}` : String(value || '—');
}

function dpFormatTimestamp(value) {
  if (!value) return '—';
  const parsed = new Date(value);
  return Number.isNaN(parsed.getTime()) ? String(value) : parsed.toLocaleString();
}

function dpDatesHtml(dates) {
  const values = dates || [];
  if (!values.length) return '<span class="si-pending">none</span>';
  return values.map(day => esc(dpFormatShortDate(day))).join(', ');
}

function dpCadenceHtml(row) {
  if (row.cadenceIsLowerBound && row.cadenceDays != null) {
    return `<span class="dp-cadence-common">≥ ${esc(String(row.cadenceDays))}</span>`;
  }
  if (row.cadenceDays != null) {
    return `<span class="dp-cadence-common">${esc(String(row.cadenceDays))}</span>`;
  }
  return `<span class="si-pending">${esc(row.cadence || '—')}</span>`;
}

function dpCadenceEvidenceText(row) {
  if (row.error) return 'Unavailable';
  if (row.cadenceIsLowerBound) {
    const prefix = row.pricingDoesNotChange
      ? 'No price changes observed'
      : 'No complete interior ranges';
    return `${prefix} · cadence is at least ${row.cadenceLowerBoundDays || row.cadenceDays} days`;
  }
  if (row.pricingDoesNotChange) return 'Pricing Does Not Change';
  const count = row.cadenceEvidenceRangeCount || 0;
  const units = row.cadenceEvidenceUnitCount || 0;
  const lengths = row.cadenceEvidenceLengths || [];
  const detail = count
    ? `${count} interior range${count === 1 ? '' : 's'} across ${units} unit${units === 1 ? '' : 's'}; lengths ${lengths.join(', ')} days`
    : 'no complete interior ranges';
  return `${row.cadenceConfidence || 'Insufficient Data'} · ${detail}`;
}

function dpColumnText(row, key, forExport = false) {
  if (key.endsWith('BootstrapApiCallDates')) {
    return (row[key] || []).map(dpFormatShortDate).join(', ');
  }
  if (key === 'cadenceEvidence') return dpCadenceEvidenceText(row);
  if (key === 'latestSync') {
    return forExport ? String(row.latestSync || '') : dpFormatTimestamp(row.latestSync);
  }
  return String(row[key] ?? '');
}

function dpMatchesFilter(row, column, query) {
  const filter = String(query || '').trim();
  if (!filter) return true;
  const rawValue = row[column.key];
  if (column.numeric) {
    const match = filter.match(/^(<=|>=|!=|=|<|>)?\s*(-?\d+(?:\.\d+)?)$/);
    if (match) {
      const actual = Number(rawValue);
      const expected = Number(match[2]);
      if (!Number.isFinite(actual)) return false;
      const op = match[1] || '=';
      if (op === '<') return actual < expected;
      if (op === '<=') return actual <= expected;
      if (op === '>') return actual > expected;
      if (op === '>=') return actual >= expected;
      if (op === '!=') return actual !== expected;
      return actual === expected;
    }
  }
  const haystack = `${dpColumnText(row, column.key)} ${String(rawValue ?? '')}`.toLocaleLowerCase();
  return haystack.includes(filter.toLocaleLowerCase());
}

function dpColumnSortValue(row, key) {
  if (key.endsWith('BootstrapApiCallDates')) {
    return (row[key] || [])[0] || '';
  }
  if (key === 'cadenceEvidence') return dpCadenceEvidenceText(row);
  if (key === 'latestSync') return row.latestSync || '';
  return row[key];
}

function dpVisibleRows(rows) {
  const filtered = (rows || []).filter(row => DP_REPORT_COLUMNS.every(column =>
    dpMatchesFilter(row, column, dynamicPricing.filters[column.key])
  ));
  const column = DP_REPORT_COLUMNS.find(item => item.key === dynamicPricing.sortKey);
  if (!column) return filtered;
  return filtered.map((row, index) => ({row, index})).sort((left, right) => {
    const a = dpColumnSortValue(left.row, column.key);
    const b = dpColumnSortValue(right.row, column.key);
    const aEmpty = a == null || a === '';
    const bEmpty = b == null || b === '';
    if (aEmpty && bEmpty) return left.index - right.index;
    if (aEmpty) return 1;
    if (bEmpty) return -1;
    let compared;
    if (column.numeric) {
      compared = Number(a) - Number(b);
    } else {
      compared = String(a).localeCompare(
        String(b), undefined,
        {numeric: true, sensitivity: 'base'});
    }
    if (!compared) return left.index - right.index;
    return dynamicPricing.sortDir === 'asc' ? compared : -compared;
  }).map(item => item.row);
}

function dpSetSort(key) {
  if (dynamicPricing.sortKey === key) {
    dynamicPricing.sortDir = dynamicPricing.sortDir === 'asc' ? 'desc' : 'asc';
  } else {
    dynamicPricing.sortKey = key;
    dynamicPricing.sortDir = 'asc';
  }
  dpRenderResult(dynamicPricing.result, !!dynamicPricing.result?.partial);
}

function dpSortIndicator(key) {
  if (dynamicPricing.sortKey !== key) return '';
  return dynamicPricing.sortDir === 'asc' ? ' ▲' : ' ▼';
}

function dpValidationActiveColumns() {
  return dynamicPricing.validationView === 'organization'
    ? DP_VALIDATION_ORG_COLUMNS : DP_VALIDATION_COLUMNS;
}

function dpValidationSortedRows(rows) {
  const column = dpValidationActiveColumns().find(
    item => item.key === dynamicPricing.validationSortKey);
  if (!column) return rows || [];
  return (rows || []).map((row, index) => ({row, index})).sort((left, right) => {
    const a = dpColumnSortValue(left.row, column.key);
    const b = dpColumnSortValue(right.row, column.key);
    const aEmpty = a == null || a === '';
    const bEmpty = b == null || b === '';
    if (aEmpty && bEmpty) return left.index - right.index;
    if (aEmpty) return 1;
    if (bEmpty) return -1;
    const compared = column.numeric
      ? Number(a) - Number(b)
      : String(a).localeCompare(
          String(b), undefined, {numeric: true, sensitivity: 'base'});
    if (!compared) return left.index - right.index;
    return dynamicPricing.validationSortDir === 'asc' ? compared : -compared;
  }).map(item => item.row);
}

function dpSetValidationSort(key) {
  if (dynamicPricing.validationSortKey === key) {
    dynamicPricing.validationSortDir =
      dynamicPricing.validationSortDir === 'asc' ? 'desc' : 'asc';
  } else {
    dynamicPricing.validationSortKey = key;
    dynamicPricing.validationSortDir = 'asc';
  }
  dpRenderValidationResult(
    dynamicPricing.validationResult,
    dynamicPricing.validationResult?.partial === true);
}

function dpSetValidationView(view) {
  const next = view === 'organization' ? 'organization' : 'community';
  if (dynamicPricing.validationView === next) return;
  dynamicPricing.validationView = next;
  const columns = dpValidationActiveColumns();
  if (!columns.some(column => column.key === dynamicPricing.validationSortKey)) {
    dynamicPricing.validationSortKey = 'unknownApiCallsSaved';
    dynamicPricing.validationSortDir = 'desc';
  }
  dpRenderValidationResult(
    dynamicPricing.validationResult,
    dynamicPricing.validationResult?.partial === true);
}

function dpValidationHeaderHtml() {
  return dpValidationActiveColumns().map(column => {
    const active = dynamicPricing.validationSortKey === column.key;
    const ariaSort = active
      ? (dynamicPricing.validationSortDir === 'asc'
          ? 'ascending' : 'descending')
      : 'none';
    const indicator = active
      ? (dynamicPricing.validationSortDir === 'asc' ? ' ▲' : ' ▼')
      : '';
    return `<th class="dp-sortable${column.numeric ? ' dp-num' : ''}" aria-sort="${ariaSort}">`
      + `<button type="button" data-dp-validation-sort="${esc(column.key)}" title="Sort by ${esc(column.label)}">`
      + `${esc(column.label)}<span class="dp-sort-indicator">${indicator}</span></button></th>`;
  }).join('');
}

function dpCsvCell(value) {
  let text = String(value ?? '');
  if (/^[=+\-@]/.test(text)) text = `'${text}`;
  return `"${text.replaceAll('"', '""')}"`;
}

function dpExportCsv() {
  const rows = dpVisibleRows(dynamicPricing.result?.rows || []);
  if (!rows.length) return;
  const lines = [
    DP_REPORT_COLUMNS.map(column => dpCsvCell(column.label)).join(','),
    ...rows.map(row => DP_REPORT_COLUMNS.map(column =>
      dpCsvCell(dpColumnText(row, column.key, true))).join(',')),
  ];
  const blob = new Blob([`\uFEFF${lines.join('\r\n')}`], {type: 'text/csv;charset=utf-8'});
  const url = URL.createObjectURL(blob);
  const anchor = document.createElement('a');
  anchor.href = url;
  anchor.download = `dynamic-pricing-cadence-${new Date().toISOString().slice(0, 10)}.csv`;
  document.body.appendChild(anchor);
  anchor.click();
  anchor.remove();
  setTimeout(() => URL.revokeObjectURL(url), 0);
}

function dpReportHeaderHtml() {
  return DP_REPORT_COLUMNS.map(column => {
    const active = dynamicPricing.sortKey === column.key;
    const ariaSort = active
      ? (dynamicPricing.sortDir === 'asc' ? 'ascending' : 'descending')
      : 'none';
    return `<th class="dp-sortable${column.numeric ? ' dp-num' : ''}" aria-sort="${ariaSort}">`
      + `<button type="button" data-dp-sort="${esc(column.key)}" title="Sort by ${esc(column.label)}">`
      + `${esc(column.label)}<span class="dp-sort-indicator">${dpSortIndicator(column.key)}</span></button></th>`;
  }).join('');
}

function dpReportFiltersHtml() {
  return DP_REPORT_COLUMNS.map(column => {
    const value = dynamicPricing.filters[column.key] || '';
    const placeholder = column.numeric ? '= 7 or >= 5' : 'Filter…';
    return `<th class="dp-filter-cell"><input type="text" data-dp-filter="${esc(column.key)}" `
      + `value="${esc(value)}" placeholder="${esc(placeholder)}" aria-label="Filter ${esc(column.label)}"></th>`;
  }).join('');
}

function dpCalendarDates(start, end) {
  if (!start || !end) return [];
  const values = [];
  const cursor = new Date(`${start}T00:00:00Z`);
  const final = new Date(`${end}T00:00:00Z`);
  while (cursor <= final) {
    values.push(cursor.toISOString().slice(0, 10));
    cursor.setUTCDate(cursor.getUTCDate() + 1);
  }
  return values;
}

function dpVisualizerSignatureId(unit, day) {
  const value = unit.pricingSignatureIds?.[day];
  return value == null ? null : Number(value);
}

function dpUnitPricingDates(unit) {
  return unit.visualPricingDates || unit.pricingDates || [];
}

function dpVisualizerMode(row, bid) {
  const selected = dynamicPricing.visualModes[bid] || 'known';
  if (row.retrievalPlans?.[selected]) return selected;
  return row.retrievalPlans?.known ? 'known' : (row.cadenceMode || 'known');
}

function dpVisualizerPlan(row, bid) {
  const mode = dpVisualizerMode(row, bid);
  return row.retrievalPlans?.[mode] || {
    mode,
    bootstrapApiCallDates: row.bootstrapApiCallDates || [],
    algorithmCallSteps: row.algorithmCallSteps || [],
    cadenceKnownAtCall: row.cadenceKnownAtCall,
    cadenceVerifiedAtCall: row.cadenceVerifiedAtCall,
    effectiveCadenceDays: row.cadenceDays,
    unitPhaseKnownAtCall: Object.fromEntries(
      (row.units || []).map((unit, index) => [index, unit.cyclePhaseKnownAtCall])),
    unitCycleBoundaryDates: Object.fromEntries(
      (row.units || []).map((unit, index) => [index, unit.cycleBoundaryDates || []])),
    unitBoundaryNotRequired: [],
    unitFutureAvailabilityAlignment: {},
    unitEndpointEqualityAtCall: {},
    unitLowerBoundInferenceAtCall: {},
    cadenceInvalidations: [],
  };
}

function dpVisualizerKnownDates(unit, row, step, plan, unitIndex) {
  const pricingDates = dpUnitPricingDates(unit);
  const calls = (plan.bootstrapApiCallDates || []).slice(0, step);
  const callSet = new Set(calls);
  const known = new Set(pricingDates.filter(day => callSet.has(day)));

  const endpointEqualityAt = plan.unitEndpointEqualityAtCall?.[unitIndex];
  if (endpointEqualityAt != null && step >= endpointEqualityAt) {
    pricingDates.forEach(day => known.add(day));
  }
  Object.entries(plan.unitLowerBoundInferenceAtCall?.[unitIndex] || {})
    .forEach(([day, proofCall]) => {
      if (step >= proofCall) known.add(day);
    });

  const cadence = plan.effectiveCadenceDays ?? row.cadenceDays;
  const cadenceReadyAt = plan.cadenceReadyAtCall;
  const cadenceReady = cadence && (
    plan.mode === 'trusted'
    || (cadenceReadyAt != null && step >= cadenceReadyAt));
  if (cadenceReady) {
    const positions = new Map(pricingDates.map((day, index) => [day, index]));
    const calledForUnit = pricingDates.filter(day => callSet.has(day));
    for (let index = 0; index + 1 < calledForUnit.length; index += 1) {
      const leftDay = calledForUnit[index];
      const rightDay = calledForUnit[index + 1];
      const left = positions.get(leftDay);
      const right = positions.get(rightDay);
      if (right - left > cadence) continue;
      if (dpVisualizerSignatureId(unit, leftDay) !== dpVisualizerSignatureId(unit, rightDay)) continue;
      for (let position = left; position <= right; position += 1) {
        known.add(pricingDates[position]);
      }
    }
  }

  const phaseAt = plan.unitPhaseKnownAtCall?.[unitIndex];
  const phaseKnown = phaseAt != null && step >= phaseAt;
  if (phaseKnown) {
    const boundaries = new Set(plan.unitCycleBoundaryDates?.[unitIndex] || []);
    const groups = [];
    let group = [];
    pricingDates.forEach(day => {
      if (group.length && boundaries.has(day)) {
        groups.push(group);
        group = [];
      }
      group.push(day);
    });
    if (group.length) groups.push(group);
    groups.forEach(days => {
      if (days.some(day => callSet.has(day))) days.forEach(day => known.add(day));
    });
  }
  return known;
}

function dpVisualizerHtml(row) {
  const bid = String(row.buildingId || '');
  const units = row.units || [];
  const fullscreen = dynamicPricing.visualFullscreen.has(bid);
  const colorMode = !dynamicPricing.visualColorOff.has(bid);
  const mode = dpVisualizerMode(row, bid);
  dynamicPricing.visualModes[bid] = mode;
  const plan = dpVisualizerPlan(row, bid);
  const calls = plan.bootstrapApiCallDates || [];
  const requestedStep = Number(dynamicPricing.visualSteps[bid] || 0);
  const step = Math.max(0, Math.min(requestedStep, calls.length));
  dynamicPricing.visualSteps[bid] = step;
  const currentCall = step ? calls[step - 1] : null;
  const allDates = units.flatMap(dpUnitPricingDates).sort();
  if (!allDates.length) return '<div class="si-pending">No dated pricing to visualize.</div>';
  const calendar = dpCalendarDates(allDates[0], allDates[allDates.length - 1]);
  const gridHeightBudget = fullscreen
    ? Math.max(240, window.innerHeight - 190)
    : Math.max(180, Math.min(window.innerHeight * 0.58, 640));
  const rowHeight = Math.max(6, Math.min(25,
    Math.floor((gridHeightBudget - 46) / Math.max(units.length, 1))));
  const denseClass = rowHeight < 18 ? ' dp-viz-dense' : '';
  const unitColumnWidth = fullscreen ? 210 : (calendar.length > 120 ? 150 : 190);
  const dateFontSize = calendar.length > 140 ? 6 : (calendar.length > 100 ? 7 : 8);
  const called = new Set(calls.slice(0, step));
  const currentStep = step ? (plan.algorithmCallSteps || [])[step - 1] : null;
  const knownPhaseUnits = units.filter((_unit, index) => {
    const phaseAt = plan.unitPhaseKnownAtCall?.[index];
    return phaseAt != null && step >= phaseAt;
  }).length;
  const boundaryNotRequired = new Set(plan.unitBoundaryNotRequired || []);
  const boundaryNotRequiredCount = units.filter(
    (_unit, index) => boundaryNotRequired.has(index)).length;
  const fullyRetrievedUnits = units.filter(unit =>
    dpUnitPricingDates(unit).every(day => called.has(day))).length;
  let cadenceStatus;
  const effectiveCadence = plan.effectiveCadenceDays ?? row.cadenceDays;
  const responseCadenceLowerBound = units.reduce((largest, unit, index) => {
    const proofCall = plan.unitEndpointEqualityAtCall?.[index];
    return proofCall != null && step >= proofCall
      ? Math.max(largest, dpUnitPricingDates(unit).length)
      : largest;
  }, 0);
  if (mode === 'trusted') {
    cadenceStatus = row.cadenceIsLowerBound
      ? `Supplied lower bound ≥ ${row.cadenceDays} days · trusted without verification`
      : `Known and trusted before call 1 · ${effectiveCadence || '—'} days`;
  } else if (mode === 'unknown') {
    const activeInvalidation = (plan.cadenceInvalidations || [])
      .filter(item => step >= Number(item.atCall || 0))
      .at(-1);
    const activeRejection = (plan.cadenceCandidateRejections || [])
      .filter(item => step >= Number(item.atCall || 0))
      .at(-1);
    cadenceStatus = activeInvalidation
      && (plan.cadenceKnownAtCall == null || step < plan.cadenceKnownAtCall)
      ? `Invalidated ${activeInvalidation.cadenceDays}-day cadence at call ${activeInvalidation.atCall} · discovery resumed`
      : activeRejection
        && (plan.cadenceKnownAtCall == null || step < plan.cadenceKnownAtCall)
      ? `Rejected ${activeRejection.cadenceDays}-day candidate at call ${activeRejection.atCall} from existing property responses · discovery continued`
      : plan.cadenceKnownAtCall != null && step >= plan.cadenceKnownAtCall
      ? (plan.cadenceStatus || `Discovered at call ${plan.cadenceKnownAtCall} · ${effectiveCadence} days`)
      : (step === calls.length
          ? (plan.cadenceIsLowerBound
              ? plan.cadenceStatus
              : `Not discoverable · full retrieval establishes only ≥ ${row.cadenceDays || '—'} days`)
          : (responseCadenceLowerBound
              ? `Exact cadence unknown · established lower bound ≥ ${responseCadenceLowerBound} days`
              : 'Unknown · testing future-unit endpoints'));
  } else {
    const suppliedLabel = row.cadenceIsLowerBound
      ? `supplied lower bound ≥ ${row.cadenceDays}`
      : `supplied cadence ${row.cadenceDays}`;
    cadenceStatus = plan.cadenceVerifiedAtCall != null && step >= plan.cadenceVerifiedAtCall
      ? `Verified at call ${plan.cadenceVerifiedAtCall} · ${effectiveCadence} days`
      : (step === calls.length
          ? `${suppliedLabel} days could not be verified · full retrieval used`
          : `${suppliedLabel} days · verification in progress`);
  }
  let knownCellCount = 0;
  let totalCellCount = 0;

  const headerCells = calendar.map(day => {
    const currentClass = day === currentCall ? ' current-call' : '';
    const calledClass = called.has(day) ? ' called-date' : '';
    return `<th class="dp-viz-date${currentClass}${calledClass}" title="${esc(day)}"><span>${esc(dpFormatShortDate(day))}</span></th>`;
  }).join('');

  const unitRows = units.map((unit, unitIndex) => {
    const pricingDates = dpUnitPricingDates(unit);
    const active = new Set(pricingDates);
    const known = dpVisualizerKnownDates(unit, row, step, plan, unitIndex);
    // Anchor every unit's first and last price signatures to fixed gradient
    // endpoints. Intermediate signatures keep the same proportional position
    // at every algorithm step; unknown cells remain uncolored.
    const signatureOrder = [];
    const signatureIndexes = new Map();
    pricingDates.forEach(day => {
      const signatureId = dpVisualizerSignatureId(unit, day);
      if (signatureId == null || signatureIndexes.has(signatureId)) return;
      signatureIndexes.set(signatureId, signatureOrder.length);
      signatureOrder.push(signatureId);
    });
    const boundaries = new Set(plan.unitCycleBoundaryDates?.[unitIndex] || []);
    const phaseAt = plan.unitPhaseKnownAtCall?.[unitIndex];
    const phaseKnown = phaseAt != null && step >= phaseAt;
    const endpointEqualityAt = plan.unitEndpointEqualityAtCall?.[unitIndex];
    const endpointEqualityKnown = endpointEqualityAt != null && step >= endpointEqualityAt;
    const lowerBoundInference = plan.unitLowerBoundInferenceAtCall?.[unitIndex] || {};
    const lowerBoundInferenceKnown = Object.values(lowerBoundInference)
      .some(proofCall => step >= proofCall);
    const unitBoundaryNotRequired = boundaryNotRequired.has(unitIndex);
    const availabilityAlignment = plan.unitFutureAvailabilityAlignment?.[unitIndex];
    const activeCalls = pricingDates.filter(day => called.has(day));
    const positions = new Map(pricingDates.map((day, index) => [day, index]));
    const observedBoundaryStarts = new Set();
    for (let index = 0; index + 1 < pricingDates.length; index += 1) {
      const previous = pricingDates[index];
      const current = pricingDates[index + 1];
      if (called.has(previous) && called.has(current)
          && dpVisualizerSignatureId(unit, previous) !== dpVisualizerSignatureId(unit, current)) {
        observedBoundaryStarts.add(current);
      }
    }
    const boundaryWindows = new Set();
    for (let index = 0; index + 1 < activeCalls.length; index += 1) {
      const lower = activeCalls[index];
      const upper = activeCalls[index + 1];
      if (dpVisualizerSignatureId(unit, lower) === dpVisualizerSignatureId(unit, upper)) continue;
      const lowerIndex = positions.get(lower);
      const upperIndex = positions.get(upper);
      if (upperIndex - lowerIndex <= 1) continue;
      for (let position = lowerIndex + 1; position <= upperIndex; position += 1) {
        boundaryWindows.add(pricingDates[position]);
      }
    }
    totalCellCount += active.size;
    knownCellCount += known.size;
    let phaseText;
    if (endpointEqualityKnown) phaseText = 'full window inferred · first and last prices match';
    else if (lowerBoundInferenceKnown) phaseText = 'range inferred from observed cadence lower bound';
    else if (unitBoundaryNotRequired) phaseText = 'no boundary needed · cadence exceeds hold';
    else if (phaseAt === 0) phaseText = 'cycle known initially';
    else if (phaseAt != null && phaseKnown) phaseText = `cycle known at call ${phaseAt}`;
    else if (phaseAt != null) phaseText = `cycle pending · call ${phaseAt}`;
    else if (pricingDates.every(day => called.has(day))) phaseText = 'full window retrieved · no boundary observed';
    else phaseText = 'cycle not yet observable';
    const cells = calendar.map(day => {
      if (!active.has(day)) {
        return `<td class="dp-viz-cell outside${day === currentCall ? ' current-call' : ''}"></td>`;
      }
      const direct = called.has(day);
      const inferred = !direct && known.has(day);
      const boundary = phaseKnown && boundaries.has(day);
      const signatureId = known.has(day) ? dpVisualizerSignatureId(unit, day) : null;
      const signatureIndex = signatureId == null
        ? null : signatureIndexes.get(signatureId);
      const signaturePosition = signatureOrder.length > 1
        ? signatureIndex / (signatureOrder.length - 1) : 0;
      const signatureHue = Math.round(
        DP_PRICE_GRADIENT_START_HUE
        + (DP_PRICE_GRADIENT_END_HUE - DP_PRICE_GRADIENT_START_HUE)
          * signaturePosition);
      const signatureClass = signatureId == null || !colorMode
        ? '' : 'price-signature';
      const signatureStyle = signatureId == null || !colorMode
        ? '' : ` style="--dp-price-hue:${signatureHue}"`;
      const observedPriceChange = observedBoundaryStarts.has(day);
      const boundaryWindow = !phaseKnown && boundaryWindows.has(day);
      const classes = [
        'dp-viz-cell',
        direct ? 'direct' : (inferred ? 'inferred' : 'unknown'),
        signatureClass,
        observedPriceChange ? 'observed-change' : '',
        boundaryWindow ? 'boundary-window' : '',
        boundary ? 'cycle-start' : '',
        day === currentCall ? 'current-call' : '',
      ].filter(Boolean).join(' ');
      const state = direct ? 'direct API response' : (inferred ? 'inferred pricing' : 'unknown pricing');
      const signatureText = signatureId == null
        ? '' : ` · price pattern ${signatureIndex + 1} of ${signatureOrder.length}`;
      const boundaryText = boundaryWindow ? ' · a price boundary is known to fall in this interval' : '';
      return `<td class="${classes}"${signatureStyle} title="${esc(`${unit.unitId} · ${day} · ${state}${signatureText}${boundaryText}`)}"></td>`;
    }).join('');
    const alignmentText = availabilityAlignment && step >= availabilityAlignment.atCall
      ? ` · availability alignment ${availabilityAlignment.status.toLowerCase()}`
      : '';
    const unitSummary = `${unit.holdTimeDays || active.size}d hold · available ${dpFormatShortDate(unit.availableDate)} · retrieval starts ${dpFormatShortDate(unit.visualStartDate)} · ${phaseText}${alignmentText}`;
    return `<tr>
      <th class="dp-viz-unit" title="${esc(`${unit.unitId} · ${unitSummary}`)}">
        <strong>${esc(unit.unitId)}</strong>
        <span class="${phaseKnown || endpointEqualityKnown || lowerBoundInferenceKnown ? 'phase-known' : 'phase-pending'}">${esc(unitSummary)}</span>
      </th>${cells}
    </tr>`;
  }).join('');

  const stepLabel = step
    ? `Call ${step} of ${calls.length} · ${dpFormatShortDate(currentCall)}`
    : `Before call 1 · ${calls.length} calls planned`;
  const observedPhaseCount = Math.max(0, knownPhaseUnits - boundaryNotRequiredCount);
  const phaseStatus = `${observedPhaseCount}/${units.length} cycle points known · ${boundaryNotRequiredCount} boundary searches unnecessary · ${fullyRetrievedUnits}/${units.length} windows fully retrieved`;
  const completion = totalCellCount
    ? Math.round(100 * knownCellCount / totalCellCount)
    : 0;

  return `<div class="dp-algorithm-viz${fullscreen ? ' fullscreen' : ''}${colorMode ? ' color-mode' : ''}${denseClass}" data-bid="${esc(bid)}" style="--dp-viz-row-height:${rowHeight}px;--dp-viz-unit-width:${unitColumnWidth}px;--dp-viz-date-font:${dateFontSize}px;--dp-price-start-hue:${DP_PRICE_GRADIENT_START_HUE};--dp-price-end-hue:${DP_PRICE_GRADIENT_END_HUE}">
    <div class="dp-viz-toolbar">
      <label class="dp-viz-mode">Mode
        <select data-dp-viz-mode data-bid="${esc(bid)}" aria-label="Cadence starting state">
          <option value="known"${mode === 'known' ? ' selected' : ''}>Known — verify first</option>
          <option value="trusted"${mode === 'trusted' ? ' selected' : ''}>Known — trust without verification</option>
          <option value="unknown"${mode === 'unknown' ? ' selected' : ''}>Unknown — discover first</option>
        </select>
      </label>
      <button type="button" data-dp-viz-action="reset" data-bid="${esc(bid)}"${step === 0 ? ' disabled' : ''}>Reset</button>
      <button type="button" data-dp-viz-action="prev" data-bid="${esc(bid)}"${step === 0 ? ' disabled' : ''}>Previous</button>
      <input class="dp-viz-slider" type="range" min="0" max="${calls.length}" value="${step}" data-dp-viz-slider data-bid="${esc(bid)}" aria-label="Algorithm step">
      <button type="button" data-dp-viz-action="next" data-bid="${esc(bid)}"${step === calls.length ? ' disabled' : ''}>Next API Call</button>
      <button type="button" data-dp-viz-action="last" data-bid="${esc(bid)}"${step === calls.length ? ' disabled' : ''}>Finish</button>
      <button type="button" data-dp-viz-action="color" data-bid="${esc(bid)}" aria-pressed="${colorMode}">Color Mode: ${colorMode ? 'On' : 'Off'}</button>
      <button type="button" data-dp-viz-action="fullscreen" data-bid="${esc(bid)}" aria-pressed="${fullscreen}">${fullscreen ? 'Exit Full Screen' : 'Full Screen'}</button>
      <strong class="dp-viz-step-label">${esc(stepLabel)}</strong>
      <span class="dp-viz-key-hint">←/→ step calls</span>
    </div>
    <div class="dp-viz-status">
      <span><b>Cadence:</b> ${esc(cadenceStatus)}</span>
      <span><b>Cycle position:</b> ${esc(phaseStatus)}</span>
      <span><b>Known pricing:</b> ${knownCellCount}/${totalCellCount} cells (${completion}%)</span>
      ${currentStep ? `<span><b>Stage:</b> ${esc(currentStep.stage)} · ${esc(currentStep.reason)}</span>` : ''}
    </div>
    <div class="dp-viz-legend" aria-label="Legend">
      <span><i class="direct"></i>${colorMode ? 'API response · price gradient' : 'API response'}</span>
      <span><i class="inferred"></i>${colorMode ? 'Inferred price · muted gradient' : 'Inferred pricing'}</span>
      <span><i class="unknown"></i>Unknown</span>
      <span><i class="observed-change"></i>Observed adjacent price change</span>
      <span><i class="boundary-window"></i>Boundary lies in interval</span>
      <span><i class="boundary"></i>Projected boundary after proof</span>
    </div>
    <div class="dp-viz-grid-wrap">
      <table class="dp-viz-grid">
        <colgroup><col class="dp-viz-unit-col">${calendar.map(() => '<col>').join('')}</colgroup>
        <thead><tr><th class="dp-viz-corner">Unit / availability and hold</th>${headerCells}</tr></thead>
        <tbody>${unitRows}</tbody>
      </table>
    </div>
  </div>`;
}

function dpFindVisualizerRow(bid) {
  return (dynamicPricing.result?.rows || [])
    .find(item => String(item.buildingId || '') === String(bid))
    || dynamicPricing.validationVisualizerRows.get(String(bid));
}

function dpRenderVisualizer(bid) {
  const row = dpFindVisualizerRow(bid);
  const host = document.querySelector(`.dp-algorithm-viz[data-bid="${CSS.escape(String(bid))}"]`);
  if (row && host) host.outerHTML = dpVisualizerHtml(row);
}

function dpSetVisualizerStep(bid, action) {
  const row = dpFindVisualizerRow(bid);
  if (!row) return;
  dynamicPricing.activeVisualizer = String(bid);
  if (action === 'color') {
    if (dynamicPricing.visualColorOff.has(String(bid))) {
      dynamicPricing.visualColorOff.delete(String(bid));
    } else {
      dynamicPricing.visualColorOff.add(String(bid));
    }
    dpRenderVisualizer(bid);
    return;
  }
  if (action === 'fullscreen') {
    if (dynamicPricing.visualFullscreen.has(String(bid))) {
      dynamicPricing.visualFullscreen.delete(String(bid));
    } else {
      dynamicPricing.visualFullscreen.add(String(bid));
    }
    dpRenderVisualizer(bid);
    return;
  }
  const maximum = (dpVisualizerPlan(row, String(bid)).bootstrapApiCallDates || []).length;
  let step = Number(dynamicPricing.visualSteps[bid] || 0);
  if (action === 'reset') step = 0;
  else if (action === 'prev') step -= 1;
  else if (action === 'next') step += 1;
  else if (action === 'last') step = maximum;
  dynamicPricing.visualSteps[bid] = Math.max(0, Math.min(step, maximum));
  dpRenderVisualizer(bid);
}

function dpUnitDetailHtml(row) {
  if (row.error) {
    return `<div class="dp-error">Could not read the sync-matched matrix: ${esc(row.error)}</div>`;
  }
  if (!(row.units || []).length) {
    return '<div class="si-pending">The sync-matched matrix contains no dated unit pricing.</div>';
  }
  return dpVisualizerHtml(row);
}

function dpRenderResult(result, isPartial = false) {
  dynamicPricing.result = result || {};
  const allRows = dynamicPricing.result.rows || [];
  const body = document.getElementById('dp-preview-body');
  const status = document.getElementById('dp-preview-status');
  const analyzed = dynamicPricing.result.analyzed || 0;
  const total = dynamicPricing.result.communities || 0;
  status.textContent = isPartial ? `${analyzed} / ${total} analyzed` : `${total} communities`;

  if (!allRows.length) {
    body.innerHTML = `<div class="pane-msg">${isPartial
      ? 'Matching successful MITS syncs to pricing matrices…'
      : (dynamicPricing.result.excluded
          ? 'All matched communities were excluded because they had no successful MITS sync with a valid multi-day pricing matrix.'
          : 'No active Entrata communities with dynamic pricing were found.')}</div>`;
    return;
  }

  const rows = dpVisibleRows(allRows);
  const totalCurrent = rows.reduce((sum, row) => sum + (row.currentApiCalls || 0), 0);
  const totalKnown = rows.reduce((sum, row) => sum + (row.knownBootstrapApiCalls || 0), 0);
  const totalTrusted = rows.reduce((sum, row) => sum + (row.trustedBootstrapApiCalls || 0), 0);
  const totalUnknown = rows.reduce((sum, row) => sum + (row.unknownBootstrapApiCalls || 0), 0);
  const totalKnownSaved = rows.reduce((sum, row) => sum + (row.knownApiCallsSaved || 0), 0);
  const totalTrustedSaved = rows.reduce((sum, row) => sum + (row.trustedApiCallsSaved || 0), 0);
  const totalUnknownSaved = rows.reduce((sum, row) => sum + (row.unknownApiCallsSaved || 0), 0);
  const totalKnownSavedPct = totalCurrent
    ? (100 * totalKnownSaved / totalCurrent).toFixed(1)
    : '0.0';
  const totalUnknownSavedPct = totalCurrent
    ? (100 * totalUnknownSaved / totalCurrent).toFixed(1)
    : '0.0';
  const totalTrustedSavedPct = totalCurrent
    ? (100 * totalTrustedSaved / totalCurrent).toFixed(1)
    : '0.0';
  const tableRows = rows.map(row => {
    const bid = String(row.buildingId || '');
    const isOpen = dynamicPricing.open.has(bid);
    const callDateCell = (dates, label) => (dates || []).length
      ? `<details class="dp-dates"><summary>${dates.length} ${label} dates</summary>`
        + `<div class="dp-date-list">${dpDatesHtml(dates)}</div></details>`
      : '<span class="si-pending">none</span>';
    return `<tr class="dp-community-row" data-bid="${esc(bid)}">
      <td><button class="dp-expand" data-bid="${esc(bid)}" aria-expanded="${isOpen}">${isOpen ? 'Hide' : 'Visualize'}</button></td>
      <td>${esc(row.orgName || '—')}</td>
      <td>${esc(row.buildingName || '—')}</td>
      <td class="si-mono">${esc(bid)}</td>
      <td>${row.snapshotLink
        ? `<a href="${esc(row.snapshotLink)}" target="_blank" rel="noopener noreferrer">${esc(dpFormatTimestamp(row.latestSync))}</a>`
        : esc(dpFormatTimestamp(row.latestSync))}</td>
      <td>${row.error ? '<span class="dp-error">Error</span>' : dpCadenceHtml(row)}</td>
      <td>${esc(dpCadenceEvidenceText(row))}</td>
      <td>${esc(row.knownCadenceStatus || '—')}</td>
      <td>${esc(row.unknownCadenceStatus || '—')}</td>
      <td>${esc(row.cycleAlignment || 'Unknown')}</td>
      <td class="dp-num">${row.unitCount || 0}</td>
      <td class="dp-num">${row.currentApiCalls || 0}</td>
      <td class="dp-num">${row.knownBootstrapApiCalls ?? row.bootstrapApiCalls ?? 0}</td>
      <td class="dp-num">${row.trustedBootstrapApiCalls ?? row.bootstrapApiCalls ?? 0}</td>
      <td class="dp-num">${row.unknownBootstrapApiCalls ?? row.bootstrapApiCalls ?? 0}</td>
      <td class="dp-num dp-saved">${row.knownApiCallsSaved ?? row.apiCallsSaved ?? 0}</td>
      <td class="dp-num dp-saved">${row.trustedApiCallsSaved ?? row.apiCallsSaved ?? 0}</td>
      <td class="dp-num dp-saved">${row.unknownApiCallsSaved ?? row.apiCallsSaved ?? 0}</td>
      <td class="dp-num dp-saved">${row.knownApiCallsSavedPct != null ? `${row.knownApiCallsSavedPct}%` : '—'}</td>
      <td class="dp-num dp-saved">${row.trustedApiCallsSavedPct != null ? `${row.trustedApiCallsSavedPct}%` : '—'}</td>
      <td class="dp-num dp-saved">${row.unknownApiCallsSavedPct != null ? `${row.unknownApiCallsSavedPct}%` : '—'}</td>
      <td class="dp-num">${row.knownReconstructionAccuracyPct ?? row.reconstructionAccuracyPct ?? '—'}</td>
      <td class="dp-num">${row.trustedReconstructionAccuracyPct ?? row.reconstructionAccuracyPct ?? '—'}</td>
      <td class="dp-num">${row.unknownReconstructionAccuracyPct ?? row.reconstructionAccuracyPct ?? '—'}</td>
      <td>${callDateCell(row.knownBootstrapApiCallDates || row.bootstrapApiCallDates, 'known-mode')}</td>
      <td>${callDateCell(row.trustedBootstrapApiCallDates || row.bootstrapApiCallDates, 'trusted-mode')}</td>
      <td>${callDateCell(row.unknownBootstrapApiCallDates || row.bootstrapApiCallDates, 'unknown-mode')}</td>
    </tr>
    <tr class="dp-detail-row" data-bid="${esc(bid)}"${isOpen ? '' : ' hidden'}>
      <td colspan="${DP_REPORT_COLUMNS.length + 1}"><div class="dp-unit-detail">${isOpen ? dpUnitDetailHtml(row) : ''}</div></td>
    </tr>`;
  }).join('') || `<tr><td class="dp-no-results" colspan="${DP_REPORT_COLUMNS.length + 1}">No communities match the column filters.</td></tr>`;

  const activeFilters = Object.values(dynamicPricing.filters).some(value => String(value || '').trim());
  const loadedLabel = rows.length === allRows.length
    ? `${rows.length} loaded`
    : `${rows.length} of ${allRows.length} shown`;

  body.innerHTML = `<div class="dp-summary">
      <span>${loadedLabel}</span>
      <span>${totalCurrent} current API calls</span>
      <span>Known: ${totalKnown} calls · ${totalKnownSaved} saved (${totalKnownSavedPct}%)</span>
      <span>Trusted: ${totalTrusted} calls · ${totalTrustedSaved} saved (${totalTrustedSavedPct}%)</span>
      <span>Unknown: ${totalUnknown} calls · ${totalUnknownSaved} saved (${totalUnknownSavedPct}%)</span>
      ${dynamicPricing.result.excluded ? `<span>${dynamicPricing.result.excluded} invalid or single-day communities excluded</span>` : ''}
      ${dynamicPricing.result.errors ? `<span style="color:#f85149">${dynamicPricing.result.errors} errors</span>` : ''}
      ${dynamicPricing.result.unitNumberError ? '<span style="color:#d29922">Unit numbers unavailable; showing matrix IDs</span>' : ''}
      <div class="dp-summary-actions">
        <button type="button" data-dp-clear-filters${activeFilters ? '' : ' disabled'}>Clear Filters</button>
        <button type="button" class="dp-export" data-dp-export${rows.length ? '' : ' disabled'}>Export CSV</button>
      </div>
    </div>
    <div class="dp-algorithm-actions" aria-label="Algorithm references">
      <span>Algorithm reference:</span>
      <button type="button" data-dp-algorithm="known">Known mode pseudocode</button>
      <button type="button" data-dp-algorithm="unknown">Unknown mode pseudocode</button>
    </div>
    <div class="dp-table-wrap"><table class="dp-table">
      <thead>
        <tr><th></th>${dpReportHeaderHtml()}</tr>
        <tr class="dp-filter-row"><th></th>${dpReportFiltersHtml()}</tr>
      </thead>
      <tbody>${tableRows}</tbody>
    </table></div>`;
}

function dpAggregateValidationOrgs(rows) {
  const organizations = new Map();
  (rows || []).forEach(row => {
    const key = row.orgId == null
      ? `name:${row.orgName || 'Unknown'}` : `id:${row.orgId}`;
    if (!organizations.has(key)) {
      organizations.set(key, {
        orgId: row.orgId,
        orgName: row.orgName || 'Unknown',
        communityCount: 0,
        currentApiCalls: 0,
        unknownBootstrapApiCalls: 0,
        unknownApiCallsSaved: 0,
        matricesPassed: 0,
        matricesFailed: 0,
        matrixCells: 0,
        incorrectCellCount: 0,
        accuracySum: 0,
        accuracyCount: 0,
        exactCellAccuracy: true,
      });
    }
    const org = organizations.get(key);
    org.communityCount += 1;
    org.currentApiCalls += Number(row.currentApiCalls || 0);
    org.unknownBootstrapApiCalls += Number(row.unknownBootstrapApiCalls || 0);
    org.unknownApiCallsSaved += Number(row.unknownApiCallsSaved || 0);
    const accuracy = Number(row.unknownReconstructionAccuracyPct);
    if (Number.isFinite(accuracy)) {
      org.accuracySum += accuracy;
      org.accuracyCount += 1;
      if (accuracy === 100) org.matricesPassed += 1;
      else org.matricesFailed += 1;
    }
    const matrixCells = Number(row.matrixCells);
    const incorrectCells = Number(row.incorrectCellCount);
    if (Number.isFinite(matrixCells) && Number.isFinite(incorrectCells)) {
      org.matrixCells += matrixCells;
      org.incorrectCellCount += incorrectCells;
    } else {
      org.exactCellAccuracy = false;
    }
  });
  return [...organizations.values()].map(org => ({
    ...org,
    unknownApiCallsSavedPct: org.currentApiCalls
      ? 100 * org.unknownApiCallsSaved / org.currentApiCalls : 0,
    unknownReconstructionAccuracyPct:
      org.exactCellAccuracy && org.matrixCells
        ? 100 * (org.matrixCells - org.incorrectCellCount) / org.matrixCells
        : (org.accuracyCount ? org.accuracySum / org.accuracyCount : null),
  }));
}

function dpRenderValidationResult(result, isPartial = false) {
  dynamicPricing.validationResult = result || {};
  const body = document.getElementById('dp-preview-body');
  const status = result.validationStatus || (isPartial ? 'running' : 'unknown');
  const statusLabel = status.replace('-', ' ');
  const communityRows = result.rows || [];
  const organizationView = dynamicPricing.validationView === 'organization';
  const rows = dpValidationSortedRows(
    organizationView ? dpAggregateValidationOrgs(communityRows) : communityRows);
  const totalCurrentCalls = communityRows.reduce(
    (sum, row) => sum + Number(row.currentApiCalls || 0), 0);
  const totalUnknownCalls = communityRows.reduce(
    (sum, row) => sum + Number(row.unknownBootstrapApiCalls || 0), 0);
  // Run-wide savings must be calculated from the summed call counts, rather
  // than by averaging (or otherwise combining) community percentages.
  const totalCallsSaved = totalCurrentCalls - totalUnknownCalls;
  const totalSavedPct = totalCurrentCalls
    ? 100 * totalCallsSaved / totalCurrentCalls : 0;
  const fallbackAccuracies = communityRows
    .map(row => Number(row.unknownReconstructionAccuracyPct))
    .filter(Number.isFinite);
  const totalAccuracy = result.overallReconstructionAccuracyPct != null
    ? Number(result.overallReconstructionAccuracyPct)
    : (fallbackAccuracies.length
        ? fallbackAccuracies.reduce((sum, value) => sum + value, 0)
          / fallbackAccuracies.length
        : null);
  const matricesPassed = result.matricesPassed != null
    ? Number(result.matricesPassed)
    : communityRows.filter(
        row => Number(row.unknownReconstructionAccuracyPct) === 100).length;
  const matricesFailed = result.matricesFailed != null
    ? Number(result.matricesFailed)
    : Math.max(0, communityRows.length - matricesPassed);
  const statusClass = status === 'failed'
    ? 'fail' : (status === 'passed' ? 'pass' : 'neutral');
  const tableRows = organizationView ? rows.map(row => {
    const accuracy = row.unknownReconstructionAccuracyPct;
    const accuracyLabel = accuracy == null
      ? '—'
      : `${Number(accuracy).toFixed(6)}%${row.exactCellAccuracy ? '' : ' avg'}`;
    return `<tr class="dp-community-row">
      <td>${esc(row.orgName || '—')}</td>
      <td class="si-mono">${esc(row.orgId ?? '—')}</td>
      <td class="dp-num">${Number(row.communityCount || 0).toLocaleString()}</td>
      <td class="dp-num">${Number(row.currentApiCalls || 0).toLocaleString()}</td>
      <td class="dp-num">${Number(row.unknownBootstrapApiCalls || 0).toLocaleString()}</td>
      <td class="dp-num dp-saved">${Number(row.unknownApiCallsSaved || 0).toLocaleString()}</td>
      <td class="dp-num dp-saved">${Number(row.unknownApiCallsSavedPct || 0).toFixed(1)}%</td>
      <td class="dp-num dp-validation-${row.matricesFailed ? 'fail' : 'pass'}">${accuracyLabel}</td>
      <td class="dp-num">${Number(row.matricesPassed || 0).toLocaleString()}</td>
      <td class="dp-num">${Number(row.matricesFailed || 0).toLocaleString()}</td>
    </tr>`;
  }).join('') : rows.map(row => {
    const bid = String(row.buildingId || '');
    const isOpen = dynamicPricing.validationOpen.has(bid);
    const loadedRow = dynamicPricing.validationVisualizerRows.get(bid);
    const accuracy = row.unknownReconstructionAccuracyPct;
    const passed = accuracy === 100;
    return `<tr class="dp-community-row" data-bid="${esc(bid)}">
      <td><button type="button" class="dp-expand" data-dp-validation-viz="${esc(bid)}"
        aria-expanded="${isOpen}"${isPartial || !dynamicPricing.validationResultId ? ' disabled' : ''}>${isOpen ? 'Hide' : 'Visualize steps'}</button></td>
      <td>${esc(row.orgName || '—')}</td>
      <td>${esc(row.buildingName || '—')}</td>
      <td class="si-mono">${esc(row.buildingId || '—')}</td>
      <td>${row.snapshotLink
        ? `<a href="${esc(row.snapshotLink)}" target="_blank" rel="noopener noreferrer">${esc(dpFormatTimestamp(row.latestSync))}</a>`
        : esc(dpFormatTimestamp(row.latestSync))}</td>
      <td>${esc(row.cadence || row.cadenceDays || '—')}</td>
      <td class="dp-num">${row.unitCount || 0}</td>
      <td class="dp-num">${row.currentApiCalls || 0}</td>
      <td class="dp-num">${row.unknownBootstrapApiCalls || 0}</td>
      <td class="dp-num dp-saved">${row.unknownApiCallsSaved || 0}</td>
      <td class="dp-num dp-saved">${row.unknownApiCallsSavedPct == null ? '—' : `${row.unknownApiCallsSavedPct}%`}</td>
      <td class="dp-num dp-validation-${passed ? 'pass' : 'fail'}">${accuracy == null ? '—' : `${accuracy}%`}</td>
      <td>${esc(row.unknownCadenceStatus || '—')}</td>
    </tr>
    <tr class="dp-detail-row dp-validation-detail-row" data-bid="${esc(bid)}"${isOpen ? '' : ' hidden'}>
      <td colspan="13"><div class="dp-unit-detail">${isOpen
        ? (loadedRow ? dpVisualizerHtml(loadedRow) : '<div class="si-pending">Loading saved matrix and algorithm steps…</div>')
        : ''}</div></td>
    </tr>`;
  }).join('');

  document.getElementById('dp-preview-title').textContent = 'Unknown Mode Validation';
  document.getElementById('dp-preview-status').textContent = isPartial
    ? `${result.communitiesCompleted || 0}/${result.communitiesConsidered || 0} checked`
    : `${Number(result.matricesTested || 0).toLocaleString()} matrices tested`;
  body.innerHTML = `<div class="dp-validation-summary">
      <span class="dp-validation-rollup"><strong>All ${communityRows.length.toLocaleString()} buildings:</strong> ${totalCallsSaved.toLocaleString()} total API calls saved · ${totalSavedPct.toFixed(1)}% total saved${totalAccuracy == null ? '' : ` · ${totalAccuracy.toFixed(6)}% total accuracy`}</span>
      <span class="dp-validation-status ${statusClass}">${esc(statusLabel)}</span>
      <span>${Number(result.matricesTested || 0).toLocaleString()} matrices tested</span>
      <span>${matricesPassed.toLocaleString()} passed · ${matricesFailed.toLocaleString()} failed</span>
      <span>${totalCurrentCalls.toLocaleString()} current API calls</span>
      <span>${totalUnknownCalls.toLocaleString()} Unknown-mode API calls</span>
      <span>${Number(result.communitiesCompleted || 0).toLocaleString()} of ${Number(result.communitiesConsidered || 0).toLocaleString()} communities checked</span>
      <span>${Number(result.cadenceOneTested || 0).toLocaleString()} cadence = 1 tested</span>
      <span>${Number(result.missingAvailabilitySkipped || 0).toLocaleString()} missing or inconsistent availability inputs</span>
      <span>${Number(result.excluded || 0).toLocaleString()} unavailable matrices excluded</span>
      <span>${Number((result.cadenceCorrections || []).length).toLocaleString()} cadence candidates corrected from normal responses</span>
      <span>${isPartial ? 'Result will be saved when validation completes' : 'Saved to validation history'}</span>
      ${result.errors ? `<span class="dp-validation-fail">${Number(result.errors).toLocaleString()} errors</span>` : ''}
      ${result.durationSeconds != null ? `<span>${esc(result.durationSeconds)} seconds</span>` : ''}
    </div>
    <div class="si-toggle-bar">
      <span class="si-toggle-label">View totals by</span>
      <div class="si-seg">
        <button class="si-seg-btn${organizationView ? '' : ' active'}" data-dp-validation-view="community">Community</button>
        <button class="si-seg-btn${organizationView ? ' active' : ''}" data-dp-validation-view="organization">Organization</button>
      </div>
    </div>
    <p class="dp-validation-confidence">${esc(result.confidence || '')}</p>
    ${organizationView && rows.some(row => !row.exactCellAccuracy)
      ? '<p class="dp-validation-warning">This saved run predates per-community cell totals, so organization accuracy is the average community accuracy. New validation runs use exact cell-weighted accuracy.</p>'
      : ''}
    ${result.populationTruncated ? '<p class="dp-validation-warning">The configured limit was reached, so this result covers a sample rather than the full selected population.</p>' : ''}
    <div class="dp-table-wrap"><table class="dp-table dp-validation-table">
      <thead><tr>${organizationView ? '' : '<th></th>'}${dpValidationHeaderHtml()}</tr></thead>
      <tbody>${tableRows || `<tr><td colspan="${dpValidationActiveColumns().length + (organizationView ? 0 : 1)}" class="dp-no-results">${isPartial ? 'Waiting for the first matrix with an available cadence…' : 'No matrices with an available cadence were available in this run.'}</td></tr>`}</tbody>
    </table></div>`;
}

async function dpToggleValidationVisualizer(bid) {
  bid = String(bid || '');
  if (!bid || !dynamicPricing.validationResultId) return;
  const button = document.querySelector(
    `[data-dp-validation-viz="${CSS.escape(bid)}"]`);
  const detail = document.querySelector(
    `.dp-validation-detail-row[data-bid="${CSS.escape(bid)}"]`);
  if (!button || !detail) return;

  if (dynamicPricing.validationOpen.has(bid)) {
    dynamicPricing.validationOpen.delete(bid);
    dynamicPricing.visualFullscreen.delete(bid);
    detail.hidden = true;
    detail.querySelector('.dp-unit-detail').innerHTML = '';
    button.textContent = 'Visualize steps';
    button.setAttribute('aria-expanded', 'false');
    if (dynamicPricing.activeVisualizer === bid) {
      dynamicPricing.activeVisualizer = [...dynamicPricing.validationOpen][0]
        || [...dynamicPricing.open][0] || null;
    }
    return;
  }

  dynamicPricing.validationOpen.add(bid);
  dynamicPricing.activeVisualizer = bid;
  dynamicPricing.visualModes[bid] = 'unknown';
  dynamicPricing.visualSteps[bid] ||= 0;
  detail.hidden = false;
  button.textContent = 'Hide';
  button.setAttribute('aria-expanded', 'true');
  const host = detail.querySelector('.dp-unit-detail');
  const cached = dynamicPricing.validationVisualizerRows.get(bid);
  if (cached) {
    host.innerHTML = dpVisualizerHtml(cached);
    return;
  }

  button.disabled = true;
  host.innerHTML = '<div class="si-pending">Loading the saved sync-matched matrix and rebuilding its algorithm steps…</div>';
  try {
    const response = await fetch(
      `/api/dynamic-pricing/validation/${encodeURIComponent(dynamicPricing.validationResultId)}/community/${encodeURIComponent(bid)}`);
    const row = await response.json();
    if (!response.ok || row.error) {
      throw new Error(row.error || response.statusText);
    }
    dynamicPricing.validationVisualizerRows.set(bid, row);
    host.innerHTML = dpVisualizerHtml(row);
  } catch (error) {
    dynamicPricing.validationOpen.delete(bid);
    dynamicPricing.activeVisualizer = null;
    button.textContent = 'Visualize steps';
    button.setAttribute('aria-expanded', 'false');
    host.innerHTML = `<div class="dp-error">Could not load algorithm steps: ${esc(error.message)}</div>`;
  } finally {
    button.disabled = false;
  }
}

function dpToggleCommunity(bid) {
  if (dynamicPricing.open.has(bid)) {
    dynamicPricing.open.delete(bid);
    dynamicPricing.visualFullscreen.delete(bid);
    if (dynamicPricing.activeVisualizer === bid) {
      dynamicPricing.activeVisualizer = [...dynamicPricing.open][0] || null;
    }
  } else {
    dynamicPricing.open.add(bid);
    dynamicPricing.activeVisualizer = bid;
    dynamicPricing.visualModes[bid] ||= 'known';
    dynamicPricing.visualSteps[bid] ||= 0;
  }
  dpRenderResult(dynamicPricing.result, !!dynamicPricing.result?.partial);
}

async function runDynamicPricing() {
  const scopeValues = dpReadRunScope();
  if (!scopeValues) return;
  const {limit, orgIds, communityIds} = scopeValues;
  if (dynamicPricing.validationPolling) clearInterval(dynamicPricing.validationPolling);
  dynamicPricing.validationJobId = null;
  dynamicPricing.validationPolling = null;
  dpResetReportState();

  dpSetRunButtons(true);
  const scope = dpScopeLabel(orgIds, communityIds);
  dpSetStatus(scope
    ? `Finding Entrata communities for ${scope}…`
    : 'Finding Entrata communities in Snowflake…');
  document.getElementById('dp-preview-status').textContent = 'Starting…';
  document.getElementById('dp-preview-body').innerHTML =
    '<div class="pane-msg">Matching successful MITS syncs to pricing matrices…</div>';
  try {
    const response = await fetch('/api/dynamic-pricing/analyze', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({limit, orgIds, communityIds}),
    });
    const data = await response.json();
    if (!response.ok || data.error) throw new Error(data.error || response.statusText);
    dynamicPricing.jobId = data.jobId;
    dynamicPricing.polling = setInterval(pollDynamicPricing, 1500);
    await pollDynamicPricing();
  } catch (error) {
    dpSetRunButtons(false);
    dpSetStatus(`Analysis failed: ${error.message}`, true);
    document.getElementById('dp-preview-status').textContent = 'Error';
    document.getElementById('dp-preview-body').innerHTML =
      `<div class="pane-msg" style="color:#f85149">${esc(error.message)}</div>`;
  }
}

function dpReadRunScope() {
  const input = document.getElementById('dp-limit');
  const limit = Number.parseInt(input.value, 10);
  if (!Number.isInteger(limit) || limit < 1 || limit > 5000) {
    dpSetStatus('Maximum communities must be between 1 and 5,000.', true);
    return null;
  }
  const orgText = document.getElementById('dp-org-ids').value.trim();
  const orgTokens = orgText ? orgText.split(/[\s,]+/).filter(Boolean) : [];
  const invalidOrgId = orgTokens.find(value => !/^\d+$/.test(value) || Number(value) <= 0);
  if (invalidOrgId) {
    dpSetStatus(`Organization IDs must be positive integers; check “${invalidOrgId}”.`, true);
    return null;
  }
  const orgIds = [...new Set(orgTokens)];
  if (orgIds.length > 5000) {
    dpSetStatus('Enter at most 5,000 organization IDs.', true);
    return null;
  }
  const communityText = document.getElementById('dp-community-ids').value.trim();
  const communityTokens = communityText
    ? communityText.split(/[\s,]+/).filter(Boolean)
    : [];
  const invalidCommunityId = communityTokens.find(value =>
    !/^\d+$/.test(value) || Number(value) <= 0);
  if (invalidCommunityId) {
    dpSetStatus(`Community IDs must be positive integers; check “${invalidCommunityId}”.`, true);
    return null;
  }
  const communityIds = [...new Set(communityTokens)];
  if (communityIds.length > 5000) {
    dpSetStatus('Enter at most 5,000 community IDs.', true);
    return null;
  }
  return {limit, orgIds, communityIds};
}

function dpResetReportState() {
  if (dynamicPricing.polling) clearInterval(dynamicPricing.polling);
  dynamicPricing.jobId = null;
  dynamicPricing.polling = null;
  dynamicPricing.result = null;
  dynamicPricing.validationResultId = null;
  dynamicPricing.validationResult = null;
  dynamicPricing.validationVisualizerRows.clear();
  dynamicPricing.validationOpen.clear();
  dynamicPricing.open.clear();
  dynamicPricing.visualSteps = {};
  dynamicPricing.visualModes = {};
  dynamicPricing.visualFullscreen.clear();
  dynamicPricing.activeVisualizer = null;
  dynamicPricing.filters = {};
  dynamicPricing.sortKey = 'knownApiCallsSaved';
  dynamicPricing.sortDir = 'desc';
  dynamicPricing.validationSortKey = 'unknownApiCallsSaved';
  dynamicPricing.validationSortDir = 'desc';
  dynamicPricing.validationView = 'community';
}

function dpSetRunButtons(disabled) {
  document.getElementById('btn-run-dynamic-pricing').disabled = disabled;
  document.getElementById('btn-validate-dynamic-pricing').disabled = disabled;
}

function dpScopeLabel(orgIds, communityIds) {
  return [
    communityIds.length
      ? `${communityIds.length} specified communit${communityIds.length === 1 ? 'y' : 'ies'}`
      : '',
    orgIds.length
      ? `${orgIds.length} organization${orgIds.length === 1 ? '' : 's'}`
      : '',
  ].filter(Boolean).join(' plus ');
}

async function pollDynamicPricing() {
  if (!dynamicPricing.jobId) return;
  try {
    const response = await fetch(`/api/job?id=${encodeURIComponent(dynamicPricing.jobId)}`);
    const job = await response.json();
    if (!response.ok || !job.status) throw new Error(job.error || response.statusText);
    if (job.result) dpRenderResult(job.result, job.status === 'running');
    dpSetStatus(job.note || 'Analyzing pricing cadence…');
    if (job.status === 'running') return;

    clearInterval(dynamicPricing.polling);
    dynamicPricing.polling = null;
    dynamicPricing.jobId = null;
    dpSetRunButtons(false);
    if (job.status === 'error') throw new Error(job.error || 'Unknown analysis error');
    const result = job.result || {};
    dpRenderResult(result, false);
    dpSetStatus(`Done — ${result.analyzed || 0} communities analyzed`
      + (result.excluded ? ` · ${result.excluded} excluded` : '')
      + (result.errors ? ` · ${result.errors} errors` : ''));
  } catch (error) {
    if (dynamicPricing.polling) clearInterval(dynamicPricing.polling);
    dynamicPricing.polling = null;
    dynamicPricing.jobId = null;
    dpSetRunButtons(false);
    dpSetStatus(`Analysis failed: ${error.message}`, true);
    document.getElementById('dp-preview-status').textContent = 'Error';
  }
}

async function runDynamicPricingValidation() {
  const scopeValues = dpReadRunScope();
  if (!scopeValues) return;
  const {limit, orgIds, communityIds} = scopeValues;
  if (dynamicPricing.polling) clearInterval(dynamicPricing.polling);
  dynamicPricing.jobId = null;
  if (dynamicPricing.validationPolling) clearInterval(dynamicPricing.validationPolling);
  dynamicPricing.validationJobId = null;
  dpResetReportState();
  dpSetRunButtons(true);

  const scope = dpScopeLabel(orgIds, communityIds);
  dpSetStatus(scope
    ? `Preparing Unknown-mode validation for ${scope}…`
    : 'Preparing broad Unknown-mode validation…');
  document.getElementById('dp-preview-title').textContent = 'Unknown Mode Validation';
  document.getElementById('dp-preview-status').textContent = 'Starting…';
  document.getElementById('dp-preview-body').innerHTML =
    '<div class="pane-msg">Testing latest-sync matrices with cadence greater than one…</div>';
  try {
    const response = await fetch('/api/dynamic-pricing/validate-unknown', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({limit, orgIds, communityIds}),
    });
    const data = await response.json();
    if (!response.ok || data.error) throw new Error(data.error || response.statusText);
    dynamicPricing.validationJobId = data.jobId;
    dynamicPricing.validationResultId = data.jobId;
    dynamicPricing.validationPolling = setInterval(
      pollDynamicPricingValidation, 1500);
    await pollDynamicPricingValidation();
  } catch (error) {
    dpSetRunButtons(false);
    dpSetStatus(`Validation failed: ${error.message}`, true);
    document.getElementById('dp-preview-status').textContent = 'Error';
    document.getElementById('dp-preview-body').innerHTML =
      `<div class="pane-msg" style="color:#f85149">${esc(error.message)}</div>`;
  }
}

async function pollDynamicPricingValidation() {
  if (!dynamicPricing.validationJobId) return;
  try {
    const response = await fetch(`/api/job?id=${encodeURIComponent(dynamicPricing.validationJobId)}`);
    const job = await response.json();
    if (!response.ok || !job.status) throw new Error(job.error || response.statusText);
    if (job.result) dpRenderValidationResult(job.result, job.status === 'running');
    dpSetStatus(job.note || 'Validating Unknown mode…');
    if (job.status === 'running') return;

    clearInterval(dynamicPricing.validationPolling);
    dynamicPricing.validationPolling = null;
    dynamicPricing.validationJobId = null;
    dpSetRunButtons(false);
    if (job.status === 'error') throw new Error(job.error || 'Unknown validation error');
    const result = job.result || {};
    dpRenderValidationResult(result, false);
    dpSetStatus(`Validation ${String(result.validationStatus || 'finished').replace('-', ' ')} — ${Number(result.matricesTested || 0).toLocaleString()} matrices tested`);
    await loadHistory();
    const saved = document.getElementById('saved-dynamic-pricing-validation');
    saved?.classList.add('open');
    saved?.querySelector('.saved-toggle')?.setAttribute('aria-expanded', 'true');
  } catch (error) {
    if (dynamicPricing.validationPolling) clearInterval(dynamicPricing.validationPolling);
    dynamicPricing.validationPolling = null;
    dynamicPricing.validationJobId = null;
    dpSetRunButtons(false);
    dpSetStatus(`Validation failed: ${error.message}`, true);
    document.getElementById('dp-preview-status').textContent = 'Error';
  }
}

async function openDynamicPricingValidationHistory(entry) {
  setMode('dynamic-pricing');
  dynamicPricing.validationResultId = entry.id;
  dynamicPricing.validationResult = null;
  dynamicPricing.validationSortKey = 'unknownApiCallsSaved';
  dynamicPricing.validationSortDir = 'desc';
  dynamicPricing.validationView = 'community';
  dynamicPricing.validationVisualizerRows.clear();
  dynamicPricing.validationOpen.clear();
  dynamicPricing.visualSteps = {};
  dynamicPricing.visualModes = {};
  dynamicPricing.visualFullscreen.clear();
  dynamicPricing.activeVisualizer = null;
  document.getElementById('dp-preview-title').textContent = 'Unknown Mode Validation';
  document.getElementById('dp-preview-status').textContent = 'Loading saved result…';
  document.getElementById('dp-preview-body').innerHTML =
    '<div class="pane-msg">Opening saved validation result…</div>';
  try {
    const url = entry.resultUrl
      || `/api/dynamic-pricing/validation/${encodeURIComponent(entry.id)}`;
    const response = await fetch(url);
    const result = await response.json();
    if (!response.ok || result.error) throw new Error(result.error || response.statusText);
    dpRenderValidationResult(result, false);
    dpSetStatus(`Saved validation from ${entry.createdAt ? new Date(entry.createdAt).toLocaleString() : 'history'}`);
  } catch (error) {
    dpSetStatus(`Could not open saved validation: ${error.message}`, true);
    document.getElementById('dp-preview-status').textContent = 'Error';
    document.getElementById('dp-preview-body').innerHTML =
      `<div class="pane-msg" style="color:#f85149">${esc(error.message)}</div>`;
  }
}

// ── Sync Issues ────────────────────────────────────────────────────────────────

const syncIssues = {
  syncs:     [],         // last query results
  jobId:     null,       // current analyze job id
  polling:   null,       // setInterval handle
  buildings: {},         // BUILDING_ID → per-building analysis detail
  open:      new Set(),  // BUILDING_IDs whose detail row is expanded
  showAll:   false,      // false = only units this sync newly marked
  lastResult: null,      // last job result, for re-rendering on toggle
  queryPct:  0,          // threshold the query ran with (slider floor)
  minPct:    0,          // post-query threshold from the slider
  sortSyncs: {key: 'pct',   dir: 'desc'},
  sortDist:  {key: 'count', dir: 'desc'},
};

// Every reason row carries both an all-units and a newly-marked count; these
// pick the active one so the toggle needs no re-fetch.
function siCount(row) { return syncIssues.showAll ? row.count : row.countNew; }
function siPct(row)   { return syncIssues.showAll ? row.pct   : row.pctNew;   }

// Reasons with no units in the active scope are hidden, and the surviving rows
// re-sort by the active count.
function siActiveReasons(reasons) {
  return (reasons || [])
    .filter(r => siCount(r) > 0)
    .sort((a, b) => siCount(b) - siCount(a) ||
                    a.reason.localeCompare(b.reason));
}

function siActiveUnits(row) {
  const units = row.units || [];
  return syncIssues.showAll ? units : units.filter(u => u.isNew === true);
}

function siScopeLabel() {
  return syncIssues.showAll ? 'unavailable units' : 'newly marked unavailable';
}

function buildScopeToggleHtml() {
  const a = syncIssues.showAll;
  return `<div class="si-toggle-bar">
    <span class="si-toggle-label">Show</span>
    <div class="si-seg">
      <button class="si-seg-btn${a ? '' : ' active'}" data-scope="new">Newly marked only</button>
      <button class="si-seg-btn${a ? ' active' : ''}" data-scope="all">All unavailable</button>
    </div>
    <span class="si-toggle-note">${a
      ? 'Including units that were already unavailable before the sync.'
      : 'Excluding units that were already unavailable before the sync.'}</span>
  </div>`;
}

function siSetScope(showAll) {
  if (syncIssues.showAll === showAll) return;
  syncIssues.showAll = showAll;
  document.querySelectorAll('.si-seg-btn').forEach(b =>
    b.classList.toggle('active', (b.dataset.scope === 'all') === showAll));
  const note = document.querySelector('.si-toggle-note');
  if (note) note.textContent = showAll
    ? 'Including units that were already unavailable before the sync.'
    : 'Excluding units that were already unavailable before the sync.';
  siRepaint();
}

function siSummaryLine(r) {
  const n = syncIssues.showAll ? r.unavailableUnits : r.newlyMarkedUnits;
  const dedup = r.deduplicatedBuildings || r.syncsAnalyzed || 0;
  const orig  = r.originalSyncs || dedup;
  const dupNote = orig > dedup ? ` (${orig} syncs → ${dedup} unique buildings)` : '';
  return `${n || 0} ${siScopeLabel()} · ${r.syncsWithData || 0} buildings analyzed${dupNote}`;
}

// Helpers for the two status surfaces
function siSetSidebarStatus(msg, isError) {
  const el = document.getElementById('si-status');
  el.textContent = msg;
  el.style.color = isError ? '#f85149' : '#8b949e';
}

function siSetPreviewStatus(msg) {
  document.getElementById('si-preview-status').textContent = msg;
}

function siSetPreviewTitle(msg) {
  document.getElementById('si-preview-title').textContent = msg;
}

function siSetPreviewBody(html) {
  document.getElementById('si-preview-body').innerHTML = html;
}

async function runSyncIssuesQuery() {
  const startDate = document.getElementById('si-start-date').value.trim();
  const endDate   = document.getElementById('si-end-date').value.trim();
  if (!startDate || !endDate) {
    siSetSidebarStatus('Please select a start and end date.', true);
    return;
  }
  const integrations = [...document.querySelectorAll('.si-integration-cb:checked')]
    .map(cb => cb.value);
  const thresholdPct = parseFloat(document.getElementById('si-threshold').value);
  if (isNaN(thresholdPct) || thresholdPct <= 0 || thresholdPct > 100) {
    siSetSidebarStatus('Threshold must be between 1 and 100.', true);
    return;
  }
  const threshold = thresholdPct / 100;
  const limit = parseInt(document.getElementById('si-limit').value, 10) || 100;

  // Cancel any in-flight analysis and drop the previous run's per-building data
  if (syncIssues.polling) {
    clearInterval(syncIssues.polling);
    syncIssues.polling = null;
    syncIssues.jobId = null;
  }
  syncIssues.buildings  = {};
  syncIssues.lastResult = null;
  syncIssues.open.clear();
  // The slider can only narrow the query, so it starts at the queried value.
  syncIssues.queryPct   = threshold;
  syncIssues.minPct     = threshold;
  syncIssues.sortSyncs  = {key: 'pct',   dir: 'desc'};
  syncIssues.sortDist   = {key: 'count', dir: 'desc'};

  siSetSidebarStatus('Running Snowflake query…', false);
  siSetPreviewTitle('Sync Issues');
  siSetPreviewStatus('Querying…');
  siSetPreviewBody(`<div class="pane-msg" style="flex-direction:column;gap:6px;">
    <span style="font-size:20px;opacity:.4">⏳</span>
    <span>Running Snowflake query — this may take up to a minute…</span>
  </div>`);

  const btn = document.getElementById('btn-run-sync-query');
  btn.disabled = true;

  try {
    const res = await fetch('/api/sync-issues/query', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ startDate, endDate, integrations, threshold, limit }),
    });
    const data = await res.json();
    if (!res.ok || data.error) throw new Error(data.error || res.statusText);

    syncIssues.syncs = data.syncs || [];
    const n = syncIssues.syncs.length;
    siSetSidebarStatus(`Found ${n} sync${n === 1 ? '' : 's'}.`, false);

    if (!n) {
      siSetPreviewStatus('');
      siSetPreviewBody(`<div class="pane-msg" style="flex-direction:column;gap:6px;">
        <span style="font-size:20px;opacity:.4">✅</span>
        <span>No syncs matched the criteria for this date range.</span>
      </div>`);
      return;
    }

    // Render the syncs table immediately, then auto-start analysis
    siSetPreviewStatus(`${n} sync${n === 1 ? '' : 's'} found — analyzing…`);
    siSetPreviewBody(
      `<div id="si-controls">${buildScopeToggleHtml()}${buildThresholdSliderHtml()}</div>
       <div id="si-syncs-host"></div>` + buildAnalyzeProgressHtml());
    siRenderSyncsTable();
    runSyncIssuesAnalyze();
  } catch (e) {
    siSetSidebarStatus(`Query failed: ${e.message}`, true);
    siSetPreviewStatus('Error');
    siSetPreviewBody(`<div class="pane-msg" style="color:#f85149">${esc(e.message)}</div>`);
  } finally {
    btn.disabled = false;
  }
}

const SI_TABLE_COLS = 9;

// Sortable columns of the Flagged Syncs table.  `get` returns a comparable
// value; `num` marks numeric columns so they compare as numbers, not strings.
const SI_SYNC_COLUMNS = [
  {key: 'org',      label: 'Org',             get: s => s.ORG_NAME || ''},
  {key: 'building', label: 'Building',        get: s => s.BUILDING_NAME || ''},
  {key: 'started',  label: 'Sync Start',      get: s => s.SYNC_STARTED_AT || ''},
  {key: 'sources',  label: 'Sources',         get: s => s.SOURCES || ''},
  {key: 'before',   label: 'Units Before',    get: s => s.TOTAL_UNITS_BEFORE_SYNC, num: true, right: true},
  {key: 'marked',   label: 'Marked Unavail.', get: s => s.UNITS_MARKED_UNAVAILABLE, num: true, right: true},
  {key: 'pct',      label: '% Unavail.',      get: s => s.PCT_UNITS_MARKED_UNAVAILABLE, num: true, right: true},
  {key: 'reason',   label: 'Top Reason',      get: s => {
    const b = syncIssues.buildings[String(s.BUILDING_ID ?? '')];
    if (!b) return '';
    if (b.status === 'skipped') return '\uffff';          // sort skipped last
    return (siActiveReasons(b.reasons)[0] || {}).reason || '';
  }},
];

function siSortIndicator(key) {
  const st = syncIssues.sortSyncs;
  if (st.key !== key) return '';
  return st.dir === 'asc' ? ' <span class="si-sort-arrow">▲</span>'
                          : ' <span class="si-sort-arrow">▼</span>';
}

function siCompare(a, b, col, dir) {
  let va = col.get(a), vb = col.get(b);
  if (col.num) {
    va = va == null ? -Infinity : parseFloat(va);
    vb = vb == null ? -Infinity : parseFloat(vb);
    if (Number.isNaN(va)) va = -Infinity;
    if (Number.isNaN(vb)) vb = -Infinity;
  } else {
    va = String(va ?? '').toLowerCase();
    vb = String(vb ?? '').toLowerCase();
  }
  const c = va < vb ? -1 : va > vb ? 1 : 0;
  return dir === 'asc' ? c : -c;
}

// Syncs at or above the post-query threshold slider.
function siVisibleSyncs() {
  const min = syncIssues.minPct;
  const kept = syncIssues.syncs.filter(s => {
    const detail = syncIssues.buildings[String(s.BUILDING_ID ?? '')];
    // Until analysis resolves the candidate, keep it visible with its loading
    // state. Once we know it has no pre-sync snapshot, it is not a verified
    // sync issue and must disappear from the flagged list entirely.
    if (detail && detail.excludedFromIssues) return false;
    const v = parseFloat(s.PCT_UNITS_MARKED_UNAVAILABLE);
    return Number.isNaN(v) ? true : v >= min - 1e-9;
  });
  const col = SI_SYNC_COLUMNS.find(c => c.key === syncIssues.sortSyncs.key)
            || SI_SYNC_COLUMNS.find(c => c.key === 'pct');
  return kept.sort((a, b) => siCompare(a, b, col, syncIssues.sortSyncs.dir));
}

function buildThresholdSliderHtml() {
  const floorPct = Math.round(syncIssues.queryPct * 100);
  const curPct   = Math.round(syncIssues.minPct * 100);
  return `<div class="si-slider-bar">
    <span class="si-toggle-label">Min % Unavail.</span>
    <input type="range" id="si-pct-slider" min="${floorPct}" max="100" step="1"
           value="${curPct}" aria-label="Minimum percent of units marked unavailable">
    <span id="si-pct-value">${curPct}%</span>
    <span id="si-pct-count" class="si-toggle-note"></span>
  </div>`;
}

function buildSyncsTableHtml(syncs) {
  const rows = syncs.map(s => {
    const bid = String(s.BUILDING_ID ?? '');
    const pct = s.PCT_UNITS_MARKED_UNAVAILABLE != null
      ? (parseFloat(s.PCT_UNITS_MARKED_UNAVAILABLE) * 100).toFixed(1) + '%'
      : '—';
    const buildingCell = s.SNAPSHOT_LINK
      ? `<a href="${esc(s.SNAPSHOT_LINK)}" target="_blank" rel="noopener" style="color:#58a6ff">${esc(s.BUILDING_NAME || '—')}</a>`
      : esc(s.BUILDING_NAME || '—');
    const ts = (s.SYNC_STARTED_AT || '').replace('T', ' ').replace(/\.\d+.*$/, '');
    return `<tr class="si-sync-row" data-bid="${esc(bid)}">
      <td class="si-expand-cell">
        <button class="si-expand-btn" data-bid="${esc(bid)}" aria-expanded="false"
                title="Show unavailability reasons for this building" disabled>▶</button>
      </td>
      <td>${esc(s.ORG_NAME || '—')}</td>
      <td>${buildingCell}</td>
      <td>${esc(ts)}</td>
      <td>${esc(s.SOURCES || '—')}</td>
      <td style="text-align:right">${esc(String(s.TOTAL_UNITS_BEFORE_SYNC ?? '—'))}</td>
      <td style="text-align:right">${esc(String(s.UNITS_MARKED_UNAVAILABLE ?? '—'))}</td>
      <td style="text-align:right;font-weight:600;color:#f85149">${esc(pct)}</td>
      <td class="si-top-reason" data-bid="${esc(bid)}"><span class="si-pending">analyzing…</span></td>
    </tr>
    <tr class="si-detail-row" data-bid="${esc(bid)}" hidden>
      <td colspan="${SI_TABLE_COLS}"><div class="si-detail"></div></td>
    </tr>`;
  }).join('');

  const total = syncIssues.syncs.filter(s => {
    const detail = syncIssues.buildings[String(s.BUILDING_ID ?? '')];
    return !(detail && detail.excludedFromIssues);
  }).length;
  const shownNote = syncs.length === total
    ? `${total}` : `${syncs.length} of ${total}`;
  const heads = SI_SYNC_COLUMNS.map(c =>
    `<th class="si-sortable${c.right ? ' si-th-right' : ''}" data-sortkey="${c.key}"
         title="Sort by ${esc(c.label)}">${esc(c.label)}${siSortIndicator(c.key)}</th>`
  ).join('');

  return `<div class="si-syncs-section">
    <div class="si-syncs-heading">Flagged Syncs (${shownNote})
      <span class="si-syncs-hint">— click ▶ for a building's reasons, or a column header to sort</span>
    </div>
    <div class="si-syncs-wrap">
      <table class="si-table">
        <thead><tr><th style="width:28px"></th>${heads}</tr></thead>
        <tbody>${rows}</tbody>
      </table>
    </div>
  </div>`;
}

// Re-render the syncs table in place, preserving which rows were expanded.
function siRenderSyncsTable() {
  const host = document.getElementById('si-syncs-host');
  if (!host) return;
  const visible = siVisibleSyncs();
  host.innerHTML = buildSyncsTableHtml(visible);
  // Restore expanded rows that survived the filter.
  syncIssues.open.forEach(bid => {
    const row = host.querySelector(`.si-detail-row[data-bid="${CSS.escape(bid)}"]`);
    const btn = host.querySelector(`.si-expand-btn[data-bid="${CSS.escape(bid)}"]`);
    if (row) row.hidden = false;
    if (btn) { btn.textContent = '▼'; btn.setAttribute('aria-expanded', 'true'); }
  });
  siRefreshBuildingRows();
  const countEl = document.getElementById('si-pct-count');
  if (countEl) {
    const total = syncIssues.syncs.filter(s => {
      const detail = syncIssues.buildings[String(s.BUILDING_ID ?? '')];
      return !(detail && detail.excludedFromIssues);
    }).length;
    countEl.textContent = visible.length === total
      ? `all ${total} sync${total === 1 ? '' : 's'}`
      : `${visible.length} of ${total} syncs`;
  }
}

// The combined rollup is recomputed from the per-building data so the slider
// needs no re-query: buildings below the threshold simply drop out.
function siAggregateVisibleResult() {
  const base = syncIssues.lastResult || {};
  const visibleBids = new Set(siVisibleSyncs().map(s => String(s.BUILDING_ID ?? '')));
  const byReason = new Map();
  const byInt = {}, byIntNew = {};
  let all = 0, neu = 0, withData = 0, skipped = 0, baselineMissing = 0, analyzed = 0;

  Object.entries(syncIssues.buildings).forEach(([bid, b]) => {
    if (!visibleBids.has(bid)) return;
    analyzed++;
    if (b.status === 'skipped') { skipped++; return; }
    withData++;
    all += b.unavailableUnits || 0;
    neu += b.newlyMarkedUnits || 0;
    if (!b.baselineAvailable) baselineMissing++;
    if (b.integration) {
      byInt[b.integration]    = (byInt[b.integration]    || 0) + (b.unavailableUnits || 0);
      byIntNew[b.integration] = (byIntNew[b.integration] || 0) + (b.newlyMarkedUnits || 0);
    }
    (b.reasons || []).forEach(r => {
      const e = byReason.get(r.reason) || {reason: r.reason, count: 0, countNew: 0};
      e.count    += r.count    || 0;
      e.countNew += r.countNew || 0;
      byReason.set(r.reason, e);
    });
  });

  const rows = [...byReason.values()].map(e => ({
    ...e,
    pct:    all ? Math.round(1000 * e.count    / all) / 10 : 0,
    pctNew: neu ? Math.round(1000 * e.countNew / neu) / 10 : 0,
  }));

  return {
    ...base,
    reasonDistribution: rows,
    unavailableUnits: all,
    newlyMarkedUnits: neu,
    syncsAnalyzed: analyzed,
    syncsWithData: withData,
    skipped,
    baselineMissingBuildings: baselineMissing,
    byIntegration: byInt,
    byIntegrationNew: byIntNew,
    originalSyncs: analyzed,
    deduplicatedBuildings: analyzed,
  };
}

// One place that repaints everything the slider / toggle / sort can affect.
function siRepaint() {
  siRenderSyncsTable();
  if (syncIssues.lastResult) {
    const agg = siAggregateVisibleResult();
    _siRenderLiveDist(agg, !!syncIssues.lastResult.partial);
    siSetPreviewStatus(siSummaryLine(agg));
  }
}

function siSetMinPct(pct) {
  const next = Math.max(syncIssues.queryPct, Math.min(1, pct));
  if (Math.abs(next - syncIssues.minPct) < 1e-9) return;
  syncIssues.minPct = next;
  const val = document.getElementById('si-pct-value');
  if (val) val.textContent = `${Math.round(next * 100)}%`;
  siRepaint();
}

function siDistSortIndicator(key) {
  const st = syncIssues.sortDist;
  if (st.key !== key) return '';
  return st.dir === 'asc' ? ' <span class="si-sort-arrow">▲</span>'
                          : ' <span class="si-sort-arrow">▼</span>';
}

// Count and % rank identically within one scope, so both map to the active
// count; only Reason sorts as text.
function siSortDistRows(rows) {
  const {key, dir} = syncIssues.sortDist;
  rows.sort((a, b) => {
    let c;
    if (key === 'reason') {
      c = a.reason.toLowerCase() < b.reason.toLowerCase() ? -1
        : a.reason.toLowerCase() > b.reason.toLowerCase() ? 1 : 0;
    } else {
      c = siCount(a) - siCount(b);
      if (c === 0) c = a.reason.toLowerCase() < b.reason.toLowerCase() ? -1 : 1;
    }
    return dir === 'asc' ? c : -c;
  });
  return rows;
}

function siSortDistBy(key) {
  const st = syncIssues.sortDist;
  if (st.key === key) {
    st.dir = st.dir === 'desc' ? 'asc' : 'desc';
  } else {
    st.key = key;
    st.dir = key === 'reason' ? 'asc' : 'desc';
  }
  if (syncIssues.lastResult) {
    _siRenderLiveDist(siAggregateVisibleResult(), !!syncIssues.lastResult.partial);
  }
}

function siSortSyncsBy(key) {
  const st = syncIssues.sortSyncs;
  if (st.key === key) {
    st.dir = st.dir === 'desc' ? 'asc' : 'desc';
  } else {
    st.key = key;
    // Numeric columns are most useful largest-first; text ascending.
    const col = SI_SYNC_COLUMNS.find(c => c.key === key);
    st.dir = col && col.num ? 'desc' : 'asc';
  }
  siRenderSyncsTable();
}

// ── Per-building expand ─────────────────────────────────────────────────────

function siToggleBuilding(bid) {
  const detail = document.querySelector(`.si-detail-row[data-bid="${CSS.escape(bid)}"]`);
  const btn    = document.querySelector(`.si-expand-btn[data-bid="${CSS.escape(bid)}"]`);
  if (!detail) return;
  const willOpen = detail.hidden;
  detail.hidden = !willOpen;
  if (btn) {
    btn.textContent = willOpen ? '▼' : '▶';
    btn.setAttribute('aria-expanded', String(willOpen));
  }
  if (willOpen) { syncIssues.open.add(bid); siRenderBuildingDetail(bid); }
  else          { syncIssues.open.delete(bid); }
}

function siRenderBuildingDetail(bid) {
  const row = document.querySelector(`.si-detail-row[data-bid="${CSS.escape(bid)}"]`);
  if (!row || row.hidden) return;
  const host = row.querySelector('.si-detail');
  if (!host) return;
  const b = syncIssues.buildings[bid];

  if (!b) {
    host.innerHTML = `<div class="si-pending">Still analyzing this building…</div>`;
    return;
  }
  if (b.status === 'skipped') {
    host.innerHTML = `<div class="si-skip-note">
      <strong>Not analyzed.</strong> ${esc(b.skipReason || 'Unknown reason')}
    </div>`;
    return;
  }

  const reasons = siActiveReasons(b.reasons);
  const maxCount = Math.max(...reasons.map(siCount), 1);

  const distRows = reasons.map(r => {
    const barPct = Math.round(100 * siCount(r) / maxCount);
    return `<tr>
      <td>${esc(r.reason)}</td>
      <td style="text-align:right;font-variant-numeric:tabular-nums">${siCount(r)}</td>
      <td style="text-align:right;font-variant-numeric:tabular-nums">${siPct(r)}%</td>
      <td class="si-dist-bar-cell">
        <div class="si-dist-bar-wrap"><div class="si-dist-bar" style="width:${barPct}%"></div></div>
      </td>
    </tr>`;
  }).join('');

  const unitBlocks = reasons.map(r => {
    const units = siActiveUnits(r);
    if (!units.length) return '';
    const cols = ['status', 'rent', 'availableDate', 'sqft']
      .filter(c => units.some(u => u[c] != null));
    const head = ['Unit Key', 'Unit Number', ...cols.map(siUnitColLabel)]
      .map(h => `<th>${esc(h)}</th>`).join('');
    const body = units.map(u => `<tr>
      <td class="si-mono">${esc(String(u.unitKey ?? '—'))}</td>
      <td>${esc(String(u.unitNumber ?? '—'))}</td>
      ${cols.map(c => `<td>${esc(u[c] == null ? '—' : String(u[c]))}</td>`).join('')}
    </tr>`).join('');
    const more = r.unitsTruncated
      ? `<div class="si-units-more">Showing first ${units.length} of ${siCount(r)} units.</div>`
      : '';
    return `<details class="si-units">
      <summary>${esc(r.reason)} <span class="si-units-count">${siCount(r)} unit${siCount(r) === 1 ? '' : 's'}</span></summary>
      <div class="si-units-wrap">
        <table class="si-unit-table"><thead><tr>${head}</tr></thead><tbody>${body}</tbody></table>
        ${more}
      </div>
    </details>`;
  }).join('');

  // The baseline is the snapshot preceding the analysed one; without it we
  // cannot separate newly-marked units from already-unavailable ones.
  const baselineNote = b.baselineAvailable
    ? `baseline <span class="si-mono">${esc(b.baselineSnapshot || '')}</span>`
    : `<span class="si-warn">no pre-sync snapshot found — newly-marked count unavailable</span>`;

  const shown = syncIssues.showAll ? b.unavailableUnits : b.newlyMarkedUnits;
  const breakdown = b.baselineAvailable
    ? ` <span class="si-detail-sub">(${b.newlyMarkedUnits} newly marked, `
      + `${b.preExistingUnits} already unavailable)</span>`
    : '';

  const emptyMsg = syncIssues.showAll
    ? 'No unavailable units found in this snapshot.'
    : (b.baselineAvailable
        ? 'This sync newly marked no units unavailable — every unavailable unit was already unavailable beforehand.'
        : 'No pre-sync snapshot was found for this building, so newly-marked units cannot be identified. Switch to "All unavailable" to see the full distribution.');

  host.innerHTML = `
    <div class="si-detail-meta">
      ${esc(b.integration || '—')} · <span class="si-mono">${esc(b.snapshot || 'unknown snapshot')}</span> · ${baselineNote}
    </div>
    <div class="si-detail-meta">
      <strong style="color:#e6edf3">${shown}</strong> ${esc(siScopeLabel())}${breakdown}
    </div>
    ${reasons.length
      ? `<table class="si-dist-table">
           <thead><tr><th>Reason</th><th>Count</th><th>%</th><th style="width:160px"></th></tr></thead>
           <tbody>${distRows}</tbody>
         </table>
         ${unitBlocks ? `<div class="si-units-section">${unitBlocks}</div>` : ''}`
      : `<div class="si-pending">${esc(emptyMsg)}</div>`}`;
}

function siUnitColLabel(c) {
  return { status: 'Status', rent: 'Rent', availableDate: 'Available', sqft: 'Sq Ft' }[c] || c;
}

// Refresh the "Top Reason" cells and any expanded detail panes.
function siRefreshBuildingRows() {
  Object.entries(syncIssues.buildings).forEach(([bid, b]) => {
    const cell = document.querySelector(`.si-top-reason[data-bid="${CSS.escape(bid)}"]`);
    if (cell) {
      if (b.status === 'skipped') {
        cell.innerHTML = `<span class="si-skipped-tag" title="${esc(b.skipReason || '')}">skipped</span>`;
      } else if (!syncIssues.showAll && !b.baselineAvailable) {
        cell.innerHTML = `<span class="si-pending" title="No pre-sync snapshot found">no baseline</span>`;
      } else {
        const top = siActiveReasons(b.reasons)[0];
        cell.innerHTML = top
          ? `${esc(top.reason)} <span class="si-top-pct">${siPct(top)}%</span>`
          : `<span class="si-pending">none newly marked</span>`;
      }
    }
    const btn = document.querySelector(`.si-expand-btn[data-bid="${CSS.escape(bid)}"]`);
    if (btn) btn.disabled = false;
  });
  syncIssues.open.forEach(siRenderBuildingDetail);
}

function buildAnalyzeProgressHtml() {
  return `<div id="si-analyze-progress">
    <div id="si-analyze-progress-header">
      <div class="si-spinner"></div>
      <div id="si-analyze-progress-label">Running Availability Agent…</div>
    </div>
    <div id="si-analyze-progress-note">Loading integration indexes…</div>
    <div id="si-analyze-progress-track">
      <div id="si-analyze-progress-fill" style="width:2%"></div>
    </div>
  </div>
  <div id="si-live-dist"></div>`;
}

async function runSyncIssuesAnalyze() {
  if (!syncIssues.syncs.length) return;
  try {
    const res = await fetch('/api/sync-issues/analyze', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ syncs: syncIssues.syncs }),
    });
    const data = await res.json();
    if (!res.ok || data.error) throw new Error(data.error || res.statusText);
    syncIssues.jobId = data.jobId;
    clearInterval(syncIssues.polling);
    syncIssues.polling = setInterval(pollSyncIssuesJob, 2500);
  } catch (e) {
    siSetSidebarStatus(`Analysis failed: ${e.message}`, true);
    siSetPreviewStatus('Analysis failed');
    // Replace progress bar with error note
    const prog = document.getElementById('si-analyze-progress');
    if (prog) prog.innerHTML = `<div style="color:#f85149;font-size:12px">${esc(e.message)}</div>`;
  }
}

async function pollSyncIssuesJob() {
  if (!syncIssues.jobId) return;
  try {
    const res  = await fetch(`/api/job?id=${encodeURIComponent(syncIssues.jobId)}`);
    const data = await res.json();
    const { status, done, total, note, result, error } = data;

    // A 404 / error payload has no status — surface it instead of falling
    // through to the "done" branch with an undefined result.
    if (!status) {
      throw new Error(error || `job status unavailable (HTTP ${res.status})`);
    }

    if (status === 'running') {
      const frac = total ? done / total : 0;
      const pct  = total ? `${done} / ${total}` : '…';
      const fill = document.getElementById('si-analyze-progress-fill');
      if (fill) fill.style.width = Math.max(2, Math.round(frac * 100)) + '%';
      const lbl = document.getElementById('si-analyze-progress-label');
      if (lbl) lbl.textContent = `Running Availability Agent — ${pct} buildings`;
      const noteEl = document.getElementById('si-analyze-progress-note');
      if (noteEl) noteEl.textContent = note || '';
      siSetPreviewStatus(`Analyzing — ${pct} buildings`);
      // Render live partial distribution as it accumulates
      if (result) {
        syncIssues.buildings  = result.buildings || {};
        syncIssues.lastResult = result;
        siRefreshBuildingRows();
        if ((result.reasonDistribution || []).length > 0) {
          _siRenderLiveDist(siAggregateVisibleResult(), true);
        }
      }
      return;
    }

    clearInterval(syncIssues.polling);
    syncIssues.polling = null;
    syncIssues.jobId   = null;

    if (status === 'error') {
      siSetSidebarStatus(`Analysis error: ${error || 'unknown'}`, true);
      siSetPreviewStatus('Analysis error');
      const prog = document.getElementById('si-analyze-progress');
      if (prog) prog.innerHTML =
        `<div style="color:#f85149;font-size:12px">Analysis error: ${esc(error || 'unknown')}</div>`;
      return;
    }

    // Done — remove progress bar, finalize distribution
    const prog = document.getElementById('si-analyze-progress');
    if (prog) prog.remove();

    const r = result || {};
    syncIssues.buildings  = r.buildings || {};
    syncIssues.lastResult = r;
    // Re-render through the shared path so an active slider / sort / scope
    // selection is preserved when the job finishes.
    siRepaint();
    const agg = siAggregateVisibleResult();
    siSetSidebarStatus(
      `Done — ${agg.newlyMarkedUnits || 0} newly marked / ${agg.unavailableUnits || 0} unavailable`, false);
  } catch (e) {
    // Stop the loop and show the failure rather than polling forever in silence.
    clearInterval(syncIssues.polling);
    syncIssues.polling = null;
    syncIssues.jobId   = null;
    siSetSidebarStatus(`Analysis failed: ${e.message}`, true);
    siSetPreviewStatus('Analysis failed');
    const prog = document.getElementById('si-analyze-progress');
    if (prog) prog.innerHTML =
      `<div style="color:#f85149;font-size:12px">Analysis failed: ${esc(e.message)}</div>`;
  }
}

function _siRenderLiveDist(result, isPartial) {
  // The progress card owns #si-live-dist; if it was already removed, recreate
  // the container so the final distribution always has somewhere to render.
  let liveDist = document.getElementById('si-live-dist');
  if (!liveDist) {
    const body = document.getElementById('si-preview-body');
    if (!body) return;
    liveDist = document.createElement('div');
    liveDist.id = 'si-live-dist';
    body.appendChild(liveDist);
  }
  // Preserve which sections the user had open, since every slider drag, sort,
  // or scope change re-renders this subtree.
  const prevCombined = liveDist.querySelector('.si-combined');
  const wasOpen = prevCombined ? prevCombined.open : false;

  const el = buildDistributionHtml(result, isPartial);
  liveDist.innerHTML = '';
  liveDist.appendChild(el);

  const nextCombined = liveDist.querySelector('.si-combined');
  if (nextCombined) nextCombined.open = wasOpen;
}

function buildDistributionHtml(result, isPartial) {
  const dist = siActiveReasons(result.reasonDistribution);
  const wrap = document.createElement('div');
  wrap.className = 'si-dist-section';

  const headingSuffix = isPartial ? ' <span style="color:#6e7681;font-weight:400">(updating…)</span>' : '';

  if (!dist.length) {
    // The slider is the likelier cause once it has been raised, so name it
    // rather than pointing at the scope toggle.
    const filtered = syncIssues.minPct > syncIssues.queryPct + 1e-9;
    const msg = filtered
      ? `No syncs are at or above ${Math.round(syncIssues.minPct * 100)}% unavailable. `
        + `Lower the Min % Unavail. slider to widen the results.`
      : (syncIssues.showAll
          ? 'No unavailable units found yet in analyzed snapshots.'
          : 'No newly-marked units found yet. Switch to \u201cAll unavailable\u201d to include units that were already unavailable before the sync.');
    wrap.innerHTML = `<div class="si-dist-heading">Combined Distribution — All Buildings${headingSuffix}</div>
      <div style="font-size:12px;color:#8b949e;padding:8px 0">${msg}</div>`;
    return wrap;
  }

  const maxCount = Math.max(...dist.map(siCount), 1);
  siSortDistRows(dist);
  const rows = dist.map(d => {
    const barPct = Math.round(100 * siCount(d) / maxCount);
    return `<tr>
      <td>${esc(d.reason)}</td>
      <td style="text-align:right;font-variant-numeric:tabular-nums">${siCount(d)}</td>
      <td style="text-align:right;font-variant-numeric:tabular-nums">${siPct(d)}%</td>
      <td class="si-dist-bar-cell">
        <div class="si-dist-bar-wrap">
          <div class="si-dist-bar" style="width:${barPct}%"></div>
        </div>
      </td>
    </tr>`;
  }).join('');

  const skippedNote = result.skipped
    ? ` · ${result.skipped} skipped (expand a row for the reason)`
    : '';
  // Buildings with no pre-sync snapshot contribute nothing to the newly-marked
  // view, so say so rather than letting them silently vanish.
  const baselineNote = (!syncIssues.showAll && result.baselineMissingBuildings)
    ? ` · ${result.baselineMissingBuildings} building${result.baselineMissingBuildings === 1 ? '' : 's'} excluded (no pre-sync snapshot)`
    : '';
  const dedup = result.deduplicatedBuildings;
  const orig  = result.originalSyncs;
  const dedupNote = (dedup && orig && orig > dedup)
    ? ` · ${orig} syncs → ${dedup} unique buildings`
    : '';

  const byInt = Object.entries(
    (syncIssues.showAll ? result.byIntegration : result.byIntegrationNew) || {}
  ).filter(([, v]) => v > 0).sort((a, b) => b[1] - a[1]);
  const chips = byInt.map(([k, v]) =>
    `<span class="si-int-chip">${esc(k)} <strong>${v}</strong></span>`
  ).join('');

  // A failed rollout/metadata lookup leaves rollout-dependent overrides
  // dormant, which under-reports reasons — say so rather than hiding it.
  const lookupWarn = (result.rolloutError || result.enrichError)
    ? `<div class="si-lookup-warn">⚠ Building/rollout metadata lookup failed — `
      + `rollout-dependent reasons (AppFolio "Not Posted to Website", RealPage `
      + `"Exclude Not Rent Ready Units") were not evaluated. `
      + `${esc(result.rolloutError || result.enrichError)}</div>`
    : '';

  // Per-building distributions live in the Flagged Syncs table now, so the
  // all-buildings rollup is collapsed by default.
  wrap.innerHTML = `${lookupWarn}
    <details class="si-combined">
      <summary>
        <span class="si-dist-heading">Combined Distribution — All Buildings${headingSuffix}</span>
      </summary>
      <div class="si-combined-body">
        <div class="si-dist-meta">
          ${syncIssues.showAll ? result.unavailableUnits : result.newlyMarkedUnits} ${esc(siScopeLabel())} · ${result.syncsWithData} buildings${skippedNote}${dedupNote}${baselineNote}
        </div>
        ${chips ? `<div class="si-by-int">${chips}</div>` : ''}
        <table class="si-dist-table">
          <thead><tr>
            <th class="si-dist-sortable" data-sortkey="reason">Reason${siDistSortIndicator('reason')}</th>
            <th class="si-dist-sortable" data-sortkey="count">Count${siDistSortIndicator('count')}</th>
            <th class="si-dist-sortable" data-sortkey="pct">%${siDistSortIndicator('pct')}</th>
            <th style="width:160px"></th>
          </tr></thead>
          <tbody>${rows}</tbody>
        </table>
      </div>
    </details>`;
  return wrap;
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
