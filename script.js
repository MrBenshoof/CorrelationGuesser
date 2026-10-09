(function () {
  'use strict';

  // ---------- Configuration ----------
  var NUM_POINTS = 24;
  var RANGE = 10;               // axes run from -RANGE to +RANGE
  var SUCCESS_TOL = 0.1;        // within this = success
  var FAIL_TOL = 0.4;           // off by more than this = failure
  var MIN_POINTS = 3;           // can't delete below this many points
  var HISTORY_MAX = 100;
  var STORE_STATS = 'cg-stats';
  var STORE_THEME = 'cg-theme';

  // SVG geometry (viewBox is 640 x 640)
  var SIZE = 640, PAD = 34;
  var UNIT = (SIZE - 2 * PAD) / (2 * RANGE);
  var SVGNS = 'http://www.w3.org/2000/svg';

  // ---------- Local storage helpers (never leaves the device) ----------
  function load(key) {
    try { var v = localStorage.getItem(key); return v ? JSON.parse(v) : null; } catch (e) { return null; }
  }
  function save(key, value) {
    try { localStorage.setItem(key, JSON.stringify(value)); } catch (e) { /* storage unavailable */ }
  }

  // ---------- Math ----------
  function randn() {
    var u = 0, v = 0;
    while (u === 0) u = Math.random();
    while (v === 0) v = Math.random();
    return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
  }
  function mean(a) { var s = 0; for (var i = 0; i < a.length; i++) s += a[i]; return s / a.length; }

  function standardize(a) {
    var m = mean(a), s = 0, i;
    for (i = 0; i < a.length; i++) s += (a[i] - m) * (a[i] - m);
    s = Math.sqrt(s / a.length) || 1;
    return a.map(function (v) { return (v - m) / s; });
  }

  // Returns { n, r, slope, intercept, r2 } ; r/slope/intercept are null when undefined.
  function regression(pts) {
    var n = pts.length;
    var out = { n: n, r: null, slope: null, intercept: null, r2: null };
    if (n < 2) return out;
    var mx = 0, my = 0, i;
    for (i = 0; i < n; i++) { mx += pts[i].x; my += pts[i].y; }
    mx /= n; my /= n;
    var sxx = 0, syy = 0, sxy = 0;
    for (i = 0; i < n; i++) {
      var dx = pts[i].x - mx, dy = pts[i].y - my;
      sxx += dx * dx; syy += dy * dy; sxy += dx * dy;
    }
    if (sxx > 1e-12) {
      out.slope = sxy / sxx;
      out.intercept = my - out.slope * mx;
    }
    if (sxx > 1e-12 && syy > 1e-12) {
      out.r = Math.max(-1, Math.min(1, sxy / Math.sqrt(sxx * syy)));
      out.r2 = out.r * out.r;
    } else if (sxx > 1e-12 && syy <= 1e-12) {
      out.r = 0; out.r2 = 0; // perfectly flat line: r is technically undefined; show 0 for simplicity
    }
    return out;
  }

  // Generate points whose sample correlation equals a randomly chosen target r.
  function generatePoints() {
    var target = Math.random() * 2 - 1;
    var xs = [], zs = [], i;
    for (i = 0; i < NUM_POINTS; i++) { xs.push(randn()); zs.push(randn()); }
    xs = standardize(xs);
    // Remove the component of z along x, so x and z are exactly uncorrelated.
    var mz = mean(zs), dot = 0;
    for (i = 0; i < NUM_POINTS; i++) dot += xs[i] * (zs[i] - mz);
    dot /= NUM_POINTS;
    zs = standardize(zs.map(function (z, k) { return z - mz - dot * xs[k]; }));
    var k2 = Math.sqrt(1 - target * target);
    var ys = xs.map(function (x, k) { return target * x + k2 * zs[k]; });

    // Per-axis scaling and shifting leaves r unchanged.
    var sx = 2.2 + Math.random() * 1.2, sy = 2.2 + Math.random() * 1.2;
    var cx = (Math.random() - 0.5) * 4, cy = (Math.random() - 0.5) * 4;
    var px = xs.map(function (v) { return v * sx; });
    var py = ys.map(function (v) { return v * sy; });
    // Shrink about the centre if anything would fall outside the grid.
    var limit = RANGE - 0.6;
    function fit(arr, c) {
      var m = 0; arr.forEach(function (v) { m = Math.max(m, Math.abs(v + c)); });
      return m > limit ? (limit - Math.abs(c)) / (m - Math.abs(c)) : 1;
    }
    var fx = fit(px, cx), fy = fit(py, cy);
    return px.map(function (v, idx) {
      return { x: v * fx + cx, y: py[idx] * fy + cy };
    });
  }

  // ---------- State ----------
  var points = [];
  var trueR = 0;
  var guess = null;
  var phase = 'guessing'; // 'guessing' | 'exploring'
  var verdictState = null;
  var dragIdx = -1;
  var newIdx = -1;
  var stats = load(STORE_STATS) || { attempts: 0, successes: 0, streak: 0, best: 0, history: [] };
  if (!Array.isArray(stats.history)) stats.history = [];

  // ---------- DOM ----------
  var $ = function (id) { return document.getElementById(id); };
  var svg = $('plot'), plotCard = $('plot-card'), hint = $('plot-hint');
  var form = $('guess-form'), input = $('guess-input'), errorEl = $('guess-error');
  var submitBtn = $('submit-btn'), nextBtn = $('next-btn'), signBtn = $('sign-btn');
  var resultCard = $('result-card'), rValue = $('r-value'), verdictEl = $('verdict');
  var detailsEl = $('details'), tipEl = $('explore-tip');

  // ---------- Coordinate transforms ----------
  function sx(x) { return PAD + (x + RANGE) * UNIT; }
  function sy(y) { return PAD + (RANGE - y) * UNIT; }
  function ux(px) { return (px - PAD) / UNIT - RANGE; }
  function uy(py) { return RANGE - (py - PAD) / UNIT; }

  function el(name, attrs, parent) {
    var e = document.createElementNS(SVGNS, name);
    for (var k in attrs) if (Object.prototype.hasOwnProperty.call(attrs, k)) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }

  // ---------- Static grid ----------
  var gPoints, gLine;
  function drawGrid() {
    var i, p;
    var g = el('g', {}, svg);
    for (i = -RANGE; i <= RANGE; i++) {
      if (i === 0) continue;
      var cls = i % 5 === 0 ? 'grid-major' : 'grid-minor';
      el('line', { 'class': cls, x1: sx(i), y1: PAD, x2: sx(i), y2: SIZE - PAD }, g);
      el('line', { 'class': cls, x1: PAD, y1: sy(i), x2: SIZE - PAD, y2: sy(i) }, g);
    }
    // Axes
    el('line', { 'class': 'axis', x1: PAD, y1: sy(0), x2: SIZE - PAD + 8, y2: sy(0) }, g);
    el('line', { 'class': 'axis', x1: sx(0), y1: SIZE - PAD, x2: sx(0), y2: PAD - 8 }, g);
    el('path', { 'class': 'axis-arrow', d: 'M' + (SIZE - PAD + 14) + ' ' + sy(0) + ' l-9 -5 v10 z' }, g);
    el('path', { 'class': 'axis-arrow', d: 'M' + sx(0) + ' ' + (PAD - 14) + ' l-5 9 h10 z' }, g);
    // Tick labels every 2 units (skip 0 on axes; label origin once)
    for (i = -RANGE; i <= RANGE; i += 2) {
      if (i === 0) continue;
      p = el('text', { 'class': 'tick-label', x: sx(i), y: sy(0) + 17, 'text-anchor': 'middle' }, g);
      p.textContent = i;
      p = el('text', { 'class': 'tick-label', x: sx(0) - 8, y: sy(i) + 4.5, 'text-anchor': 'end' }, g);
      p.textContent = i;
    }
    p = el('text', { 'class': 'tick-label', x: sx(0) - 8, y: sy(0) + 17, 'text-anchor': 'end' }, g);
    p.textContent = '0';
    p = el('text', { 'class': 'axis-title', x: SIZE - 8, y: sy(0) - 12, 'text-anchor': 'end' }, g);
    p.textContent = 'x';
    p = el('text', { 'class': 'axis-title', x: sx(0) + 12, y: PAD - 14 }, g);
    p.textContent = 'y';

    gLine = el('g', {}, svg);
    gPoints = el('g', {}, svg);
  }

  // ---------- Dynamic drawing ----------
  // Clip the line y = a + b x to the visible square using Liang–Barsky.
  function clipLine(a, b) {
    var x0 = -RANGE, y0 = a + b * x0, dx = 2 * RANGE, dy = b * dx;
    var t0 = 0, t1 = 1;
    var p = [-dx, dx, -dy, dy];
    var q = [x0 + RANGE, RANGE - x0, y0 + RANGE, RANGE - y0];
    for (var i = 0; i < 4; i++) {
      if (p[i] === 0) { if (q[i] < 0) return null; }
      else {
        var t = q[i] / p[i];
        if (p[i] < 0) { if (t > t1) return null; if (t > t0) t0 = t; }
        else { if (t < t0) return null; if (t < t1) t1 = t; }
      }
    }
    return [x0 + t0 * dx, y0 + t0 * dy, x0 + t1 * dx, y0 + t1 * dy];
  }

  function render() {
    // Points
    gPoints.textContent = '';
    points.forEach(function (pt, i) {
      var g = el('g', { 'class': 'pt' + (i === dragIdx ? ' active' : '') + (i === newIdx ? ' new' : ''), 'data-i': i }, gPoints);
      el('circle', { 'class': 'pt-hit', cx: sx(pt.x), cy: sy(pt.y), r: 18 }, g);
      el('circle', { 'class': 'pt-dot', cx: sx(pt.x), cy: sy(pt.y), r: 8 }, g);
    });
    newIdx = -1;

    // Regression line (after guess only)
    gLine.textContent = '';
    var reg = regression(points);
    if (phase === 'exploring') {
      if (reg.slope !== null) {
        var seg = clipLine(reg.intercept, reg.slope);
        if (seg) el('line', { 'class': 'reg-line', x1: sx(seg[0]), y1: sy(seg[1]), x2: sx(seg[2]), y2: sy(seg[3]) }, gLine);
      }
      updateReadout(reg);
    }
  }

  function fmt(v, d) {
    if (v === null) return '—';
    var s = v.toFixed(d);
    return /^-0\.?0*$/.test(s) ? s.slice(1) : s; // avoid "-0.000"
  }
  function signed(v) { return (v < 0 ? '− ' : '+ ') + Math.abs(v).toFixed(2); }

  function updateReadout(reg) {
    rValue.textContent = reg.r === null ? 'undefined' : fmt(reg.r, 3);
    $('d-r2').textContent = fmt(reg.r2, 3);
    $('d-n').textContent = reg.n;
    $('d-eq').textContent = reg.slope === null ? 'x = constant (vertical)' : 'y = ' + reg.intercept.toFixed(2) + ' ' + signed(reg.slope) + 'x';
    if (guess !== null) {
      // "Off by" shows how the student's guess compares with the CURRENT r as points change.
      $('d-error').textContent = reg.r === null ? '—' : fmt(Math.abs(guess - reg.r), 3);
    }
  }

  // ---------- Puzzle flow ----------
  function newPuzzle() {
    points = generatePoints();
    trueR = regression(points).r;
    guess = null;
    phase = 'guessing';
    verdictState = null;
    dragIdx = -1;

    plotCard.dataset.state = 'guessing';
    resultCard.dataset.state = '';
    svg.classList.remove('interactive', 'dragging');
    rValue.textContent = '?';
    verdictEl.textContent = 'Make a guess to reveal the true value.';
    detailsEl.hidden = true;
    tipEl.hidden = true;
    hint.textContent = 'Look at the pattern in the points, then type your estimate of r below.';
    input.value = '';
    input.disabled = false;
    errorEl.textContent = '';
    submitBtn.hidden = false;
    signBtn.hidden = false;
    nextBtn.hidden = true;
    render();
    input.focus({ preventScroll: true });
  }

  function parseGuess(text) {
    var t = text.trim().replace('−', '-').replace(',', '.');
    if (t === '') return { error: 'Enter a number between −1 and 1.' };
    if (!/^[-+]?(\d+\.?\d*|\.\d+)$/.test(t)) return { error: 'That doesn’t look like a number. Try something like 0.65 or -0.4.' };
    var v = parseFloat(t);
    if (v < -1 || v > 1) return { error: 'r must be between −1 and 1.' };
    return { value: v };
  }

  function onSubmit(e) {
    e.preventDefault();
    if (phase !== 'guessing') return;
    var res = parseGuess(input.value);
    if (res.error) { errorEl.textContent = res.error; input.focus(); return; }
    errorEl.textContent = '';
    guess = res.value;

    var diff = Math.abs(guess - trueR);
    var state, msg;
    if (diff <= SUCCESS_TOL + 1e-9) { state = 'good'; msg = '✓ Success! Within 0.1'; }
    else if (diff > FAIL_TOL) { state = 'bad'; msg = '✗ Not quite — off by more than 0.4'; }
    else { state = 'near'; msg = 'Close! Off by ' + diff.toFixed(2); }
    verdictState = state;

    phase = 'exploring';
    plotCard.dataset.state = state;
    resultCard.dataset.state = state;
    verdictEl.textContent = msg;
    $('d-guess').textContent = fmt(guess, 3);
    detailsEl.hidden = false;
    tipEl.hidden = false;
    input.disabled = true;
    submitBtn.hidden = true;
    signBtn.hidden = true;
    nextBtn.hidden = false;
    nextBtn.focus({ preventScroll: true });
    svg.classList.add('interactive');
    hint.textContent = 'Click the grid to add points • drag points to move them • double-click a point to remove it.';

    recordResult(guess, trueR, state);
    render();
  }

  // ---------- Stats ----------
  function recordResult(g, r, state) {
    stats.attempts++;
    if (state === 'good') { stats.successes++; stats.streak++; stats.best = Math.max(stats.best, stats.streak); }
    else stats.streak = 0;
    stats.history.unshift({ n: stats.attempts, guess: g, r: r, state: state });
    if (stats.history.length > HISTORY_MAX) stats.history.length = HISTORY_MAX;
    save(STORE_STATS, stats);
    renderStats();
  }

  function renderStats() {
    $('s-attempts').textContent = stats.attempts;
    $('s-success').textContent = stats.successes;
    $('s-streak').textContent = stats.streak;
    $('s-best').textContent = stats.best;
    var body = $('history-body');
    body.textContent = '';
    var has = stats.history.length > 0;
    $('history-table').hidden = !has;
    $('history-empty').hidden = has;
    stats.history.forEach(function (h) {
      var tr = document.createElement('tr');
      var cells = [h.n, fmt(h.guess, 2), fmt(h.r, 3), fmt(Math.abs(h.guess - h.r), 2),
                   h.state === 'good' ? '✓' : h.state === 'bad' ? '✗' : '~'];
      cells.forEach(function (c, i) {
        var td = document.createElement('td');
        td.textContent = c;
        if (i === 4) td.className = 'res-' + h.state;
        tr.appendChild(td);
      });
      body.appendChild(tr);
    });
  }

  // ---------- Pointer interaction (add / drag / delete points) ----------
  function eventToData(e) {
    var pt = svg.createSVGPoint();
    pt.x = e.clientX; pt.y = e.clientY;
    var p = pt.matrixTransform(svg.getScreenCTM().inverse());
    return {
      x: Math.max(-RANGE, Math.min(RANGE, ux(p.x))),
      y: Math.max(-RANGE, Math.min(RANGE, uy(p.y)))
    };
  }

  var lastTapIdx = -1, lastTapTime = 0;
  svg.addEventListener('pointerdown', function (e) {
    if (phase !== 'exploring' || (e.pointerType === 'mouse' && e.button !== 0)) return;
    e.preventDefault();
    var target = e.target.closest ? e.target.closest('.pt') : null;
    if (target) {
      var idx = parseInt(target.getAttribute('data-i'), 10);
      var now = Date.now();
      // Double-click / double-tap on the same point removes it.
      if (idx === lastTapIdx && now - lastTapTime < 350 && points.length > MIN_POINTS) {
        points.splice(idx, 1);
        lastTapIdx = -1;
        render();
        return;
      }
      lastTapIdx = idx; lastTapTime = now;
      dragIdx = idx;
    } else {
      lastTapIdx = -1;
      var d = eventToData(e);
      points.push(d);
      dragIdx = points.length - 1;
      newIdx = dragIdx;
    }
    try { svg.setPointerCapture(e.pointerId); } catch (err) {}
    svg.classList.add('dragging');
    render();
  });

  svg.addEventListener('pointermove', function (e) {
    if (dragIdx < 0) return;
    var d = eventToData(e);
    points[dragIdx].x = d.x;
    points[dragIdx].y = d.y;
    render();
  });

  function endDrag(e) {
    if (dragIdx < 0) return;
    dragIdx = -1;
    svg.classList.remove('dragging');
    try { svg.releasePointerCapture(e.pointerId); } catch (err) {}
    render();
  }
  svg.addEventListener('pointerup', endDrag);
  svg.addEventListener('pointercancel', endDrag);

  svg.addEventListener('contextmenu', function (e) { if (phase === 'exploring') e.preventDefault(); });

  // ---------- Controls ----------
  form.addEventListener('submit', onSubmit);
  nextBtn.addEventListener('click', newPuzzle);

  signBtn.addEventListener('click', function () {
    var t = input.value.trim().replace('−', '-');
    input.value = t.charAt(0) === '-' ? t.slice(1) : '-' + t;
    input.focus();
  });

  $('clear-btn').addEventListener('click', function () {
    if (!window.confirm('Clear your saved stats and guess history on this device?')) return;
    stats = { attempts: 0, successes: 0, streak: 0, best: 0, history: [] };
    save(STORE_STATS, stats);
    renderStats();
  });

  // Theme toggle
  var themeBtn = $('theme-toggle');
  function applyThemeLabel() {
    var dark = document.documentElement.getAttribute('data-theme') === 'dark';
    themeBtn.setAttribute('aria-label', dark ? 'Switch to light mode' : 'Switch to dark mode');
  }
  themeBtn.addEventListener('click', function () {
    var next = document.documentElement.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
    document.documentElement.setAttribute('data-theme', next);
    try { localStorage.setItem(STORE_THEME, next); } catch (e) {}
    applyThemeLabel();
  });
  applyThemeLabel();

  // Full-screen toggle (hidden where the browser doesn't support it, e.g. iPhone Safari)
  var fsBtn = $('fs-toggle');
  var root = document.documentElement;
  var canFs = !!(root.requestFullscreen || root.webkitRequestFullscreen);
  function fsElement() { return document.fullscreenElement || document.webkitFullscreenElement; }
  function syncFs() {
    var on = !!fsElement();
    document.body.classList.toggle('is-fullscreen', on);
    fsBtn.setAttribute('aria-label', on ? 'Exit full screen' : 'Enter full screen');
    fsBtn.title = on ? 'Exit full screen' : 'Full screen';
  }
  if (canFs) {
    fsBtn.hidden = false;
    fsBtn.addEventListener('click', function () {
      try {
        if (fsElement()) (document.exitFullscreen || document.webkitExitFullscreen).call(document);
        else (root.requestFullscreen || root.webkitRequestFullscreen).call(root);
      } catch (e) { /* request denied */ }
    });
    document.addEventListener('fullscreenchange', syncFs);
    document.addEventListener('webkitfullscreenchange', syncFs);
    syncFs();
  }

  // ---------- Go ----------
  drawGrid();
  renderStats();
  newPuzzle();
})();
