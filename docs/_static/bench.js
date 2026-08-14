/* Renders the benchmark pages from the JSON that scripts/bench exports.
 *
 * The data files are static: campaigns.json lists every campaign with its
 * provenance and headline, and summary/<name>.json carries the per-logic and
 * per-family breakdown. Nothing here is generated at build time, so refreshing
 * the numbers means dropping in new JSON, not rebuilding the manual. */
(function () {
  'use strict';

  var BASE = '_static/bench/';

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text !== undefined) e.textContent = text;
    return e;
  }

  function num(n) {
    return n === null || n === undefined ? '—' : n.toLocaleString('en');
  }

  /* One shared tooltip. Every mark gets a hover layer: an HTML chart is
     interactive, and a bar the reader cannot interrogate is a picture. */
  var tip = el('div', 'bench-tip');
  document.body.appendChild(tip);

  function hoverable(node, lines) {
    node.addEventListener('mouseenter', function () {
      tip.innerHTML = lines.join('<br>');
      tip.classList.add('on');
    });
    node.addEventListener('mousemove', function (ev) {
      var pad = 14;
      tip.style.left = Math.min(ev.clientX + pad,
                                window.innerWidth - tip.offsetWidth - 4) + 'px';
      tip.style.top = (ev.clientY + pad) + 'px';
    });
    node.addEventListener('mouseleave', function () {
      tip.classList.remove('on');
    });
  }

  function tiles(host, c) {
    var h = c.headline;
    var box = el('div', 'bench-tiles');
    function tile(value, sub, label, alarm) {
      var t = el('div', 'bench-tile' + (alarm ? ' alarm' : ''));
      var n = el('div', 'n');
      n.appendChild(document.createTextNode(value));
      if (sub) { var s = el('small'); s.textContent = ' ' + sub; n.appendChild(s); }
      t.appendChild(n);
      t.appendChild(el('div', 'k', label));
      box.appendChild(t);
    }
    var pct = h.n_counted ? (100 * h.solved / h.n_counted).toFixed(1) : '0';
    tile(num(h.solved), 'of ' + num(h.n_counted) + '  (' + pct + '%)', 'solved');
    tile(num(h.timeout), '', 'timed out');
    tile(h.wall_median === null ? '—' : h.wall_median + 's', '', 'median wall');
    // Mismatches are the soundness gate: a wrong answer invalidates a campaign,
    // so the number is always shown even when it is zero, and coloured only
    // when it is not.
    tile(num(h.mismatch), '', 'answer mismatches', h.mismatch > 0);
    host.appendChild(box);
  }

  function meta(host, c) {
    var solvers = Object.keys(c.solvers || {}).map(function (k) {
      var v = c.solvers[k];
      return k + (v && v.version ? ' ' + v.version : '');
    }).join(', ');
    var p = el('p', 'bench-meta');
    p.innerHTML =
      'Commit <code>' + (c.commit_sha || '').slice(0, 12) + '</code>' +
      (c.commit_date ? ' (' + c.commit_date.slice(0, 10) + ')' : '') +
      ' &middot; ' + num(c.timeout_s) + ' s timeout, ' +
      (c.mem_limit_bytes / 1073741824).toFixed(0) + ' GB memory ceiling, ' +
      c.jobs + ' jobs' +
      (solvers ? ' &middot; ' + solvers : '') +
      (c.solver_flags ? ' &middot; <code>' + c.solver_flags + '</code>' : '');
    host.appendChild(p);
  }

  function legend(host) {
    var l = el('div', 'bench-legend');
    [['solved', 'var(--solved)'], ['unsolved', 'var(--unsolved)']].forEach(function (p) {
      var s = el('span');
      var i = el('i');
      i.style.background = p[1];
      s.appendChild(i);
      s.appendChild(document.createTextNode(p[0]));
      l.appendChild(s);
    });
    host.appendChild(l);
  }

  function byLogic(host, summary) {
    var rows = Object.keys(summary.by_logic).map(function (k) {
      var a = summary.by_logic[k];
      var parts = k.split('/');
      return { mode: parts[0], logic: parts[1], a: a };
    }).sort(function (x, y) { return y.a.n - x.a.n; });

    var table = el('table');
    var thead = el('thead');
    var hr = el('tr');
    ['Logic', 'Mode', 'Files', 'Solved', '', 'Timed out', 'Median wall'].forEach(function (h) {
      hr.appendChild(el('th', null, h));
    });
    thead.appendChild(hr);
    table.appendChild(thead);

    var tb = el('tbody');
    rows.forEach(function (r) {
      var a = r.a, tr = el('tr');
      tr.appendChild(el('td', 'logic', r.logic));
      tr.appendChild(el('td', 'mode', r.mode));
      tr.appendChild(el('td', null, num(a.n)));
      tr.appendChild(el('td', null, num(a.solved)));

      var barCell = el('td');
      var bar = el('div', 'bench-bar');
      var frac = a.n_counted ? a.solved / a.n_counted : 0;
      var solved = el('i');
      solved.style.width = (frac * 100).toFixed(2) + '%';
      var rest = el('i', 'rest');
      // 2px surface gap between the two fills so they read as separate marks.
      rest.style.left = 'calc(' + (frac * 100).toFixed(2) + '% + 2px)';
      rest.style.right = '0';
      rest.style.width = 'auto';
      bar.appendChild(solved);
      if (frac < 1) bar.appendChild(rest);
      hoverable(bar, [
        '<strong>' + r.logic + '</strong> (' + r.mode + ')',
        num(a.solved) + ' of ' + num(a.n_counted) + ' solved (' +
          (100 * frac).toFixed(1) + '%)',
        num(a.timeout) + ' timed out' +
          (a.memout ? ', ' + num(a.memout) + ' out of memory' : ''),
        a.unsupported ? num(a.unsupported) + ' unsupported (excluded)' : ''
      ].filter(Boolean));
      barCell.appendChild(bar);
      tr.appendChild(barCell);

      tr.appendChild(el('td', null, num(a.timeout)));
      tr.appendChild(el('td', null, a.wall_median === null ? '—' : a.wall_median + 's'));
      tb.appendChild(tr);
    });
    table.appendChild(tb);
    host.appendChild(table);
    legend(host);
  }

  /* Solved-count over time. Only drawn once there are at least two campaigns:
     a trend line through a single point is decoration, not information. */
  function overTime(host, campaigns) {
    if (campaigns.length < 2) {
      host.appendChild(el('p', 'bench-note',
        'A trend needs more than one campaign — this chart appears once a ' +
        'second run has been recorded.'));
      return;
    }
    var W = 720, H = 260, m = { t: 16, r: 16, b: 34, l: 52 };
    var xs = W - m.l - m.r, ys = H - m.t - m.b;
    var vals = campaigns.map(function (c) { return c.headline.solved; });
    var lo = 0, hi = Math.max.apply(null, vals) * 1.08;
    var X = function (i) { return m.l + (campaigns.length === 1 ? xs / 2 : i * xs / (campaigns.length - 1)); };
    var Y = function (v) { return m.t + ys - (v - lo) / (hi - lo) * ys; };

    var ns = 'http://www.w3.org/2000/svg';
    var svg = document.createElementNS(ns, 'svg');
    svg.setAttribute('viewBox', '0 0 ' + W + ' ' + H);
    svg.setAttribute('role', 'img');
    svg.setAttribute('aria-label', 'Instances solved per campaign');

    for (var g = 0; g <= 4; g++) {
      var v = lo + (hi - lo) * g / 4;
      var ln = document.createElementNS(ns, 'line');
      ln.setAttribute('x1', m.l); ln.setAttribute('x2', W - m.r);
      ln.setAttribute('y1', Y(v)); ln.setAttribute('y2', Y(v));
      ln.setAttribute('stroke', 'var(--rule)');
      ln.setAttribute('stroke-width', g === 0 ? 1 : 0.5);
      svg.appendChild(ln);
      var tx = document.createElementNS(ns, 'text');
      tx.setAttribute('x', m.l - 8); tx.setAttribute('y', Y(v) + 4);
      tx.setAttribute('text-anchor', 'end');
      tx.setAttribute('font-size', '11'); tx.setAttribute('fill', 'var(--muted)');
      tx.textContent = Math.round(v).toLocaleString('en');
      svg.appendChild(tx);
    }

    var d = campaigns.map(function (c, i) {
      return (i ? 'L' : 'M') + X(i) + ' ' + Y(c.headline.solved);
    }).join(' ');
    var path = document.createElementNS(ns, 'path');
    path.setAttribute('d', d);
    path.setAttribute('fill', 'none');
    path.setAttribute('stroke', 'var(--solved)');
    path.setAttribute('stroke-width', '2');
    svg.appendChild(path);

    campaigns.forEach(function (c, i) {
      var pt = document.createElementNS(ns, 'circle');
      pt.setAttribute('cx', X(i)); pt.setAttribute('cy', Y(c.headline.solved));
      pt.setAttribute('r', '4.5');
      pt.setAttribute('fill', 'var(--solved)');
      pt.setAttribute('stroke', 'var(--surface)');
      pt.setAttribute('stroke-width', '2');
      svg.appendChild(pt);
      var hit = document.createElementNS(ns, 'circle');
      hit.setAttribute('cx', X(i)); hit.setAttribute('cy', Y(c.headline.solved));
      hit.setAttribute('r', '14'); hit.setAttribute('fill', 'transparent');
      hoverable(hit, [
        '<strong>' + c.name + '</strong>',
        num(c.headline.solved) + ' of ' + num(c.headline.n_counted) + ' solved',
        'commit ' + (c.commit_sha || '').slice(0, 12)
      ]);
      svg.appendChild(hit);
      var lb = document.createElementNS(ns, 'text');
      lb.setAttribute('x', X(i)); lb.setAttribute('y', H - 12);
      lb.setAttribute('text-anchor', 'middle');
      lb.setAttribute('font-size', '11'); lb.setAttribute('fill', 'var(--muted)');
      lb.textContent = (c.commit_sha || c.name).slice(0, 7);
      svg.appendChild(lb);
    });

    var wrap = el('div', 'bench-chart');
    wrap.appendChild(svg);
    host.appendChild(wrap);
  }

  function fail(host, msg) {
    host.appendChild(el('p', 'bench-note', msg));
  }

  document.addEventListener('DOMContentLoaded', function () {
    var host = document.getElementById('bench-root');
    if (!host) return;
    fetch(BASE + 'campaigns.json').then(function (r) {
      if (!r.ok) throw new Error('campaigns.json: HTTP ' + r.status);
      return r.json();
    }).then(function (campaigns) {
      if (!campaigns.length) { fail(host, 'No campaigns have been recorded yet.'); return; }
      var latest = campaigns[campaigns.length - 1];
      host.appendChild(el('h2', null, 'Latest campaign'));
      tiles(host, latest);
      meta(host, latest);
      host.appendChild(el('h2', null, 'Over time'));
      overTime(host, campaigns);
      return fetch(BASE + 'summary/' + latest.name + '.json').then(function (r) {
        if (!r.ok) throw new Error('summary: HTTP ' + r.status);
        return r.json();
      }).then(function (summary) {
        host.appendChild(el('h2', null, 'By logic'));
        byLogic(host, summary);
      });
    }).catch(function (e) {
      fail(host, 'Could not load the benchmark data (' + e.message + ').');
    });
  });
})();
