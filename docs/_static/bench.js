/* Renders the benchmark pages from the JSON published by stp/benchmarks-data.
 *
 * The data files are static: campaigns.json lists every campaign with its
 * provenance and headline, and summary/<name>.json carries the per-logic and
 * per-family breakdown. Nothing here is generated at build time, so refreshing
 * the numbers means publishing new JSON, not rebuilding the manual. */
(function () {
  'use strict';

  /* The data lives in its own repository, because a campaign is tens of
     megabytes of results and a 24 MB binary several times a year, and none of
     that is source. Both sites are served from stp.github.io, so this fetch is
     same-origin in production; the URL is absolute rather than root-relative
     so a local build of the manual shows real numbers too.

     window.BENCH_DATA_BASE overrides it, for testing a change to the data
     against a change to this page. */
  var BASE = window.BENCH_DATA_BASE || 'https://stp.github.io/benchmarks-data/data/';

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
    if (c.complete === false) {
      var live = el('p', 'bench-running');
      live.innerHTML = 'This campaign is <strong>still running</strong> — ' +
        num(h.n) + ' instances measured so far. The figures below are a ' +
        'partial sweep and will move.';
      host.appendChild(live);
    }
    tile(num(h.solved), 'of ' + num(h.n_counted) + '  (' + pct + '%)', 'solved');
    tile(num(h.timeout), '', 'timed out');
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

  /* Grouped by logic, so a logic's two modes sit together and the corpus
     reads as nine logics rather than seventeen unrelated rows. The logic name
     is printed once per group; the blank cell below it is the grouping, which
     is why each group also carries a rule above it.

     PAR-2 charges every unsolved instance twice the timeout, so one number
     carries both how many were solved and how quickly. It is totalled at the
     foot -- that cumulative figure is the one to compare between campaigns. */
  function byLogic(host, summary) {
    var groups = {};
    Object.keys(summary.by_logic).forEach(function (k) {
      var parts = k.split('/');
      (groups[parts[1]] = groups[parts[1]] || []).push(
        { mode: parts[0], a: summary.by_logic[k] });
    });
    var total = function (logic) {
      return groups[logic].reduce(function (t, r) { return t + r.a.n; }, 0);
    };
    var order = Object.keys(groups).sort(function (x, y) {
      return total(y) - total(x);
    });

    var table = el('table', 'bench-logics');
    var thead = el('thead');
    var hr = el('tr');
    ['Logic', 'Mode', 'Files', '', 'Solved', 'Timed out', 'Out of memory',
     'Unsupported', 'PAR-2 (s)', 'Solved time (s)'].forEach(function (h) {
      hr.appendChild(el('th', null, h));
    });
    thead.appendChild(hr);
    table.appendChild(thead);

    function barCell(label, a) {
      var cell = el('td');
      var b = el('div', 'bench-bar');
      var frac = a.n_counted ? a.solved / a.n_counted : 0;
      var solved = el('i');
      solved.style.width = (frac * 100).toFixed(2) + '%';
      b.appendChild(solved);
      if (frac < 1) {
        var rest = el('i', 'rest');
        rest.style.left = 'calc(' + (frac * 100).toFixed(2) + '% + 2px)';
        rest.style.right = '0';
        rest.style.width = 'auto';
        b.appendChild(rest);
      }
      hoverable(b, [
        '<strong>' + label + '</strong>',
        num(a.solved) + ' of ' + num(a.n_counted) + ' solved (' +
          (100 * frac).toFixed(1) + '%)',
        num(a.timeout) + ' timed out',
        a.memout ? num(a.memout) + ' out of memory' : '',
        a.unsupported ? num(a.unsupported) + ' unsupported (excluded)' : '',
        'PAR-2 ' + num(Math.round(a.par2)) + ' s',
        num(Math.round(a.wall_total)) + ' s spent on the instances that were solved'
      ].filter(Boolean));
      cell.appendChild(b);
      return cell;
    }

    function measures(tr, a) {
      tr.appendChild(el('td', null, num(a.timeout)));
      tr.appendChild(el('td', a.memout ? 'hit' : 'zero', num(a.memout)));
      tr.appendChild(el('td', 'zero', num(a.unsupported)));
      tr.appendChild(el('td', null, num(Math.round(a.par2))));
      tr.appendChild(el('td', null, num(Math.round(a.wall_total))));
    }

    order.forEach(function (logic) {
      var tb = el('tbody', 'grp');
      groups[logic].sort(function (x, y) { return y.a.n - x.a.n; })
        .forEach(function (r, i) {
          var tr = el('tr');
          // The logic name links to its unsolved list. Only the first row of
          // a group carries it, which is also what makes the grouping read.
          var lcell = el('td', 'logic');
          if (i === 0) {
            var link = el('a', null, logic);
            link.href = 'benchmark-failures.html?logic=' +
                        encodeURIComponent(logic);
            var unsolved = total(logic) -
              groups[logic].reduce(function (t, r) { return t + r.a.solved; }, 0);
            link.title = unsolved + ' unsolved ' + logic + ' instances';
            lcell.appendChild(link);
          }
          tr.appendChild(lcell);
          tr.appendChild(el('td', 'mode', r.mode));
          tr.appendChild(el('td', null, num(r.a.n)));
          // Bar first, then the count it encodes: the number reads as the
          // bar's label rather than as a separate column.
          tr.appendChild(barCell(logic + ' (' + r.mode + ')', r.a));
          tr.appendChild(el('td', null, num(r.a.solved)));
          measures(tr, r.a);
          tb.appendChild(tr);
        });
      table.appendChild(tb);
    });

    // Cumulative row taken from the campaign's own overall figures rather
    // than re-summed here, so the total cannot drift from the headline.
    var o = summary.overall;
    var tf = el('tfoot');
    var ftr = el('tr');
    ftr.appendChild(el('td', 'logic', 'All logics'));
    ftr.appendChild(el('td', 'mode', ''));
    ftr.appendChild(el('td', null, num(o.n)));
    ftr.appendChild(barCell('All logics', o));
    ftr.appendChild(el('td', null, num(o.solved)));
    measures(ftr, o);
    tf.appendChild(ftr);
    table.appendChild(tf);

    host.appendChild(table);
    legend(host);
    host.appendChild(el('p', 'bench-note',
      'PAR-2 charges every unsolved instance twice the timeout, so lower is ' +
      'better and the cumulative figure moves with both how many were solved ' +
      'and how quickly. Unsupported instances are excluded from it. Total ' +
      'time is the wall clock spent on the instances that were solved; ' +
      'unsolved ones are accounted for by PAR-2 rather than counted here.'));
  }

  /* Solved-count over time. Only drawn once there are at least two campaigns:
     a trend line through a single point is decoration, not information. */
  function overTime(host, campaigns) {
    // Nothing is drawn for a single campaign -- a trend line through one point
    // is decoration, and a placeholder telling the reader so is worse than an
    // absent section. The heading is added here, so it appears only with the
    // chart it belongs to.
    if (campaigns.length < 2) return;
    host.appendChild(el('h2', null, 'Over time'));
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
