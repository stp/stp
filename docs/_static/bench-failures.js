/* The per-logic failure list, reached by clicking a logic on the benchmarks
 * page. One page serves every logic: the logic is a query parameter, so there
 * is nothing to regenerate when the corpus or the campaign changes. */
(function () {
  'use strict';

  /* stp/benchmarks-data, same as bench.js; see the note there. */
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

  /* What each outcome means, in the reader's terms. A bare class name is a
     label; this is the sentence that makes the row actionable. */
  var MEANING = {
    timeout: 'ran out of time',
    memout: 'ran out of memory',
    error: 'crashed or reported an error',
    mismatch: 'answered, but disagreed with the benchmark’s stated result',
    unsupported: 'uses a feature STP does not implement'
  };
  var ORDER = ['mismatch', 'error', 'memout', 'timeout', 'unsupported'];

  function param(name) {
    var m = new RegExp('[?&]' + name + '=([^&]*)').exec(window.location.search);
    return m ? decodeURIComponent(m[1].replace(/\+/g, ' ')) : null;
  }

  function render(host, logic, data) {
    var rows = (data.by_logic || {})[logic] || [];
    var back = el('p');
    var a = el('a', null, '← All logics');
    a.href = 'benchmarks.html';
    back.appendChild(a);
    host.appendChild(back);

    host.appendChild(el('h2', null, logic));

    if (!rows.length) {
      host.appendChild(el('p', 'bench-note',
        'Every ' + logic + ' instance in campaign ' + data.campaign +
        ' was solved — nothing to list.'));
      return;
    }

    // Counts per outcome, so the reader knows the shape before the list.
    var counts = {};
    rows.forEach(function (r) { counts[r[2]] = (counts[r[2]] || 0) + 1; });
    var lead = el('p');
    lead.innerHTML = '<strong>' + num(rows.length) + '</strong> of the ' +
      logic + ' instances were not solved in campaign <code>' +
      data.campaign + '</code>, at a ' + data.timeout_s + ' s timeout and a ' +
      (data.mem_limit_bytes / 1073741824).toFixed(0) + ' GB memory ceiling.';
    host.appendChild(lead);

    var ul = el('ul', 'bench-counts');
    ORDER.filter(function (c) { return counts[c]; }).forEach(function (c) {
      var li = el('li');
      li.innerHTML = '<strong>' + num(counts[c]) + '</strong> ' + c +
        ' — ' + MEANING[c];
      ul.appendChild(li);
    });
    host.appendChild(ul);

    var table = el('table', 'bench-fail');
    var thead = el('thead');
    var hr = el('tr');
    ['Benchmark', 'Mode', 'Outcome', 'Wall', 'Peak memory'].forEach(function (h) {
      hr.appendChild(el('th', null, h));
    });
    thead.appendChild(hr);
    table.appendChild(thead);

    var tb = el('tbody');
    rows.slice().sort(function (x, y) {
      var d = ORDER.indexOf(x[2]) - ORDER.indexOf(y[2]);
      return d || x[0].localeCompare(y[0]);
    }).forEach(function (r) {
      var tr = el('tr');
      // The corpus-relative path is the benchmark's identity; the family is
      // the part worth scanning, so it leads and the rest is secondary.
      var pathCell = el('td', 'path');
      var file = r[0].split('/').pop();
      pathCell.appendChild(el('span', 'fam', r[5] + '/'));
      pathCell.appendChild(document.createTextNode(file));
      pathCell.title = r[0];
      tr.appendChild(pathCell);
      tr.appendChild(el('td', 'mode', r[1]));
      tr.appendChild(el('td', 'cls cls-' + r[2], r[2]));
      tr.appendChild(el('td', null, r[3] === null ? '—' : r[3] + 's'));
      tr.appendChild(el('td', null,
        r[4] ? (r[4] / 1048576).toFixed(2) + ' GB' : '—'));
      tb.appendChild(tr);
    });
    table.appendChild(tb);
    host.appendChild(table);
  }

  document.addEventListener('DOMContentLoaded', function () {
    var host = document.getElementById('bench-fail-root');
    if (!host) return;
    var logic = param('logic');
    var campaign = param('campaign');
    if (!logic) {
      host.appendChild(el('p', 'bench-note',
        'No logic given. Pick one from the benchmarks page.'));
      return;
    }
    var chain = campaign
      ? Promise.resolve(campaign)
      : fetch(BASE + 'campaigns.json').then(function (r) { return r.json(); })
          .then(function (cs) { return cs[cs.length - 1].name; });
    chain.then(function (name) {
      return fetch(BASE + 'failures/' + name + '.json').then(function (r) {
        if (!r.ok) throw new Error('failures: HTTP ' + r.status);
        return r.json();
      });
    }).then(function (data) {
      render(host, logic, data);
    }).catch(function (e) {
      host.appendChild(el('p', 'bench-note',
        'Could not load the failure list (' + e.message + ').'));
    });
  });
})();
