/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

// Text, CSV and HTML renderings of the measurements.

#include "PropagatorBench.h"

#include <cmath>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <set>
#include <sstream>

namespace propbench
{
namespace
{

string rate(double perSecond)
{
  std::ostringstream o;
  o << std::fixed;
  if (perSecond >= 1e9)
    o << std::setprecision(2) << perSecond / 1e9 << "G";
  else if (perSecond >= 1e6)
    o << std::setprecision(2) << perSecond / 1e6 << "M";
  else if (perSecond >= 1e3)
    o << std::setprecision(0) << perSecond / 1e3 << "k";
  else
    o << std::setprecision(0) << perSecond;
  return o.str();
}

string fixed(double v, int places)
{
  std::ostringstream o;
  o << std::fixed << std::setprecision(places) << v;
  return o.str();
}

// yes / no / unknown, from the exhaustive run and the SAT spot check.
string verdict(const Row& r)
{
  if (r.precision.unsound > 0 || r.witnessUnsound > 0 || r.sat.unsound > 0)
    return "unsound";
  if (!r.precision.ran || r.precision.cases == 0)
    return "?";
  if (!r.precision.maximallyPrecise())
    return "no";
  if (r.sat.ran && r.sat.cases > 0 && r.sat.precise < r.sat.cases)
    return "no";
  return "yes";
}

string precisionDetail(const Row& r)
{
  std::ostringstream o;
  if (!r.precision.ran || r.precision.cases == 0)
    o << "not checked";
  else
  {
    o << "exhaustive w=" << r.precision.width << ": " << r.precision.precise
      << "/" << r.precision.cases << " cases";
    if (r.precision.derivable > 0)
      o << ", " << fixed(100.0 * r.precision.gained / r.precision.derivable, 1)
        << "% of deducible bits";
    if (r.precision.missedConflict > 0)
      o << ", " << r.precision.missedConflict << " missed conflicts";
    if (r.precision.unsound > 0)
      o << ", " << r.precision.unsound << " UNSOUND";
  }
  if (r.sat.ran && r.sat.cases > 0)
  {
    o << "; SAT w=" << r.width << ": " << r.sat.precise << "/" << r.sat.cases;
    if (r.sat.unsound > 0)
      o << " (" << r.sat.unsound << " UNSOUND)";
  }
  if (r.bcp.ran && r.bcp.cases > 0)
  {
    o << "; vs bit-blasted: " << fixed(r.bcp.bcpBits, 2) << " vs "
      << fixed(r.bcp.cbitpBits, 2) << " bits (";
    if (r.bcp.bcpBits <= 0 && r.bcp.cbitpBits > 0)
      o << "all new";
    else
      o << fixed(r.bcp.ratio(), 1) << "x";
    o << ", " << r.bcp.cases << " cases, " << r.bcp.clauses << " clauses/"
      << r.bcp.variables << " vars)";
  }
  if (r.bcpExhaustive.ran && r.bcpExhaustive.cases > 0)
  {
    const BcpExhaustive& e = r.bcpExhaustive;
    o << "; encoding arc-consistent w=" << e.width << ": "
      << (e.arcConsistent() ? "yes" : "NO") << " (" << e.complete << "/"
      << e.cases << " cases, " << e.contradictory << " contradictory";
    if (e.incomplete > 0)
      o << ", " << e.incomplete << " incomplete";
    if (e.missedConflict > 0)
      o << ", " << e.missedConflict << " MISSED CONFLICTS";
    if (e.unsound > 0)
      o << ", " << e.unsound << " UNSOUND";
    o << ")";
  }
  if (r.consistency.ran)
  {
    const ConsistencyCheck& k = r.consistency;
    o << "; consistency w=" << k.width << " (" << k.clauses << " clauses/"
      << k.variables << " vars, " << k.ioVars << " io): URC "
      << (k.urc() ? "yes" : "NO");
    if (k.urcMissed > 0)
    {
      unsigned worst = 0;
      for (size_t u = 0; u < k.urcMissedByUnset.size(); u++)
        if (k.urcMissedByUnset[u] > 0)
        {
          worst = (unsigned)u;
          break;
        }
      o << " (" << k.urcMissed << "/" << k.ioContradictory
        << " conflicts missed, some with only " << worst << " unset)";
    }
    o << ", GAC " << (k.gac() ? "yes" : "NO");
    if (k.gacDerivable > 0)
      o << " (" << fixed(100.0 * k.gacDerived / k.gacDerivable, 1)
        << "% of implied literals over " << k.ioCases << " cases)";
    o << ", PC ";
    if (!k.pcRan)
      o << "not checked";
    else
    {
      o << (k.pc() ? "yes" : "NO") << " ("
        << (k.pcExhaustive ? "exhaustive" : "sampled") << ", ";
      if (k.pcDerivable > 0)
        o << fixed(100.0 * k.pcDerived / k.pcDerivable, 1) << "% of literals, ";
      o << k.pcMissedConflict << "/" << k.pcContradictory
        << " conflicts missed)";
    }
    if (k.unsound > 0)
      o << ", " << k.unsound << " UNSOUND";
  }
  if (r.witnessUnsound > 0)
    o << "; " << r.witnessUnsound << " timed cases lost their solution";
  if (r.conflicts > 0)
    o << "; " << r.conflicts << " unexpected conflicts";
  return o.str();
}

string escape(const string& s)
{
  string out;
  for (char c : s)
  {
    if (c == '&') out += "&amp;";
    else if (c == '<') out += "&lt;";
    else if (c == '>') out += "&gt;";
    else if (c == '"') out += "&quot;";
    else out += c;
  }
  return out;
}

string configSummary(const Config& c)
{
  std::ostringstream o;
  o << c.iterations << " cases per configuration, " << c.repeats
    << " timed repeats (median reported), " << c.budgetSeconds
    << "s budget each, arity " << c.arity << ", seed " << c.seed;
  if (c.satCases > 0)
    o << ", " << c.satCases << " SAT-checked cases per row";
  if (c.bcpCases > 0)
    o << ", " << c.bcpCases << " cases per row against the bit-blasted "
      << "encoding (CNF: " << (c.cnf.empty() ? "medium" : c.cnf) << ")";
  return o.str();
}

} // namespace

// ---------------------------------------------------------------------------

void printText(const Config& cfg, const vector<Row>& rows)
{
  for (Domain d : {Domain::Cbitp, Domain::Interval, Domain::ValueSet})
  {
    bool any = false;
    for (const Row& r : rows)
      any = any || r.domain == d;
    if (!any)
      continue;

    std::cout << "\n== " << name(d) << " ==\n";
    std::cout << std::left << std::setw(14) << "op" << std::setw(12)
              << "direction" << std::setw(7) << "width" << std::setw(12)
              << "input" << std::right << std::setw(12) << "ops/sec"
              << std::setw(12) << "ns/call" << std::setw(10) << "bits"
              << "  " << std::left << std::setw(8) << "precise"
              << "detail\n";

    for (const Row& r : rows)
    {
      if (r.domain != d)
        continue;
      std::cout << std::left << std::setw(14) << r.op << std::setw(12)
                << name(r.direction) << std::setw(7) << r.width
                << std::setw(12) << r.input << std::right << std::setw(12)
                << rate(r.opsPerSec) << std::setw(12) << fixed(r.nsPerCall, 1)
                << std::setw(10) << fixed(r.bitsGained, 2) << "  " << std::left
                << std::setw(8) << verdict(r) << precisionDetail(r) << "\n";
    }
  }
  std::cout << "\n" << configSummary(cfg) << std::endl;
}

// ---------------------------------------------------------------------------

void writeCsv(const Config& cfg, const vector<Row>& rows, const string& path)
{
  std::ofstream f(path.c_str());
  if (!f)
  {
    std::cerr << "propagator_bench: cannot write " << path << std::endl;
    return;
  }
  f << "domain,op,direction,width,arity,input,ops_per_second,ns_per_call,"
       "bits_gained_per_call,calls,conflicts,maximally_precise,"
       "exhaustive_width,exhaustive_cases,exhaustive_precise,"
       "exhaustive_unsound,exhaustive_missed_conflicts,deducible_bits,"
       "gained_bits,sat_cases,sat_precise,sat_unsound,"
       "bcp_cases,bcp_bits,bcp_cbitp_bits,bcp_clauses,bcp_vars,"
       "cons_width,cons_clauses,cons_literals,cons_vars,cons_io_vars,"
       "cons_urc,cons_gac,cons_pc,cons_io_cases,cons_io_contradictory,"
       "cons_urc_missed,cons_urc_missed_min_unset,cons_gac_incomplete,"
       "cons_gac_derivable,cons_gac_derived,cons_pc_mode,cons_pc_cases,"
       "cons_pc_contradictory,cons_pc_missed_conflicts,cons_pc_incomplete,"
       "cons_pc_derivable,cons_pc_derived,cons_unsound\n";
  for (const Row& r : rows)
  {
    f << name(r.domain) << "," << r.op << "," << name(r.direction) << ","
      << r.width << "," << r.arity << ",\"" << r.input << "\","
      << fixed(r.opsPerSec, 0) << "," << fixed(r.nsPerCall, 2) << ","
      << fixed(r.bitsGained, 4) << "," << r.calls << "," << r.conflicts << ","
      << verdict(r) << "," << r.precision.width << "," << r.precision.cases
      << "," << r.precision.precise << "," << r.precision.unsound << ","
      << r.precision.missedConflict << "," << r.precision.derivable << ","
      << r.precision.gained << "," << r.sat.cases << "," << r.sat.precise
      << "," << r.sat.unsound << "," << r.bcp.cases << ","
      << fixed(r.bcp.bcpBits, 4) << "," << fixed(r.bcp.cbitpBits, 4) << ","
      << r.bcp.clauses << "," << r.bcp.variables;

    const ConsistencyCheck& k = r.consistency;
    int minUnset = -1;
    for (size_t u = 0; u < k.urcMissedByUnset.size() && minUnset < 0; u++)
      if (k.urcMissedByUnset[u] > 0)
        minUnset = (int)u;
    f << "," << (k.ran ? k.width : 0) << "," << k.clauses << "," << k.literals
      << "," << k.variables << "," << k.ioVars << ","
      << (!k.ran ? "" : k.urc() ? "yes" : "no") << ","
      << (!k.ran ? "" : k.gac() ? "yes" : "no") << ","
      << (!k.pcRan ? "" : k.pc() ? "yes" : "no") << "," << k.ioCases << ","
      << k.ioContradictory << "," << k.urcMissed << "," << minUnset << ","
      << k.gacIncomplete << "," << k.gacDerivable << "," << k.gacDerived
      << ","
      << (!k.pcRan ? "" : k.pcExhaustive ? "exhaustive" : "sampled") << ","
      << k.pcCases << "," << k.pcContradictory << "," << k.pcMissedConflict
      << "," << k.pcIncomplete << "," << k.pcDerivable << "," << k.pcDerived
      << "," << k.unsound << "\n";
  }
  (void)cfg;
  std::cout << "wrote " << path << std::endl;
}

// ---------------------------------------------------------------------------

void writeHtml(const Config& cfg, const vector<Row>& rows, const string& path)
{
  std::ofstream f(path.c_str());
  if (!f)
  {
    std::cerr << "propagator_bench: cannot write " << path << std::endl;
    return;
  }

  f << "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n"
    << "<meta charset=\"utf-8\">\n"
    << "<meta name=\"viewport\" content=\"width=device-width, "
       "initial-scale=1\">\n"
    << "<title>STP propagator benchmark</title>\n<style>\n"
    << ":root { color-scheme: light dark;\n"
    << "  --bg: #ffffff; --fg: #1a1a1a; --muted: #666; --line: #d8d8d8;\n"
    << "  --head: #f4f4f6; --zebra: #fafafa; --good: #0a7a3d; --bad: #a33;\n"
    << "  --warn: #8a6d00; }\n"
    << "@media (prefers-color-scheme: dark) {\n"
    << ":root { --bg: #14161a; --fg: #e6e6e6; --muted: #9aa0a6;\n"
    << "  --line: #2c3038; --head: #1c1f25; --zebra: #181b20;\n"
    << "  --good: #4ec97f; --bad: #f08a8a; --warn: #e0c060; } }\n"
    << "body { background: var(--bg); color: var(--fg); margin: 0 auto;\n"
    << "  padding: 2rem 1.2rem; max-width: 1200px;\n"
    << "  font: 15px/1.5 system-ui, -apple-system, 'Segoe UI', sans-serif; }\n"
    << "h1 { font-size: 1.5rem; margin: 0 0 .3rem; }\n"
    << "h2 { font-size: 1.15rem; margin: 2.2rem 0 .4rem; }\n"
    << "p.note, .meta { color: var(--muted); font-size: .87rem; }\n"
    << ".wrap { overflow-x: auto; border: 1px solid var(--line);\n"
    << "  border-radius: 6px; }\n"
    << "table { border-collapse: collapse; width: 100%; font-size: .88rem; }\n"
    << "th, td { padding: .38rem .6rem; text-align: right;\n"
    << "  border-bottom: 1px solid var(--line); white-space: nowrap; }\n"
    << "th:first-child, td:first-child, th.l, td.l { text-align: left; }\n"
    << "thead th { background: var(--head); position: sticky; top: 0;\n"
    << "  cursor: pointer; user-select: none; }\n"
    << "tbody tr:nth-child(even) { background: var(--zebra); }\n"
    << "td.detail { color: var(--muted); font-size: .8rem;\n"
    << "  white-space: normal; }\n"
    << ".yes { color: var(--good); font-weight: 600; }\n"
    << ".no { color: var(--bad); }\n"
    << ".unsound { color: var(--bad); font-weight: 700; }\n"
    << ".unknown { color: var(--muted); }\n"
    << ".filters { margin: .6rem 0; display: flex; flex-wrap: wrap;\n"
    << "  gap: .5rem; align-items: center; font-size: .85rem; }\n"
    << "select, input { font: inherit; padding: .2rem .35rem;\n"
    << "  background: var(--bg); color: var(--fg);\n"
    << "  border: 1px solid var(--line); border-radius: 4px; }\n"
    << "code { font-size: .85em; }\n"
    << "</style>\n</head>\n<body>\n";

  f << "<h1>STP propagator benchmark</h1>\n";
  f << "<p class=\"meta\">" << escape(configSummary(cfg)) << ".</p>\n";
  f << "<p class=\"note\">Every case is built from a concrete solution and "
       "then partially forgotten, so no case is contradictory and no "
       "propagator can short-circuit on a conflict. Timings are the median "
       "of the repeats; on a loaded machine treat them as an upper bound on "
       "the cost. <em>bits</em> is the information the propagator deduced per "
       "call: newly fixed bits for cbitp, and the width less the log of the "
       "domain's size for the interval and value-set analyses. "
       "<em>precise</em> is whether the propagator deduced everything that "
       "follows from its inputs, checked exhaustively at the small width "
       "given in the last column";
  if (cfg.satCases > 0)
    f << " and spot-checked at the benchmarked width against the SAT-based "
         "maximally precise propagator";
  f << ".</p>\n";
  if (cfg.bcpCases > 0)
    f << "<p class=\"note\"><em>vs bit-blasted</em> is the other comparison: "
         "how many bits unit propagation over the CNF encoding of the same "
         "operation fixes, against how many the transfer function fixes, on "
         "the same cases. STP bit-blasts and calls a SAT solver anyway, so "
         "the multiplier is what the word-level propagator adds over what "
         "the solver would have found without it.</p>\n";

  for (Domain d : {Domain::Cbitp, Domain::Interval, Domain::ValueSet})
  {
    bool any = false;
    for (const Row& r : rows)
      any = any || r.domain == d;
    if (!any)
      continue;

    const string id = name(d);
    f << "<h2>" << id << "</h2>\n";
    if (d == Domain::Cbitp)
      f << "<p class=\"note\">simplifier::constantBitP -- the transfer "
           "functions in <code>ConstantBitP_*.cpp</code>. They propagate in "
           "both directions; the direction column says what was known going "
           "in.</p>\n";
    else if (d == Domain::Interval)
      f << "<p class=\"note\">stp::UnsignedIntervalAnalysis -- unsigned "
           "intervals, bottom up only. Inputs are the tightest interval "
           "around the same partially fixed bits the cbitp rows use.</p>\n";
    else
      f << "<p class=\"note\">stp::ValueSetAnalysis -- sets of up to "
           "12 values, bottom up only, evaluated over the cartesian product "
           "of the children's sets.</p>\n";

    // Filters.
    std::set<string> directions, widths, inputs, ops;
    for (const Row& r : rows)
      if (r.domain == d)
      {
        directions.insert(name(r.direction));
        widths.insert(std::to_string(r.width));
        inputs.insert(r.input);
        ops.insert(r.op);
      }

    f << "<div class=\"filters\" data-for=\"" << id << "\">\n";
    const char* labels[] = {"op", "direction", "width", "input"};
    const std::set<string>* sets[] = {&ops, &directions, &widths, &inputs};
    for (int i = 0; i < 4; i++)
    {
      f << "<label>" << labels[i] << " <select data-col=\"" << i
        << "\"><option value=\"\">all</option>";
      for (const string& v : *sets[i])
        f << "<option>" << escape(v) << "</option>";
      f << "</select></label>\n";
    }
    f << "</div>\n";

    f << "<div class=\"wrap\"><table id=\"t_" << id << "\">\n<thead><tr>"
      << "<th class=\"l\">op</th><th class=\"l\">direction</th>"
      << "<th>width</th><th class=\"l\">input</th><th>ops/sec</th>"
      << "<th>ns/call</th><th>bits</th><th class=\"l\">precise</th>"
      << "<th class=\"l\">precision detail</th></tr></thead>\n<tbody>\n";

    for (const Row& r : rows)
    {
      if (r.domain != d)
        continue;
      const string v = verdict(r);
      const string cls =
          v == "yes" ? "yes" : (v == "no" ? "no"
                                          : (v == "unsound" ? "unsound"
                                                            : "unknown"));
      f << "<tr><td class=\"l\">" << escape(r.op) << "</td><td class=\"l\">"
        << name(r.direction) << "</td><td data-v=\"" << r.width << "\">"
        << r.width << "</td><td class=\"l\">" << escape(r.input)
        << "</td><td data-v=\"" << fixed(r.opsPerSec, 0) << "\">"
        << rate(r.opsPerSec) << "</td><td data-v=\"" << fixed(r.nsPerCall, 2)
        << "\">" << fixed(r.nsPerCall, 1) << "</td><td data-v=\""
        << fixed(r.bitsGained, 4) << "\">" << fixed(r.bitsGained, 2)
        << "</td><td class=\"l " << cls << "\">" << v
        << "</td><td class=\"detail l\">" << escape(precisionDetail(r))
        << "</td></tr>\n";
    }
    f << "</tbody></table></div>\n";
  }

  f << "<script>\n"
    << "function cellValue(row, i) {\n"
    << "  const c = row.cells[i];\n"
    << "  const v = c.getAttribute('data-v');\n"
    << "  return v === null ? c.textContent.trim() : parseFloat(v);\n"
    << "}\n"
    << "document.querySelectorAll('table').forEach(function (table) {\n"
    << "  table.querySelectorAll('thead th').forEach(function (th, i) {\n"
    << "    let asc = false;\n"
    << "    th.addEventListener('click', function () {\n"
    << "      asc = !asc;\n"
    << "      const body = table.tBodies[0];\n"
    << "      const rows = Array.from(body.rows);\n"
    << "      rows.sort(function (a, b) {\n"
    << "        const x = cellValue(a, i), y = cellValue(b, i);\n"
    << "        if (x < y) return asc ? -1 : 1;\n"
    << "        if (x > y) return asc ? 1 : -1;\n"
    << "        return 0;\n"
    << "      });\n"
    << "      rows.forEach(function (r) { body.appendChild(r); });\n"
    << "    });\n"
    << "  });\n"
    << "});\n"
    << "document.querySelectorAll('.filters').forEach(function (bar) {\n"
    << "  const table = document.getElementById('t_' + bar.dataset.for);\n"
    << "  function apply() {\n"
    << "    const want = {};\n"
    << "    bar.querySelectorAll('select').forEach(function (s) {\n"
    << "      if (s.value) want[s.dataset.col] = s.value;\n"
    << "    });\n"
    << "    Array.from(table.tBodies[0].rows).forEach(function (row) {\n"
    << "      let show = true;\n"
    << "      for (const col in want)\n"
    << "        if (row.cells[col].textContent.trim() !== want[col])\n"
    << "          show = false;\n"
    << "      row.style.display = show ? '' : 'none';\n"
    << "    });\n"
    << "  }\n"
    << "  bar.querySelectorAll('select').forEach(function (s) {\n"
    << "    s.addEventListener('change', apply);\n"
    << "  });\n"
    << "});\n"
    << "</script>\n</body>\n</html>\n";

  std::cout << "wrote " << path << std::endl;
}
} // namespace propbench
