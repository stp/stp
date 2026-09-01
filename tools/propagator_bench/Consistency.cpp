/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: September, 2026
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

// Graded GAC / URC / PC verdicts for the bit-blasted encoding.
//
// The exhaustive check in Cbitp.cpp answers the arc-consistency question
// through a fresh SAT solver per case. This one grades the answer and asks
// the propagation-completeness question too -- every CNF variable,
// auxiliaries included -- which multiplies the case count past what a solver
// restart per case can afford. So it propagates the clauses itself: counting
// unit propagation over occurrence lists, with the semantic side answered
// from a solution table held as one bitset column per variable.
//
// The table is built by asserting every input pattern and propagating; the
// encodings' auxiliaries are functions of the inputs, so each pattern yields
// its row directly. Patterns unit propagation does not finish are completed
// by enumeration, so an encoding is not required to evaluate forward under
// unit propagation alone.

#include "PropagatorBench.h"

#include <algorithm>
#include <fstream>
#include <iostream>

using namespace stp;

namespace propbench
{
namespace
{

uint64_t pow3Capped(unsigned n, uint64_t cap)
{
  uint64_t r = 1;
  for (unsigned i = 0; i < n; i++)
  {
    if (r > cap / 3)
      return cap + 1;
    r *= 3;
  }
  return r;
}

// Counting unit propagation. Small formulas, millions of calls: occurrence
// lists and a resettable trail, nothing cleverer.
struct UpEngine
{
  unsigned nVars = 0;
  const vector<vector<int>>* clauses = nullptr;
  vector<vector<unsigned>> occ; // literal 2v+neg -> clauses containing it
  vector<int8_t> val;           // by variable: 0 unset, 1 true, -1 false
  vector<unsigned> trail;
  size_t base = 0; // trail length after the formula's own unit clauses
  bool baseConflict = false;

  void init(const vector<vector<int>>& cls, unsigned nv)
  {
    nVars = nv;
    clauses = &cls;
    occ.assign(2 * (size_t)nv, {});
    for (unsigned ci = 0; ci < cls.size(); ci++)
      for (int lit : cls[ci])
        occ[lit].push_back(ci);
    val.assign(nv, 0);
    trail.clear();

    // The formula's unit clauses, propagated once and kept: occurrence-driven
    // propagation only ever revisits a clause when a literal in it just
    // became false, so a clause that arrives unit has to be applied here.
    for (const vector<int>& c : cls)
      if (c.size() == 1 && !assign(c[0] >> 1, !(c[0] & 1)))
      {
        baseConflict = true;
        return;
      }
    baseConflict = !propagate(0);
    base = trail.size();
  }

  void undoTo(size_t mark)
  {
    while (trail.size() > mark)
    {
      val[trail.back()] = 0;
      trail.pop_back();
    }
  }

  // False when the variable is already fixed the other way.
  bool assign(unsigned var, bool value)
  {
    if (val[var] != 0)
      return (val[var] > 0) == value;
    val[var] = value ? 1 : -1;
    trail.push_back(var);
    return true;
  }

  bool litTrue(int lit) const
  {
    const int8_t v = val[lit >> 1];
    return v != 0 && (v > 0) == !(lit & 1);
  }

  // Propagates everything on the trail from `from`; false on conflict.
  bool propagate(size_t from)
  {
    for (size_t head = from; head < trail.size(); head++)
    {
      const unsigned var = trail[head];
      const unsigned falseLit = 2 * var + (val[var] > 0 ? 1 : 0);
      for (unsigned ci : occ[falseLit])
      {
        const vector<int>& cls = (*clauses)[ci];
        int unit = 0;
        unsigned unassigned = 0;
        bool satisfied = false;
        for (int lit : cls)
        {
          const int8_t v = val[lit >> 1];
          if (v == 0)
          {
            unit = lit;
            if (++unassigned > 1)
              break;
          }
          else if ((v > 0) == !(lit & 1))
          {
            satisfied = true;
            break;
          }
        }
        if (satisfied || unassigned > 1)
          continue;
        if (unassigned == 0)
          return false;
        assign(unit >> 1, !(unit & 1)); // unset, so it cannot fail
      }
    }
    return true;
  }
};

// The solution set, one bitset column per variable over the rows.
struct Table
{
  bool ok = false;
  unsigned nRows = 0;
  unsigned words = 0;
  vector<uint64_t> full;             // nRows bits set
  vector<vector<uint64_t>> colTrue;  // by variable

  static constexpr unsigned MAX_ROWS = 1u << 16;

  void addRow(const UpEngine& up)
  {
    for (unsigned v = 1; v < up.nVars; v++)
      if (up.val[v] > 0)
        colTrue[v][nRows >> 6] |= 1ull << (nRows & 63);
    nRows++;
  }
};

// Enumerates every total solution extending the current trail. Unit
// propagation has already run; branches only on what it left unset.
bool enumerate(UpEngine& up, Table& t)
{
  unsigned branch = 0;
  for (unsigned v = 1; v < up.nVars; v++)
    if (up.val[v] == 0)
    {
      branch = v;
      break;
    }
  if (branch == 0)
  {
    if (t.nRows >= Table::MAX_ROWS)
      return false;
    t.addRow(up);
    return true;
  }
  for (int b = 0; b < 2; b++)
  {
    const size_t mark = up.trail.size();
    if (up.assign(branch, b == 1) && up.propagate(mark))
      if (!enumerate(up, t))
        return false;
    up.undoTo(mark);
  }
  return true;
}

// One scope's exhaustive-or-sampled sweep. `digits` is reused across calls.
struct SweepCounts
{
  uint64_t cases = 0;
  uint64_t contradictory = 0;
  uint64_t missedConflict = 0;
  uint64_t incomplete = 0;
  uint64_t derivable = 0;
  uint64_t derived = 0;
  uint64_t unsound = 0;
  vector<uint64_t> missedByUnset; // sized by the caller when it wants it
};

void oneCase(UpEngine& up, const Table& t, const vector<unsigned>& scope,
             const vector<int8_t>& digits, SweepCounts& out)
{
  out.cases++;

  // The rows this case still admits.
  static thread_local vector<uint64_t> mask;
  mask.assign(t.full.begin(), t.full.end());
  bool any = false;
  for (size_t i = 0; i < scope.size(); i++)
  {
    if (digits[i] == 0)
      continue;
    const vector<uint64_t>& col = t.colTrue[scope[i]];
    for (unsigned w = 0; w < t.words; w++)
      mask[w] &= (digits[i] > 0) ? col[w] : (t.full[w] & ~col[w]);
  }
  for (unsigned w = 0; w < t.words && !any; w++)
    any = mask[w] != 0;

  // Unit propagation on the same case.
  const size_t mark = up.trail.size();
  bool conflict = false;
  for (size_t i = 0; i < scope.size() && !conflict; i++)
    if (digits[i] != 0)
      conflict = !up.assign(scope[i], digits[i] > 0);
  if (!conflict)
    conflict = !up.propagate(mark);

  if (!any)
  {
    out.contradictory++;
    if (!conflict)
    {
      out.missedConflict++;
      if (!out.missedByUnset.empty())
      {
        unsigned unset = 0;
        for (int8_t d : digits)
          if (d == 0)
            unset++;
        out.missedByUnset[unset]++;
      }
    }
    up.undoTo(mark);
    return;
  }

  if (conflict)
  {
    out.unsound++;
    up.undoTo(mark);
    return;
  }

  // Implied literals of the unset scope variables, against what propagation
  // fixed. Propagation only ever derives entailed literals, so a derived
  // value disagreeing with an implied one means the table is wrong.
  uint64_t derivableHere = 0, derivedHere = 0;
  for (size_t i = 0; i < scope.size(); i++)
  {
    if (digits[i] != 0)
      continue;
    const vector<uint64_t>& col = t.colTrue[scope[i]];
    bool alwaysTrue = true, alwaysFalse = true;
    for (unsigned w = 0; w < t.words && (alwaysTrue || alwaysFalse); w++)
    {
      if (mask[w] & ~col[w])
        alwaysTrue = false;
      if (mask[w] & col[w])
        alwaysFalse = false;
    }
    const int8_t got = up.val[scope[i]];
    if (alwaysTrue || alwaysFalse)
    {
      derivableHere++;
      if (got != 0)
      {
        if ((got > 0) == alwaysTrue)
          derivedHere++;
        else
          out.unsound++;
      }
    }
    else if (got != 0)
      out.unsound++;
  }
  out.derivable += derivableHere;
  out.derived += derivedHere;
  if (derivedHere < derivableHere)
    out.incomplete++;

  up.undoTo(mark);
}

void sweepExhaustive(UpEngine& up, const Table& t,
                     const vector<unsigned>& scope, SweepCounts& out)
{
  vector<int8_t> digits(scope.size(), -1);
  bool done = scope.empty();
  while (!done)
  {
    oneCase(up, t, scope, digits, out);
    done = true;
    for (size_t i = 0; i < digits.size(); i++)
    {
      if (++digits[i] <= 1)
      {
        done = false;
        break;
      }
      digits[i] = -1;
    }
  }
}

void sweepSampled(UpEngine& up, const Table& t, const vector<unsigned>& scope,
                  uint64_t samples, unsigned seed, SweepCounts& out)
{
  std::mt19937 rand(seed);
  std::uniform_int_distribution<int> digit(-1, 1);
  vector<int8_t> digits(scope.size());
  for (uint64_t s = 0; s < samples; s++)
  {
    for (size_t i = 0; i < digits.size(); i++)
      digits[i] = (int8_t)digit(rand);
    oneCase(up, t, scope, digits, out);
  }
}

} // namespace

ConsistencyCheck consistencyCheck(STPMgr* mgr, const OpSpec& op,
                                  const Config& cfg)
{
  ConsistencyCheck res;

  const unsigned width = cfg.consistencyWidth;
  const Layout l = layoutFor(op, width, cfg.arity);
  if (!l.ok || l.packedBits() > 20)
    return res;

  BcpEncoding* enc = makeBcpEncoding(mgr, op, l);
  if (enc == NULL)
    return res;

  vector<vector<int>> clauses;
  vector<vector<unsigned>> io;
  unsigned nVars = 0;
  const bool got = bcpMaterial(enc, clauses, io, nVars);
  destroyBcpEncoding(enc);
  if (!got || io.empty())
    return res;

  UpEngine up;
  up.init(clauses, nVars);
  if (up.baseConflict)
    return res; // the formula itself is unsatisfiable at level zero

  // The solution table: every input pattern, propagated and completed. The
  // inputs are every io entry but the last, which is the result.
  vector<unsigned> inputBits;
  for (size_t s = 0; s + 1 < io.size(); s++)
    for (unsigned v : io[s])
      if (v != BCP_NOT_ENCODED)
        inputBits.push_back(v);
  if (inputBits.size() > 20)
    return res;

  Table t;
  t.nRows = 0;
  {
    // Built at the row cap's capacity, shrunk to fit afterwards: the sweeps
    // scan every column word per case, so a loose capacity is paid millions
    // of times.
    t.words = Table::MAX_ROWS / 64;
    t.colTrue.assign(nVars, vector<uint64_t>(t.words, 0));
    const uint64_t patterns = 1ull << inputBits.size();
    for (uint64_t p = 0; p < patterns; p++)
    {
      bool okPattern = true;
      for (size_t i = 0; i < inputBits.size() && okPattern; i++)
        okPattern = up.assign(inputBits[i], (p >> i) & 1);
      if (okPattern)
        okPattern = up.propagate(up.base);
      if (!okPattern)
        res.unsound++; // a concrete input the encoding refuses
      else if (!enumerate(up, t))
      {
        up.undoTo(up.base);
        return res; // hit the row cap; the check cannot be trusted
      }
      up.undoTo(up.base);
    }
    t.words = std::max((t.nRows + 63) / 64, 1u);
    for (vector<uint64_t>& col : t.colTrue)
      col.resize(t.words);
    t.full.assign(t.words, 0);
    for (unsigned r = 0; r < t.nRows; r++)
      t.full[r >> 6] |= 1ull << (r & 63);
  }
  if (t.nRows == 0)
    return res;

  // Scopes: the input/output bits, and every variable the CNF mentions.
  vector<unsigned> ioScope;
  {
    vector<bool> seen(nVars, false);
    for (const vector<unsigned>& sym : io)
      for (unsigned v : sym)
        if (v != BCP_NOT_ENCODED && !seen[v])
        {
          seen[v] = true;
          ioScope.push_back(v);
        }
  }
  vector<unsigned> allScope;
  {
    vector<bool> seen(nVars, false);
    for (unsigned v : ioScope)
      seen[v] = true;
    for (const vector<int>& cls : clauses)
      for (int lit : cls)
        seen[lit >> 1] = true;
    for (unsigned v = 1; v < nVars; v++)
      if (seen[v])
        allScope.push_back(v);
  }

  res.ran = true;
  res.width = width;
  res.clauses = (unsigned)clauses.size();
  for (const vector<int>& cls : clauses)
    res.literals += (unsigned)cls.size();
  res.variables = (unsigned)allScope.size();
  res.ioVars = (unsigned)ioScope.size();

  // The input/output sweep, always exhaustive: it is the definition of GAC
  // and URC, and a sample of it would grade nothing.
  if (pow3Capped((unsigned)ioScope.size(), cfg.consistencyCap) >
      cfg.consistencyCap)
  {
    res.ran = false;
    return res;
  }
  SweepCounts ioCounts;
  ioCounts.missedByUnset.assign(ioScope.size() + 1, 0);
  sweepExhaustive(up, t, ioScope, ioCounts);
  res.ioCases = ioCounts.cases;
  res.ioContradictory = ioCounts.contradictory;
  res.gacIncomplete = ioCounts.incomplete;
  res.gacDerivable = ioCounts.derivable;
  res.gacDerived = ioCounts.derived;
  res.urcMissed = ioCounts.missedConflict;
  res.urcMissedByUnset = ioCounts.missedByUnset;
  res.unsound += ioCounts.unsound;

  // The all-variables sweep, exhaustive when it fits.
  SweepCounts pcCounts;
  res.pcExhaustive =
      pow3Capped((unsigned)allScope.size(), cfg.consistencyCap) <=
      cfg.consistencyCap;
  if (res.pcExhaustive)
    sweepExhaustive(up, t, allScope, pcCounts);
  else
    sweepSampled(up, t, allScope, cfg.pcSamples, cfg.seed, pcCounts);
  res.pcRan = true;
  res.pcCases = pcCounts.cases;
  res.pcContradictory = pcCounts.contradictory;
  res.pcIncomplete = pcCounts.incomplete;
  res.pcDerivable = pcCounts.derivable;
  res.pcDerived = pcCounts.derived;
  res.pcMissedConflict = pcCounts.missedConflict;
  res.unsound += pcCounts.unsound;

  return res;
}

bool dumpEncoding(STPMgr* mgr, const OpSpec& op, const Config& cfg,
                  const string& path)
{
  const Layout l = layoutFor(op, cfg.dumpWidth, cfg.arity);
  if (!l.ok)
    return false;

  BcpEncoding* enc = makeBcpEncoding(mgr, op, l);
  if (enc == NULL)
    return false;

  vector<vector<int>> clauses;
  vector<vector<unsigned>> io;
  unsigned nVars = 0;
  const bool got = bcpMaterial(enc, clauses, io, nVars);
  destroyBcpEncoding(enc);
  if (!got)
    return false;

  std::ofstream f(path.c_str());
  if (!f)
    return false;

  f << "c op " << op.name << " width " << cfg.dumpWidth << " arity "
    << cfg.arity << " cnf " << (cfg.cnf.empty() ? "medium" : cfg.cnf) << "\n";
  for (size_t s = 0; s < io.size(); s++)
  {
    f << "c sym " << s << (s + 1 == io.size() ? " result" : " child");
    for (unsigned v : io[s])
      f << " " << (v == BCP_NOT_ENCODED ? 0u : v);
    f << "\n";
  }
  f << "p cnf " << (nVars > 0 ? nVars - 1 : 0) << " " << clauses.size()
    << "\n";
  for (const vector<int>& cls : clauses)
  {
    for (int lit : cls)
      f << ((lit & 1) ? "-" : "") << (lit >> 1) << " ";
    f << "0\n";
  }
  return true;
}

} // namespace propbench
