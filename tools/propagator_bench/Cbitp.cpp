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

// The constant-bit propagators: speed on random partially fixed cases,
// exhaustive precision against a brute-forced ideal at a small width, and a
// spot check against the SAT-based maxPrecision() at the benchmarked width.

#include "PropagatorBench.h"

#include "stp/Simplifier/constantBitP/ConstantBitP_MaxPrecision.h"

#include <chrono>
#include <cmath>
#include <iostream>

using namespace stp;
using namespace simplifier::constantBitP;

namespace propbench
{
namespace
{

typedef std::chrono::steady_clock Clock;

// One benchmark case: the seeded domains plus the concrete solution they
// were built from, which every sound propagator must keep admitting.
struct Case
{
  explicit Case(const Layout& l)
      : output(l.outWidth, l.outIsBoolean),
        witnessOut(l.outWidth, l.outIsBoolean)
  {
  }

  vector<FixedBits> children;
  FixedBits output;
  vector<FixedBits> witness;
  FixedBits witnessOut;
};

bool admits(const FixedBits& domain, const FixedBits& concrete)
{
  for (unsigned i = 0; i < domain.getWidth(); i++)
    if (domain.isFixed(i) && domain.getValue(i) != concrete.getValue(i))
      return false;
  return true;
}

bool admitsValue(const FixedBits& domain, uint64_t v)
{
  for (unsigned i = 0; i < domain.getWidth(); i++)
    if (domain.isFixed(i) && domain.getValue(i) != (((v >> i) & 1) != 0))
      return false;
  return true;
}

unsigned countFixed(const Case& c)
{
  unsigned total = c.output.countFixed();
  for (const FixedBits& f : c.children)
    total += f.countFixed();
  return total;
}

bool isShift(Kind k)
{
  return k == BVLEFTSHIFT || k == BVRIGHTSHIFT || k == BVSRSHIFT;
}

// ---------------------------------------------------------------------------
// Case generation. A concrete solution is drawn first and evaluated, then
// bits are unfixed, so the case is always satisfiable: propagators never
// short circuit on a conflict, which would make the timings meaningless.

vector<Case> makeCases(STPMgr* mgr, const OpSpec& op, const Layout& l,
                       Direction dir, unsigned prob, unsigned count,
                       std::mt19937& rand, bool shiftBias)
{
  vector<Case> cases;
  cases.reserve(count);

  for (unsigned i = 0; i < count; i++)
  {
    Case c(l);
    ASTVec concrete;
    for (unsigned j = 0; j < l.children.size(); j++)
    {
      const ChildSpec& spec = l.children[j];
      FixedBits bits(1, false);
      if (spec.isConstant)
        bits = concreteOf(spec, spec.value);
      else if (shiftBias && isShift(op.kind) && j == 1 && (rand() % 2))
        // Otherwise a random 64 bit shift amount is out of range almost
        // every time, and the propagator only ever sees the easy case.
        bits = concreteOf(spec, rand() % spec.width);
      else
        bits = randomConcrete(spec, rand);

      if (spec.isBoolean)
        concrete.push_back(bits.getValue(0) ? mgr->ASTTrue : mgr->ASTFalse);
      else
        concrete.push_back(mgr->CreateBVConst(bits.GetBVConst(), spec.width));

      c.witness.push_back(bits);
    }

    c.witnessOut = FixedBits::concreteToAbstract(evaluateNodes(mgr, op, l, concrete));

    // Seed the domains from the solution.
    for (unsigned j = 0; j < l.children.size(); j++)
    {
      FixedBits bits(c.witness[j]);
      if (!l.children[j].isConstant)
      {
        if (dir == Direction::TopDown)
          bits = FixedBits(bits.getWidth(), bits.isBoolean());
        else
          unfixTo(bits, prob, rand);
      }
      c.children.push_back(bits);
    }

    c.output = c.witnessOut;
    if (dir == Direction::BottomUp)
      c.output = FixedBits(l.outWidth, l.outIsBoolean);
    else
      unfixTo(c.output, prob, rand);

    cases.push_back(c);
  }
  return cases;
}

// ---------------------------------------------------------------------------
// Timing. The box this normally runs on is busy, so each configuration is
// timed several times and the median is reported.

Timing timeCases(STPMgr* mgr, const OpSpec& op, const vector<Case>& pristine,
                 const Config& cfg)
{
  Timing t;
  vector<double> nsPerCall;

  for (unsigned repeat = 0; repeat < cfg.repeats; repeat++)
  {
    vector<Case> work(pristine); // untimed: propagators mutate their inputs
    vector<Result> results(work.size(), NO_CHANGE);
    vector<FixedBits*> ptrs(work.empty() ? 0 : work[0].children.size());

    size_t done = 0;
    const auto start = Clock::now();
    for (size_t i = 0; i < work.size(); i++)
    {
      for (size_t j = 0; j < ptrs.size(); j++)
        ptrs[j] = &work[i].children[j];
      results[i] = cbitpTransfer(mgr, op.kind, ptrs, work[i].output);
      done++;
      if ((done & 63) == 0 &&
          std::chrono::duration<double>(Clock::now() - start).count() >
              cfg.budgetSeconds)
        break;
    }
    const double elapsed =
        std::chrono::duration<double>(Clock::now() - start).count();
    if (done == 0)
      continue;
    nsPerCall.push_back(1e9 * elapsed / done);

    if (repeat == 0)
    {
      t.calls = done;
      uint64_t before = 0, after = 0;
      for (size_t i = 0; i < done; i++)
      {
        before += countFixed(pristine[i]);
        if (results[i] == CONFLICT)
        {
          t.conflicts++; // shouldn't happen: every case is satisfiable
          after += countFixed(pristine[i]);
          continue;
        }
        after += countFixed(work[i]);

        // The solution the case was built from must survive.
        bool sound = admits(work[i].output, pristine[i].witnessOut);
        for (size_t j = 0; j < work[i].children.size(); j++)
          sound = sound && admits(work[i].children[j], pristine[i].witness[j]);
        if (!sound)
          t.unsound++;
      }
      t.bitsGained = double(after - before) / done;
    }
  }

  t.nsPerCall = median(nsPerCall);
  return t;
}

// ---------------------------------------------------------------------------
// Exhaustive precision at a small width.

FixedBits fromTernary(const ChildSpec& spec, uint64_t pattern)
{
  FixedBits bits(spec.width, spec.isBoolean);
  for (unsigned i = 0; i < spec.width; i++)
  {
    const unsigned t = pattern % 3;
    pattern /= 3;
    if (t != 2)
    {
      bits.setFixed(i, true);
      bits.setValue(i, t == 1);
    }
  }
  return bits;
}

uint64_t pow3(unsigned n)
{
  uint64_t r = 1;
  for (unsigned i = 0; i < n; i++)
    r *= 3;
  return r;
}

// The number of (pattern combination, brute force) steps a run would take.
double exhaustiveWork(const OpSpec& op, const Layout& l, Direction dir)
{
  double patterns = 1;
  if (dir != Direction::TopDown)
    for (unsigned i : l.varying())
      patterns *= double(pow3(l.children[i].width));
  if (dir != Direction::BottomUp)
    patterns *= double(pow3(l.outWidth));
  (void)op;
  return patterns * double(1ull << l.packedBits());
}

PrecisionResult exhaustive(STPMgr* mgr, const OpSpec& op, Direction dir,
                           const Config& cfg)
{
  PrecisionResult result;

  // Shrink the width until the run is affordable.
  unsigned width = cfg.precisionWidth;
  Layout l;
  while (width >= 1)
  {
    l = layoutFor(op, width, cfg.arity);
    if (l.ok && l.packedBits() <= 24 &&
        exhaustiveWork(op, l, dir) <= double(cfg.precisionCaseCap) * 64)
      break;
    width--;
  }
  if (!l.ok)
    return result;

  result.ran = true;
  result.width = width;

  const vector<unsigned> varying = l.varying();
  const vector<uint64_t> table = semanticsTable(mgr, op, l);
  const uint64_t packedCount = 1ull << l.packedBits();

  // Odometers over the ternary patterns of the children and the result.
  vector<uint64_t> childPatterns(varying.size(), 0);
  vector<uint64_t> childLimit(varying.size(), 1);
  for (size_t i = 0; i < varying.size(); i++)
    childLimit[i] = (dir == Direction::TopDown)
                        ? 1 // everything unfixed
                        : pow3(l.children[varying[i]].width);
  const uint64_t outLimit =
      (dir == Direction::BottomUp) ? 1 : pow3(l.outWidth);

  // Where each varying child sits in the packed value.
  vector<unsigned> shift(varying.size(), 0);
  {
    unsigned s = 0;
    for (size_t i = 0; i < varying.size(); i++)
    {
      shift[i] = s;
      s += l.children[varying[i]].width;
    }
  }

  vector<FixedBits> initial;
  for (const ChildSpec& spec : l.children)
    initial.push_back(FixedBits(spec.width, spec.isBoolean));

  bool done = false;
  while (!done)
  {
    // Build the children for this pattern combination.
    for (unsigned i = 0; i < l.children.size(); i++)
      if (l.children[i].isConstant)
        initial[i] = concreteOf(l.children[i], l.children[i].value);
    for (size_t i = 0; i < varying.size(); i++)
      initial[varying[i]] =
          fromTernary(l.children[varying[i]],
                      dir == Direction::TopDown ? pow3(l.children[varying[i]].width) - 1
                                                : childPatterns[i]);

    for (uint64_t outPattern = 0; outPattern < outLimit; outPattern++)
    {
      ChildSpec outSpec;
      outSpec.width = l.outWidth;
      outSpec.isBoolean = l.outIsBoolean;
      const FixedBits initialOut =
          (dir == Direction::BottomUp)
              ? FixedBits(l.outWidth, l.outIsBoolean)
              : fromTernary(outSpec, outPattern);

      result.cases++;

      // Brute force the join of every surviving solution.
      vector<uint64_t> seenZero(varying.size() + 1, 0);
      vector<uint64_t> seenOne(varying.size() + 1, 0);
      bool anySolution = false;
      for (uint64_t packed = 0; packed < packedCount; packed++)
      {
        bool ok = true;
        for (size_t i = 0; i < varying.size() && ok; i++)
        {
          const unsigned w = l.children[varying[i]].width;
          const uint64_t v = (packed >> shift[i]) & ((1ull << w) - 1);
          ok = admitsValue(initial[varying[i]], v);
        }
        if (!ok)
          continue;
        const uint64_t out = table[packed];
        if (!admitsValue(initialOut, out))
          continue;

        anySolution = true;
        for (size_t i = 0; i < varying.size(); i++)
        {
          const unsigned w = l.children[varying[i]].width;
          const uint64_t v = (packed >> shift[i]) & ((1ull << w) - 1);
          seenZero[i] |= ~v;
          seenOne[i] |= v;
        }
        seenZero[varying.size()] |= ~out;
        seenOne[varying.size()] |= out;
      }

      // Run the propagator.
      vector<FixedBits> children(initial);
      FixedBits output(initialOut);
      vector<FixedBits*> ptrs;
      for (FixedBits& f : children)
        ptrs.push_back(&f);
      const Result r = cbitpTransfer(mgr, op.kind, ptrs, output);

      if (!anySolution)
      {
        if (r == CONFLICT)
          result.precise++;
        else
          result.missedConflict++;
        continue;
      }

      if (r == CONFLICT)
      {
        result.unsound++;
        continue;
      }

      unsigned derivable = 0, gained = 0;
      bool unsound = false;
      for (size_t s = 0; s <= varying.size(); s++)
      {
        const bool isOut = (s == varying.size());
        const FixedBits& was = isOut ? initialOut : initial[varying[s]];
        const FixedBits& now = isOut ? output : children[varying[s]];
        for (unsigned i = 0; i < now.getWidth(); i++)
        {
          const bool zero = ((seenZero[s] >> i) & 1) != 0;
          const bool one = ((seenOne[s] >> i) & 1) != 0;
          if (now.isFixed(i) && !was.isFixed(i))
            gained++;
          if (zero != one) // every solution agrees on this bit
          {
            if (!was.isFixed(i))
              derivable++;
            if (now.isFixed(i) && now.getValue(i) != one)
              unsound = true;
          }
          else if (now.isFixed(i) && !was.isFixed(i))
            unsound = true; // a solution was thrown away
        }
      }

      if (unsound)
      {
        result.unsound++;
        continue;
      }
      result.derivable += derivable;
      result.gained += gained;
      if (gained == derivable)
        result.precise++;
    }

    // Step the children's odometer.
    done = true;
    for (size_t i = 0; i < varying.size(); i++)
    {
      if (++childPatterns[i] < childLimit[i])
      {
        done = false;
        break;
      }
      childPatterns[i] = 0;
    }
    if (varying.empty())
      done = true;
  }

  return result;
}

// ---------------------------------------------------------------------------
// Spot check against the SAT-based maximally precise propagator, at the
// width being benchmarked.

SatCheck satSpotCheck(STPMgr* mgr, const OpSpec& op, const vector<Case>& cases,
                      unsigned howMany, double budgetSeconds)
{
  SatCheck check;
  check.ran = true;
  const auto start = Clock::now();

  for (size_t i = 0; i < cases.size() && check.cases < howMany; i++)
  {
    if (std::chrono::duration<double>(Clock::now() - start).count() >
        budgetSeconds)
      break; // a wide multiplier can take minutes per case

    vector<FixedBits> got(cases[i].children);
    FixedBits gotOut(cases[i].output);
    vector<FixedBits*> ptrs;
    for (FixedBits& f : got)
      ptrs.push_back(&f);
    const Result r = cbitpTransfer(mgr, op.kind, ptrs, gotOut);

    vector<FixedBits> ideal(cases[i].children);
    FixedBits idealOut(cases[i].output);
    vector<FixedBits*> idealPtrs;
    for (FixedBits& f : ideal)
      idealPtrs.push_back(&f);
    const bool noSolution = maxPrecision(idealPtrs, idealOut, op.kind, mgr);

    check.cases++;
    if (noSolution)
    {
      // Can't happen: the cases are built from a solution.
      if (r != CONFLICT)
        check.unsound++;
      continue;
    }
    if (r == CONFLICT)
    {
      check.unsound++;
      continue;
    }

    bool equal = FixedBits::equals(gotOut, idealOut);
    bool tooStrong = gotOut.countFixed() > idealOut.countFixed();
    for (size_t j = 0; j < got.size(); j++)
    {
      equal = equal && FixedBits::equals(got[j], ideal[j]);
      tooStrong = tooStrong || got[j].countFixed() > ideal[j].countFixed();
    }
    if (tooStrong)
      check.unsound++;
    else if (equal)
      check.precise++;
  }
  return check;
}

// ---------------------------------------------------------------------------
// Comparison against unit propagation on the bit-blasted encoding, at the
// width being benchmarked.

// The varying children then the result, which is the order Bcp.cpp expects.
vector<const FixedBits*> bcpView(const Layout& l, const vector<FixedBits>& ch,
                                 const FixedBits& out)
{
  vector<const FixedBits*> v;
  for (unsigned i : l.varying())
    v.push_back(&ch[i]);
  v.push_back(&out);
  return v;
}

BcpCheck bcpCompare(STPMgr* mgr, const OpSpec& op, const Layout& l,
                    const vector<Case>& cases, unsigned howMany,
                    double budgetSeconds)
{
  BcpEncoding* enc = makeBcpEncoding(mgr, op, l);
  if (enc == NULL)
    return BcpCheck(); // not encodable; leave the row's check unrun

  BcpCheck check;
  check.ran = true;
  check.clauses = bcpClauses(enc);
  check.variables = bcpVariables(enc);
  uint64_t bcpGained = 0, cbitpGained = 0;
  const auto start = Clock::now();

  for (size_t i = 0; i < cases.size() && check.cases < howMany; i++)
  {
    if (std::chrono::duration<double>(Clock::now() - start).count() >
        budgetSeconds)
      break; // a fresh solver and a full CNF load per case is not cheap

    const vector<const FixedBits*> before =
        bcpView(l, cases[i].children, cases[i].output);
    const unsigned initial = bcpVisibleFixed(enc, before);

    // What boolean constraint propagation gets on its own. The sampled cases
    // are all built from a solution, so a refutation here would be a bug.
    unsigned afterBcp = 0;
    if (!bcpPropagate(enc, before, afterBcp))
      continue;

    // What the transfer function gets, counted over the same variables.
    vector<FixedBits> got(cases[i].children);
    FixedBits gotOut(cases[i].output);
    vector<FixedBits*> ptrs;
    for (FixedBits& f : got)
      ptrs.push_back(&f);
    if (cbitpTransfer(mgr, op.kind, ptrs, gotOut) == CONFLICT)
      continue; // can't happen: the cases are built from a solution
    const unsigned afterCbitp =
        bcpVisibleFixed(enc, bcpView(l, got, gotOut));

    check.cases++;
    bcpGained += (afterBcp > initial) ? afterBcp - initial : 0;
    cbitpGained += (afterCbitp > initial) ? afterCbitp - initial : 0;
  }

  if (check.cases > 0)
  {
    check.bcpBits = double(bcpGained) / check.cases;
    check.cbitpBits = double(cbitpGained) / check.cases;
  }

  destroyBcpEncoding(enc);
  return check;
}

// ---------------------------------------------------------------------------
// Exhaustive arc-consistency check of the bit-blasted encoding.
//
// Every combination of fixed/unfixed bits over the varying children and the
// result, contradictory ones included -- which is the half the sampled check
// above cannot reach, since its cases are all drawn from a solution. For each
// one the ideal is brute-forced from the operation's truth table, and unit
// propagation is asked to match it: derive every bit that follows, and refute
// the case outright when nothing follows because there is no solution.

BcpExhaustive bcpExhaustiveCheck(STPMgr* mgr, const OpSpec& op,
                                 const Config& cfg)
{
  BcpExhaustive res;

  const unsigned width = cfg.bcpExhaustiveWidth;
  const Layout l = layoutFor(op, width, cfg.arity);
  if (!l.ok || l.packedBits() > 24)
    return res;

  BcpEncoding* enc = makeBcpEncoding(mgr, op, l);
  if (enc == NULL)
    return res;

  res.ran = true;
  res.width = width;

  const vector<unsigned> varying = l.varying();
  const vector<uint64_t> table = semanticsTable(mgr, op, l);
  const uint64_t packedCount = 1ull << l.packedBits();

  // Where each varying child sits in the packed value.
  vector<unsigned> shift(varying.size(), 0);
  {
    unsigned s = 0;
    for (size_t i = 0; i < varying.size(); i++)
    {
      shift[i] = s;
      s += l.children[varying[i]].width;
    }
  }

  ChildSpec outSpec;
  outSpec.width = l.outWidth;
  outSpec.isBoolean = l.outIsBoolean;

  vector<FixedBits> children;
  for (const ChildSpec& spec : l.children)
    children.push_back(FixedBits(spec.width, spec.isBoolean));

  vector<uint64_t> childPatterns(varying.size(), 0);
  const uint64_t outLimit = pow3(l.outWidth);

  bool done = false;
  while (!done)
  {
    for (unsigned i = 0; i < l.children.size(); i++)
      if (l.children[i].isConstant)
        children[i] = concreteOf(l.children[i], l.children[i].value);
    for (size_t i = 0; i < varying.size(); i++)
      children[varying[i]] =
          fromTernary(l.children[varying[i]], childPatterns[i]);

    for (uint64_t outPattern = 0; outPattern < outLimit; outPattern++)
    {
      const FixedBits output = fromTernary(outSpec, outPattern);
      res.cases++;

      // The ideal: the join of every solution this case still admits.
      vector<FixedBits> ideal(children);
      FixedBits idealOut(output);
      bool anySolution = false;
      for (uint64_t packed = 0; packed < packedCount; packed++)
      {
        bool ok = true;
        for (size_t i = 0; i < varying.size() && ok; i++)
        {
          const unsigned w = l.children[varying[i]].width;
          ok = admitsValue(children[varying[i]],
                           (packed >> shift[i]) & ((1ull << w) - 1));
        }
        if (!ok || !admitsValue(output, table[packed]))
          continue;

        if (!anySolution)
        {
          for (size_t i = 0; i < varying.size(); i++)
          {
            const unsigned w = l.children[varying[i]].width;
            ideal[varying[i]] = concreteOf(l.children[varying[i]],
                                           (packed >> shift[i]) &
                                               ((1ull << w) - 1));
          }
          idealOut = concreteOf(outSpec, table[packed]);
          anySolution = true;
        }
        else
        {
          for (size_t i = 0; i < varying.size(); i++)
          {
            const unsigned w = l.children[varying[i]].width;
            ideal[varying[i]].join((packed >> shift[i]) &
                                   ((1ull << w) - 1));
          }
          idealOut.join(table[packed]);
        }
      }

      unsigned fixed = 0;
      const bool propagated =
          bcpPropagate(enc, bcpView(l, children, output), fixed);

      if (!anySolution)
      {
        res.contradictory++;
        if (propagated)
          res.missedConflict++;
        else
          res.complete++;
        continue;
      }

      if (!propagated)
      {
        res.unsound++; // refused a case that has a solution
        continue;
      }

      const unsigned initial =
          bcpVisibleFixed(enc, bcpView(l, children, output));
      const unsigned idealFixed = bcpVisibleFixed(enc, bcpView(l, ideal, idealOut));

      if (fixed > idealFixed)
        res.unsound++;
      else
      {
        res.derivable += idealFixed - initial;
        res.gained += fixed - initial;
        if (fixed == idealFixed)
          res.complete++;
        else
          res.incomplete++;
      }
    }

    done = true;
    for (size_t i = 0; i < varying.size(); i++)
    {
      if (++childPatterns[i] < pow3(l.children[varying[i]].width))
      {
        done = false;
        break;
      }
      childPatterns[i] = 0;
    }
    if (varying.empty())
      done = true;
  }

  destroyBcpEncoding(enc);
  return res;
}

} // namespace

// ---------------------------------------------------------------------------

void runCbitp(STPMgr* mgr, const Config& cfg, vector<Row>& out)
{
  for (const OpSpec& op : allOps())
  {
    if (!cfg.ops.empty() &&
        std::find(cfg.ops.begin(), cfg.ops.end(), string(op.name)) ==
            cfg.ops.end())
      continue;

    BcpExhaustive bcpEx;
    if (cfg.bcpExhaustiveWidth > 0)
    {
      if (cfg.verbose)
        std::cerr << "bcp arc-consistency " << op.name << std::endl;
      bcpEx = bcpExhaustiveCheck(mgr, op, cfg);
    }

    ConsistencyCheck cons;
    if (cfg.consistencyWidth > 0)
    {
      if (cfg.verbose)
        std::cerr << "encoding consistency " << op.name << std::endl;
      cons = consistencyCheck(mgr, op, cfg);
    }

    const bool isBoolean =
        op.shape == Shape::BoolNary || op.shape == Shape::BoolUnary;
    vector<unsigned> widths = isBoolean ? vector<unsigned>{1} : cfg.widths;

    for (Direction dir : cfg.directions)
    {
      PrecisionResult precision;
      if (cfg.precision)
      {
        if (cfg.verbose)
          std::cerr << "cbitp precision " << op.name << " " << name(dir)
                    << std::endl;
        precision = exhaustive(mgr, op, dir, cfg);
      }

      for (unsigned width : widths)
      {
        const Layout l = layoutFor(op, width, cfg.arity);
        if (!l.ok)
          continue;

        for (unsigned prob : cfg.probs)
        {
          if (cfg.verbose)
            std::cerr << "cbitp speed " << op.name << " " << name(dir) << " w="
                      << width << " p=" << prob << std::endl;

          std::mt19937 rand(cfg.seed);
          const vector<Case> cases =
              makeCases(mgr, op, l, dir, prob, cfg.iterations, rand,
                        cfg.shiftBias);
          const Timing t = timeCases(mgr, op, cases, cfg);

          Row row;
          row.domain = Domain::Cbitp;
          row.op = op.name;
          row.direction = dir;
          row.width = width;
          row.arity = (unsigned)l.children.size();
          row.prob = prob;
          row.input = std::to_string(prob) + "% fixed";
          row.nsPerCall = t.nsPerCall;
          row.opsPerSec = t.nsPerCall > 0 ? 1e9 / t.nsPerCall : 0;
          row.bitsGained = t.bitsGained;
          row.calls = t.calls;
          row.conflicts = t.conflicts;
          row.witnessUnsound = t.unsound;
          row.precision = precision;
          row.bcpExhaustive = bcpEx;
          row.consistency = cons;

          if (cfg.satCases > 0 && op.satCheckable)
          {
            if (cfg.verbose)
              std::cerr << "  sat check" << std::endl;
            row.sat =
                satSpotCheck(mgr, op, cases, cfg.satCases, cfg.satBudgetSeconds);
          }

          if (cfg.bcpCases > 0)
          {
            if (cfg.verbose)
              std::cerr << "  bcp check" << std::endl;
            row.bcp = bcpCompare(mgr, op, l, cases, cfg.bcpCases,
                                 cfg.bcpBudgetSeconds);
          }

          out.push_back(row);
        }
      }
    }
  }
}
} // namespace propbench
