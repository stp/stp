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

// The two value-analysis domains: unsigned intervals and value sets. Both
// only ever run bottom up -- they compute a node's domain from its
// children's -- so there is nothing to seed at the result.

#include "PropagatorBench.h"

#include "stp/Simplifier/UnsignedIntervalAnalysis.h"
#include "stp/Simplifier/ValueSetAnalysis.h"

#include <algorithm>
#include <chrono>
#include <iostream>

using namespace stp;

namespace propbench
{
namespace
{

typedef std::chrono::steady_clock Clock;

CBV cbvOf(unsigned width, uint64_t value)
{
  CBV v = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width && i < 64; i++)
    if ((value >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(v, i);
  return v;
}

uint64_t u64Of(CBV v, unsigned width)
{
  uint64_t r = 0;
  for (unsigned i = 0; i < width && i < 64; i++)
    if (CONSTANTBV::BitVector_bit_test(v, i))
      r |= (1ull << i);
  return r;
}

// ---------------------------------------------------------------------------
// Unsigned intervals.

UnsignedInterval* intervalOf(unsigned width, uint64_t lo, uint64_t hi)
{
  return new UnsignedInterval(cbvOf(width, lo), cbvOf(width, hi));
}

// The tightest interval holding everything the fixed bits admit. This is how
// NodeDomainAnalysis moves between the two domains, and it keeps the
// "50% fixed" input of the interval tables comparable with cbitp's.
UnsignedInterval* intervalOf(const FixedBits& bits)
{
  const unsigned width = bits.getWidth();
  CBV min = CONSTANTBV::BitVector_Create(width, true);
  CBV max = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width; i++)
  {
    if (bits.isFixed(i))
    {
      if (bits.getValue(i))
      {
        CONSTANTBV::BitVector_Bit_On(min, i);
        CONSTANTBV::BitVector_Bit_On(max, i);
      }
    }
    else
      CONSTANTBV::BitVector_Bit_On(max, i);
  }
  return new UnsignedInterval(min, max);
}

// How much of the value is pinned down, in bits: the width less the number
// of bits needed to count the interval's members. Zero for a complete
// interval, the full width for a constant.
double knownBits(const UnsignedInterval* iv, unsigned width)
{
  if (iv == NULL)
    return 0;
  CBV diff = CONSTANTBV::BitVector_Create(width, true);
  bool carry = false;
  CONSTANTBV::BitVector_sub(diff, iv->maxV, iv->minV, &carry);
  int highest = -1;
  for (int i = (int)width - 1; i >= 0; i--)
    if (CONSTANTBV::BitVector_bit_test(diff, i))
    {
      highest = i;
      break;
    }
  CONSTANTBV::BitVector_Destroy(diff);
  return width - (highest + 1);
}

// ---------------------------------------------------------------------------
// Value sets.

ValueSet* valueSetOf(unsigned width, bool isBoolean,
                     const vector<uint64_t>& values)
{
  ValueSet* set = new ValueSet(width, isBoolean);
  for (uint64_t v : values)
    if (!set->insert(cbvOf(width, v)))
    {
      delete set;
      return NULL; // more members than the domain can hold
    }
  return set;
}

double knownBits(const ValueSet* set, unsigned width)
{
  if (set == NULL || set->size() == 0)
    return 0;
  double bits = 0;
  while ((1u << (unsigned)bits) < set->size())
    bits++;
  return width - bits;
}

// The subset of {0, ..., 2^width - 1} a mask stands for.
vector<uint64_t> membersOf(uint32_t mask)
{
  vector<uint64_t> members;
  for (unsigned i = 0; i < 32; i++)
    if ((mask >> i) & 1)
      members.push_back(i);
  return members;
}

uint32_t maskOf(const ValueSet* set, unsigned width)
{
  if (set == NULL)
    return (width >= 5) ? 0xffffffffu : ((1u << (1u << width)) - 1);
  uint32_t mask = 0;
  for (CBV v : set->values)
    mask |= (1u << u64Of(v, width));
  return mask;
}

// ---------------------------------------------------------------------------
// Shared: enumerate every combination of per-child input domains.

// An odometer over `limits`. Returns false when it wraps.
bool step(vector<uint64_t>& odometer, const vector<uint64_t>& limits)
{
  for (size_t i = 0; i < odometer.size(); i++)
  {
    if (++odometer[i] < limits[i])
      return true;
    odometer[i] = 0;
  }
  return false;
}

vector<unsigned> shiftsOf(const Layout& l, const vector<unsigned>& varying)
{
  vector<unsigned> shift(varying.size(), 0);
  unsigned s = 0;
  for (size_t i = 0; i < varying.size(); i++)
  {
    shift[i] = s;
    s += l.children[varying[i]].width;
  }
  return shift;
}

// ---------------------------------------------------------------------------
// Interval precision: exhaustively, at a small width, against the hull of
// every value the operation can actually take.

PrecisionResult intervalPrecision(STPMgr* mgr, const OpSpec& op,
                                  const Config& cfg)
{
  PrecisionResult result;

  unsigned width = cfg.precisionWidth;
  Layout l;
  while (width >= 1)
  {
    l = layoutFor(op, width, cfg.arity);
    if (l.ok && l.packedBits() <= 20)
    {
      double work = 1;
      for (unsigned i : l.varying())
      {
        const uint64_t n = 1ull << l.children[i].width;
        work *= double(n * (n + 1) / 2);
      }
      work *= double(1ull << l.packedBits());
      if (work <= double(cfg.precisionCaseCap) * 64)
        break;
    }
    width--;
  }
  if (!l.ok)
    return result;

  result.ran = true;
  result.width = width;

  UnsignedIntervalAnalysis analysis;
  const ASTNode node = buildNode(mgr, op, l);
  const vector<uint64_t> table = semanticsTable(mgr, op, l);
  const vector<unsigned> varying = l.varying();
  const vector<unsigned> shift = shiftsOf(l, varying);
  const uint64_t packedCount = 1ull << l.packedBits();

  // Every (low, high) pair, per varying child.
  vector<vector<std::pair<uint64_t, uint64_t>>> options(varying.size());
  vector<uint64_t> limits(varying.size(), 0);
  for (size_t i = 0; i < varying.size(); i++)
  {
    const uint64_t n = 1ull << l.children[varying[i]].width;
    for (uint64_t lo = 0; lo < n; lo++)
      for (uint64_t hi = lo; hi < n; hi++)
        options[i].push_back({lo, hi});
    limits[i] = options[i].size();
  }

  vector<uint64_t> odometer(varying.size(), 0);
  const uint64_t outMask =
      (l.outWidth >= 64) ? ~0ull : ((1ull << l.outWidth) - 1);

  do
  {
    // The children, in the order the transfer function expects.
    vector<UnsignedInterval*> owned(l.children.size(), NULL);
    vector<const UnsignedInterval*> children(l.children.size(), NULL);
    for (unsigned j = 0; j < l.children.size(); j++)
      if (l.children[j].isConstant)
      {
        owned[j] = intervalOf(l.children[j].width, l.children[j].value,
                              l.children[j].value);
        children[j] = owned[j];
      }
    for (size_t i = 0; i < varying.size(); i++)
    {
      const auto& bounds = options[i][odometer[i]];
      const unsigned w = l.children[varying[i]].width;
      // A complete interval carries no information; the analysis passes a
      // null pointer for those, and some transfer functions check for it.
      if (bounds.first == 0 && bounds.second == (1ull << w) - 1)
        continue;
      owned[varying[i]] = intervalOf(w, bounds.first, bounds.second);
      children[varying[i]] = owned[varying[i]];
    }

    // The hull of everything the operation attains.
    uint64_t idealLo = outMask, idealHi = 0;
    bool any = false;
    for (uint64_t packed = 0; packed < packedCount; packed++)
    {
      bool ok = true;
      for (size_t i = 0; i < varying.size() && ok; i++)
      {
        const unsigned w = l.children[varying[i]].width;
        const uint64_t v = (packed >> shift[i]) & ((1ull << w) - 1);
        ok = v >= options[i][odometer[i]].first &&
             v <= options[i][odometer[i]].second;
      }
      if (!ok)
        continue;
      const uint64_t out = table[packed];
      idealLo = std::min(idealLo, out);
      idealHi = std::max(idealHi, out);
      any = true;
    }

    if (any)
    {
      result.cases++;
      UnsignedInterval* got = analysis.dispatchToTransferFunctions(node, children);
      const uint64_t gotLo = got ? u64Of(got->minV, l.outWidth) : 0;
      const uint64_t gotHi = got ? u64Of(got->maxV, l.outWidth) : outMask;

      if (gotLo > idealLo || gotHi < idealHi)
        result.unsound++;
      else
      {
        if (gotLo == idealLo && gotHi == idealHi)
          result.precise++;
        UnsignedInterval ideal(cbvOf(l.outWidth, idealLo),
                               cbvOf(l.outWidth, idealHi));
        result.derivable += (uint64_t)knownBits(&ideal, l.outWidth);
        result.gained += (uint64_t)knownBits(got, l.outWidth);
      }
      delete got;
    }

    for (UnsignedInterval* iv : owned)
      delete iv;
  } while (step(odometer, limits) && !varying.empty());

  return result;
}

// ---------------------------------------------------------------------------
// Value set precision: exhaustively over every subset, at a small width.

PrecisionResult valueSetPrecision(STPMgr* mgr, const OpSpec& op,
                                  const Config& cfg)
{
  PrecisionResult result;

  unsigned width = std::min(cfg.precisionWidth, 4u);
  Layout l;
  while (width >= 1)
  {
    l = layoutFor(op, width, cfg.arity);
    if (l.ok && l.packedBits() <= 20)
    {
      double work = 1;
      for (unsigned i : l.varying())
        work *= double(1ull << (1ull << l.children[i].width));
      work *= double(1ull << l.packedBits());
      if (work <= double(cfg.precisionCaseCap) * 64)
        break;
    }
    width--;
  }
  if (!l.ok)
    return result;

  result.ran = true;
  result.width = width;

  ValueSetAnalysis analysis(*mgr);
  const ASTNode node = buildNode(mgr, op, l);
  const vector<uint64_t> table = semanticsTable(mgr, op, l);
  const vector<unsigned> varying = l.varying();
  const vector<unsigned> shift = shiftsOf(l, varying);
  const uint64_t packedCount = 1ull << l.packedBits();

  // Every non-empty subset, plus "nothing is known" -- which the analysis
  // represents with a null pointer, and which a symbol always has.
  vector<uint64_t> limits(varying.size(), 0);
  for (size_t i = 0; i < varying.size(); i++)
    limits[i] = 1ull << (1ull << l.children[varying[i]].width);

  vector<uint64_t> odometer(varying.size(), 0);

  do
  {
    vector<ValueSet*> owned(l.children.size(), NULL);
    vector<const ValueSet*> children(l.children.size(), NULL);
    vector<uint32_t> masks(varying.size(), 0);
    bool buildable = true;

    for (unsigned j = 0; j < l.children.size(); j++)
      if (l.children[j].isConstant)
      {
        owned[j] = valueSetOf(l.children[j].width, false,
                              {l.children[j].value});
        children[j] = owned[j];
      }

    for (size_t i = 0; i < varying.size() && buildable; i++)
    {
      const ChildSpec& spec = l.children[varying[i]];
      const bool unknown = (odometer[i] == limits[i] - 1);
      masks[i] = unknown ? (uint32_t)(limits[i] - 1)
                         : (uint32_t)(odometer[i] + 1);
      if (unknown)
        continue; // leave the child null

      owned[varying[i]] =
          valueSetOf(spec.width, spec.isBoolean, membersOf(masks[i]));
      if (owned[varying[i]] == NULL)
        buildable = false; // more members than the domain holds
      children[varying[i]] = owned[varying[i]];
    }

    if (buildable)
    {
      // Exactly the values the operation attains.
      uint32_t idealMask = 0;
      for (uint64_t packed = 0; packed < packedCount; packed++)
      {
        bool ok = true;
        for (size_t i = 0; i < varying.size() && ok; i++)
        {
          const unsigned w = l.children[varying[i]].width;
          const uint64_t v = (packed >> shift[i]) & ((1ull << w) - 1);
          ok = (masks[i] >> v) & 1;
        }
        if (ok)
          idealMask |= (1u << table[packed]);
      }

      result.cases++;
      ValueSet* got = analysis.dispatchToTransferFunctions(node, children);
      const uint32_t gotMask = maskOf(got, l.outWidth);

      if ((gotMask | idealMask) != gotMask)
        result.unsound++; // a value the operation attains isn't in the set
      else
      {
        if (gotMask == idealMask)
          result.precise++;
        vector<uint64_t> idealMembers = membersOf(idealMask);
        ValueSet* ideal =
            valueSetOf(l.outWidth, l.outIsBoolean, idealMembers);
        result.derivable += (uint64_t)knownBits(ideal, l.outWidth);
        result.gained += (uint64_t)knownBits(got, l.outWidth);
        delete ideal;
      }
      delete got;
    }

    for (ValueSet* set : owned)
      delete set;
  } while (step(odometer, limits) && !varying.empty());

  return result;
}

} // namespace

// ---------------------------------------------------------------------------

void runInterval(STPMgr* mgr, const Config& cfg, vector<Row>& out)
{
  UnsignedIntervalAnalysis analysis;

  for (const OpSpec& op : allOps())
  {
    if (!cfg.ops.empty() &&
        std::find(cfg.ops.begin(), cfg.ops.end(), string(op.name)) ==
            cfg.ops.end())
      continue;
    if (!supports(Domain::Interval, op))
      continue;

    PrecisionResult precision;
    if (cfg.precision)
    {
      if (cfg.verbose)
        std::cerr << "interval precision " << op.name << std::endl;
      precision = intervalPrecision(mgr, op, cfg);
    }

    const bool isBoolean =
        op.shape == Shape::BoolNary || op.shape == Shape::BoolUnary;
    const vector<unsigned> widths = isBoolean ? vector<unsigned>{1} : cfg.widths;

    for (unsigned width : widths)
    {
      const Layout l = layoutFor(op, width, cfg.arity);
      if (!l.ok)
        continue;
      const ASTNode node = buildNode(mgr, op, l);

      for (unsigned prob : cfg.probs)
      {
        if (cfg.verbose)
          std::cerr << "interval speed " << op.name << " w=" << width
                    << " p=" << prob << std::endl;

        std::mt19937 rand(cfg.seed);
        // Inputs are read-only, so one set is reused by every repeat.
        vector<vector<UnsignedInterval*>> owned(cfg.iterations);
        vector<vector<const UnsignedInterval*>> cases(cfg.iterations);
        for (unsigned i = 0; i < cfg.iterations; i++)
        {
          for (unsigned j = 0; j < l.children.size(); j++)
          {
            const ChildSpec& spec = l.children[j];
            UnsignedInterval* iv;
            if (spec.isConstant)
              iv = intervalOf(spec.width, spec.value, spec.value);
            else
            {
              FixedBits bits = randomConcrete(spec, rand);
              unfixTo(bits, prob, rand);
              iv = intervalOf(bits);
            }
            owned[i].push_back(iv);
            cases[i].push_back(iv->isComplete() ? NULL : iv);
          }
        }

        vector<double> nsPerCall;
        vector<UnsignedInterval*> results(cfg.iterations, NULL);
        double gained = 0;
        uint64_t calls = 0;
        for (unsigned repeat = 0; repeat < cfg.repeats; repeat++)
        {
          size_t done = 0;
          const auto start = Clock::now();
          for (unsigned i = 0; i < cfg.iterations; i++)
          {
            results[i] = analysis.dispatchToTransferFunctions(node, cases[i]);
            done++;
            if ((done & 63) == 0 &&
                std::chrono::duration<double>(Clock::now() - start).count() >
                    cfg.budgetSeconds)
              break;
          }
          const double elapsed =
              std::chrono::duration<double>(Clock::now() - start).count();
          if (done > 0)
            nsPerCall.push_back(1e9 * elapsed / done);

          if (repeat == 0)
          {
            calls = done;
            for (size_t i = 0; i < done; i++)
              gained += knownBits(results[i], l.outWidth);
          }
          for (size_t i = 0; i < done; i++)
          {
            delete results[i];
            results[i] = NULL;
          }
        }

        Row row;
        row.domain = Domain::Interval;
        row.op = op.name;
        row.direction = Direction::BottomUp;
        row.width = width;
        row.arity = (unsigned)l.children.size();
        row.prob = prob;
        row.input = std::to_string(prob) + "% fixed";
        row.nsPerCall = median(nsPerCall);
        row.opsPerSec = row.nsPerCall > 0 ? 1e9 / row.nsPerCall : 0;
        row.bitsGained = calls ? gained / calls : 0;
        row.calls = calls;
        row.precision = precision;
        out.push_back(row);

        for (auto& v : owned)
          for (UnsignedInterval* iv : v)
            delete iv;
      }
    }
  }
}

void runValueSet(STPMgr* mgr, const Config& cfg, vector<Row>& out)
{
  ValueSetAnalysis analysis(*mgr);

  for (const OpSpec& op : allOps())
  {
    if (!cfg.ops.empty() &&
        std::find(cfg.ops.begin(), cfg.ops.end(), string(op.name)) ==
            cfg.ops.end())
      continue;
    if (!supports(Domain::ValueSet, op))
      continue;

    PrecisionResult precision;
    if (cfg.precision)
    {
      if (cfg.verbose)
        std::cerr << "valueset precision " << op.name << std::endl;
      precision = valueSetPrecision(mgr, op, cfg);
    }

    const bool isBoolean =
        op.shape == Shape::BoolNary || op.shape == Shape::BoolUnary;
    const vector<unsigned> widths = isBoolean ? vector<unsigned>{1} : cfg.widths;

    for (unsigned width : widths)
    {
      const Layout l = layoutFor(op, width, cfg.arity);
      if (!l.ok)
        continue;
      const ASTNode node = buildNode(mgr, op, l);

      for (unsigned setSize : cfg.setSizes)
      {
        if (cfg.verbose)
          std::cerr << "valueset speed " << op.name << " w=" << width
                    << " n=" << setSize << std::endl;

        std::mt19937 rand(cfg.seed);
        vector<vector<ValueSet*>> owned(cfg.iterations);
        vector<vector<const ValueSet*>> cases(cfg.iterations);
        bool buildable = true;
        for (unsigned i = 0; i < cfg.iterations && buildable; i++)
        {
          for (unsigned j = 0; j < l.children.size(); j++)
          {
            const ChildSpec& spec = l.children[j];
            vector<uint64_t> values;
            if (spec.isConstant)
              values.push_back(spec.value);
            else
            {
              // Distinct values, so a row labelled "4 values" really is
              // four. Small widths can run out; the set is then smaller.
              const uint64_t limit =
                  spec.width >= 64 ? ~0ull : (1ull << spec.width);
              for (unsigned k = 0, tries = 0;
                   k < setSize && tries < 20 * setSize; tries++)
              {
                const uint64_t v =
                    (((uint64_t)rand() << 32) | rand()) %
                    limit;
                if (std::find(values.begin(), values.end(), v) == values.end())
                {
                  values.push_back(v);
                  k++;
                }
              }
            }
            ValueSet* set = valueSetOf(spec.width, spec.isBoolean, values);
            if (set == NULL)
            {
              buildable = false; // asked for more values than fit
              break;
            }
            // Passed as-is even when the set turns out to be every value of
            // the width: a null child would measure the early bail-out
            // instead of the transfer function.
            owned[i].push_back(set);
            cases[i].push_back(set);
          }
        }

        if (buildable)
        {
          vector<double> nsPerCall;
          vector<ValueSet*> results(cfg.iterations, NULL);
          double gained = 0;
          uint64_t calls = 0;
          for (unsigned repeat = 0; repeat < cfg.repeats; repeat++)
          {
            size_t done = 0;
            const auto start = Clock::now();
            for (unsigned i = 0; i < cfg.iterations; i++)
            {
              results[i] = analysis.dispatchToTransferFunctions(node, cases[i]);
              done++;
              if ((done & 63) == 0 &&
                  std::chrono::duration<double>(Clock::now() - start).count() >
                      cfg.budgetSeconds)
                break;
            }
            const double elapsed =
                std::chrono::duration<double>(Clock::now() - start).count();
            if (done > 0)
              nsPerCall.push_back(1e9 * elapsed / done);

            if (repeat == 0)
            {
              calls = done;
              for (size_t i = 0; i < done; i++)
                gained += knownBits(results[i], l.outWidth);
            }
            for (size_t i = 0; i < done; i++)
            {
              delete results[i];
              results[i] = NULL;
            }
          }

          Row row;
          row.domain = Domain::ValueSet;
          row.op = op.name;
          row.direction = Direction::BottomUp;
          row.width = width;
          row.arity = (unsigned)l.children.size();
          row.setSize = setSize;
          row.input = std::to_string(setSize) + " values";
          row.nsPerCall = median(nsPerCall);
          row.opsPerSec = row.nsPerCall > 0 ? 1e9 / row.nsPerCall : 0;
          row.bitsGained = calls ? gained / calls : 0;
          row.calls = calls;
          row.precision = precision;
          out.push_back(row);
        }

        for (auto& v : owned)
          for (ValueSet* set : v)
            delete set;
      }
    }
  }
}
} // namespace propbench
