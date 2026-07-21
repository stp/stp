/***********
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
**********************/

#include "stp/cpp_interface.h"
#include "stp/Parser/parser.h"
#include "stp/Simplifier/NodeDomainAnalysis.h"
#include "stp/Simplifier/UnsignedInterval.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/MersenneTwister.h"
#include <gtest/gtest.h>
#include <stdio.h>


  const std::string start_input = R"(
  (set-logic QF_BV)
  (set-info :smt-lib-version 2.0)
  (set-info :category "check")
  (set-info :status sat)

  (declare-fun v0 () (_ BitVec 20))
  (declare-fun v1 () (_ BitVec 20))
  (declare-fun v2 () (_ BitVec 20))
  (declare-fun v3 () (_ BitVec 20))
  (declare-fun v4 () (_ BitVec 20))

  (declare-fun x0 () (_ BitVec 1))

  (declare-fun a () Bool)
  (declare-fun b () Bool)
  (declare-fun c () Bool)

  (push 1)
  )";


struct Context
{
   stp::STPMgr mgr;
   SimplifyingNodeFactory snf;
   stp::Cpp_interface interface;
   stp::NodeDomainAnalysis domain;

   Context() :
   snf (*(mgr.hashingNodeFactory), mgr),
   interface(mgr, &snf),
   domain(&mgr)
   { 
    mgr.defaultNodeFactory = &snf;
    stp::GlobalParserBM = &mgr;
    stp::GlobalParserInterface = &interface;
   }
   
   void process(std::string input)
   {
      stp::SMT2ScanString((start_input + input).c_str());
      stp::SMT2Parse();
      // TODO assert it was parsed properly.
      smt2lex_destroy();
      ASTNode n = mgr.CreateNode(stp::AND, mgr.GetAsserts());
      domain.buildMap(n);
    }
};
 
// fixed bits are constant, internval is null
TEST(NodeDomainAnalysis_Test, 0)
{
  CONSTANTBV::BitVector_Boot(); // TODO hack. needs to be run once before the constructors start allocating constantbvs.
  Context c;

  const auto width = 10;
  stp::FixedBits a = stp::FixedBits::fromUnsignedInt(width,3);

  auto a_ptr = &a;
  stp::UnsignedInterval* b_ptr = nullptr;

  c.domain.harmonise(a_ptr, b_ptr);

  ASSERT_TRUE(a.isTotallyFixed());
  ASSERT_TRUE(b_ptr != nullptr && b_ptr->isConstant());
}

// fixed bits are null, internval is costant.
TEST(NodeDomainAnalysis_Test, 1)
{
  Context c;

  stp::FixedBits * a_ptr = nullptr;

  ASTNode constant = c.mgr.CreateBVConst("1",10, 10); // hold a reference otherwise garbage collected.
  stp::CBV cbv  = constant.GetBVConst();
  stp::UnsignedInterval* b_ptr = new stp::UnsignedInterval(CONSTANTBV::BitVector_Clone(cbv), CONSTANTBV::BitVector_Clone(cbv));

  c.domain.harmonise(a_ptr, b_ptr);

  ASSERT_TRUE(a_ptr != NULL && a_ptr->isTotallyFixed());
  ASSERT_TRUE(b_ptr->isConstant());
}


TEST(NodeDomainAnalysis_Test, 2)
{
  Context c;
  MTRand rand(10U);

  for (int i = 0; i < 100; i++)
  {
    stp::FixedBits a = stp::FixedBits::createRandom(i+1,  30, rand);
    stp::FixedBits start =a;                        

    auto a_ptr = new stp::FixedBits(a);
    stp::UnsignedInterval* b_ptr = nullptr;

    c.domain.harmonise(a_ptr, b_ptr);
    
    // The interval provides no information, so sould be the same.
    ASSERT_TRUE(stp::FixedBits::equals(start,a)); 

    // Min and max should be the same
    if (a_ptr != nullptr && b_ptr != nullptr)
    {
      ASSERT_EQ(CONSTANTBV::BitVector_Compare(b_ptr->minV, a_ptr->GetMinBVConst()),0);
      ASSERT_EQ(CONSTANTBV::BitVector_Compare(b_ptr->maxV, a_ptr->GetMaxBVConst()),0);
    }

    delete a_ptr;
    delete b_ptr;
  }
}


TEST(NodeDomainAnalysis_Test, 3)
{
  Context c;

  const auto width =2;

  stp::CBV min = CONSTANTBV::BitVector_Create(width, true);
  stp::CBV max = CONSTANTBV::BitVector_Create(width, true);
  stp::UnsignedInterval b(min,max);

  stp::FixedBits a = stp::FixedBits::fromUnsignedInt(width,3);

  auto a_ptr = &a;
  stp::UnsignedInterval* b_ptr = nullptr;

  c.domain.harmonise(a_ptr, b_ptr);

  ASSERT_EQ(a_ptr->isTotallyFixed(), true);
  ASSERT_EQ(b_ptr->isConstant(), true);
}

///// Idempotence of harmonise. Tightening should reach a fixpoint in a
///// single call, so a second call must leave both domains unchanged.

static void boot()
{
  static bool booted = false;
  if (!booted)
  {
    CONSTANTBV::BitVector_Boot();
    booted = true;
  }
}

static stp::CBV cbvFromUnsigned(unsigned width, unsigned v)
{
  assert(width <= 32);
  stp::CBV result = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width; i++)
    if ((v >> i) & 1)
      CONSTANTBV::BitVector_Bit_On(result, i);
  return result;
}

// Build a FixedBits from a base-3 encoding: digit 0 = unfixed,
// digit 1 = fixed to zero, digit 2 = fixed to one.
static stp::FixedBits bitsFromTernary(unsigned width, unsigned config)
{
  stp::FixedBits b(width, false);
  for (unsigned i = 0; i < width; i++)
  {
    const unsigned digit = config % 3;
    config /= 3;
    if (digit == 0)
      b.setFixed(i, false);
    else
    {
      b.setFixed(i, true);
      b.setValue(i, digit == 2);
    }
  }
  return b;
}

static bool bitsContain(const stp::FixedBits& b, unsigned v)
{
  for (unsigned i = 0; i < b.getWidth(); i++)
    if (b.isFixed(i) && b.getValue(i) != (((v >> i) & 1) != 0))
      return false;
  return true;
}

// Whether "v" is in the intersection of the two domains, where nullptr
// means the domain contains everything.
static bool contains(const stp::FixedBits* bits,
                     const stp::UnsignedInterval* interval, unsigned width,
                     unsigned v)
{
  if (bits != nullptr && !bitsContain(*bits, v))
    return false;
  if (interval != nullptr)
  {
    stp::CBV cbv = cbvFromUnsigned(width, v);
    const bool in = interval->in(cbv);
    CONSTANTBV::BitVector_Destroy(cbv);
    if (!in)
      return false;
  }
  return true;
}

static std::string describe(const stp::FixedBits* bits,
                            const stp::UnsignedInterval* interval)
{
  std::stringstream s;
  if (bits == nullptr)
    s << "bits: null";
  else
    s << "bits: " << *bits;
  s << ", interval: ";
  if (interval == nullptr)
    s << "null";
  else
  {
    unsigned char* min = CONSTANTBV::BitVector_to_Bin(interval->minV);
    unsigned char* max = CONSTANTBV::BitVector_to_Bin(interval->maxV);
    s << "[" << min << ", " << max << "]";
    free(min);
    free(max);
  }
  return s.str();
}

// harmonise, then harmonise again, and check the second call changed
// nothing. Deletes/replaces the domains via harmonise, so callers must
// delete what remains afterwards.
static void checkIdempotent(Context& c, stp::FixedBits*& bits,
                            stp::UnsignedInterval*& interval,
                            const std::string& input)
{
  c.domain.harmonise(bits, interval);

  // Snapshot the state after the first call.
  stp::FixedBits* bitsAfterFirst =
      (bits == nullptr) ? nullptr : new stp::FixedBits(*bits);
  stp::CBV minAfterFirst =
      (interval == nullptr) ? nullptr : CONSTANTBV::BitVector_Clone(interval->minV);
  stp::CBV maxAfterFirst =
      (interval == nullptr) ? nullptr : CONSTANTBV::BitVector_Clone(interval->maxV);
  const std::string afterFirst = describe(bits, interval);

  c.domain.harmonise(bits, interval);

  const std::string msg = "input: " + input + ", after first call: " +
                          afterFirst + ", after second call: " +
                          describe(bits, interval);

  ASSERT_EQ(bitsAfterFirst == nullptr, bits == nullptr) << msg;
  if (bits != nullptr)
    ASSERT_TRUE(stp::FixedBits::equals(*bitsAfterFirst, *bits)) << msg;

  ASSERT_EQ(minAfterFirst == nullptr, interval == nullptr) << msg;
  if (interval != nullptr)
  {
    ASSERT_EQ(0, CONSTANTBV::BitVector_Lexicompare(minAfterFirst, interval->minV)) << msg;
    ASSERT_EQ(0, CONSTANTBV::BitVector_Lexicompare(maxAfterFirst, interval->maxV)) << msg;
  }

  delete bitsAfterFirst;
  if (minAfterFirst != nullptr)
    CONSTANTBV::BitVector_Destroy(minAfterFirst);
  if (maxAfterFirst != nullptr)
    CONSTANTBV::BitVector_Destroy(maxAfterFirst);
}

// Every fixed-bits pattern crossed with every interval that shares at
// least one value with it. Checks that harmonise is idempotent and that
// it neither adds nor removes values from the intersection.
TEST(NodeDomainAnalysis_Test, harmonise_idempotent_exhaustive)
{
  boot();
  Context c;

  for (unsigned width = 1; width <= 5; width++)
  {
    unsigned configs = 1;
    for (unsigned i = 0; i < width; i++)
      configs *= 3;
    const unsigned values = 1u << width;

    for (unsigned config = 0; config < configs; config++)
    {
      const stp::FixedBits pattern = bitsFromTernary(width, config);

      for (unsigned lo = 0; lo < values; lo++)
        for (unsigned hi = lo; hi < values; hi++)
        {
          // harmonise requires the domains to intersect.
          bool shared = false;
          for (unsigned v = lo; v <= hi && !shared; v++)
            shared = bitsContain(pattern, v);
          if (!shared)
            continue;

          stp::FixedBits* bits = new stp::FixedBits(pattern);
          stp::UnsignedInterval* interval = new stp::UnsignedInterval(
              cbvFromUnsigned(width, lo), cbvFromUnsigned(width, hi));

          const std::string input = describe(bits, interval);

          std::vector<bool> memberBefore(values);
          for (unsigned v = 0; v < values; v++)
            memberBefore[v] = contains(bits, interval, width, v);

          checkIdempotent(c, bits, interval, input);
          if (::testing::Test::HasFatalFailure())
            return;

          // Tightening must preserve the intersection exactly.
          for (unsigned v = 0; v < values; v++)
            ASSERT_EQ(memberBefore[v], contains(bits, interval, width, v))
                << "value " << v << " input: " << input << ", output: "
                << describe(bits, interval);

          delete bits;
          delete interval;
        }
    }
  }
}

// Every fixed-bits pattern crossed with every interval that shares at
// least one value with it. Checks that harmonise tightens fully: the
// interval's bounds become the least and greatest shared values, and a
// bit ends up fixed exactly when every shared value agrees on it.
TEST(NodeDomainAnalysis_Test, harmonise_tightens_maximally_exhaustive)
{
  boot();
  Context c;

  for (unsigned width = 1; width <= 5; width++)
  {
    unsigned configs = 1;
    for (unsigned i = 0; i < width; i++)
      configs *= 3;
    const unsigned values = 1u << width;

    for (unsigned config = 0; config < configs; config++)
    {
      const stp::FixedBits pattern = bitsFromTernary(width, config);

      for (unsigned lo = 0; lo < values; lo++)
        for (unsigned hi = lo; hi < values; hi++)
        {
          // The shared values, and per bit whether they all agree.
          unsigned smallest = 0, largest = 0;
          bool any = false;
          std::vector<bool> agree(width), agreedValue(width);
          for (unsigned v = lo; v <= hi; v++)
          {
            if (!bitsContain(pattern, v))
              continue;
            if (!any)
            {
              smallest = v;
              for (unsigned i = 0; i < width; i++)
              {
                agree[i] = true;
                agreedValue[i] = ((v >> i) & 1) != 0;
              }
            }
            else
              for (unsigned i = 0; i < width; i++)
                if (agree[i] && agreedValue[i] != (((v >> i) & 1) != 0))
                  agree[i] = false;
            largest = v;
            any = true;
          }
          if (!any)
            continue; // harmonise requires the domains to intersect.

          stp::FixedBits* bits = new stp::FixedBits(pattern);
          stp::UnsignedInterval* interval = new stp::UnsignedInterval(
              cbvFromUnsigned(width, lo), cbvFromUnsigned(width, hi));

          const std::string input = describe(bits, interval);

          c.domain.harmonise(bits, interval);

          const std::string msg =
              "input: " + input + ", output: " + describe(bits, interval);

          ASSERT_NE(interval, nullptr) << msg;
          stp::CBV expectedMin = cbvFromUnsigned(width, smallest);
          stp::CBV expectedMax = cbvFromUnsigned(width, largest);
          ASSERT_EQ(
              0, CONSTANTBV::BitVector_Lexicompare(interval->minV, expectedMin))
              << msg;
          ASSERT_EQ(
              0, CONSTANTBV::BitVector_Lexicompare(interval->maxV, expectedMax))
              << msg;
          CONSTANTBV::BitVector_Destroy(expectedMin);
          CONSTANTBV::BitVector_Destroy(expectedMax);

          for (unsigned i = 0; i < width; i++)
          {
            const bool fixed = bits != nullptr && bits->isFixed(i);
            ASSERT_EQ(agree[i], fixed) << "bit " << i << " " << msg;
            if (fixed)
              ASSERT_EQ(agreedValue[i], bits->getValue(i))
                  << "bit " << i << " " << msg;
          }

          delete bits;
          delete interval;
        }
    }
  }
}

// Fixed bits with no interval: harmonise builds the interval, and must
// still be idempotent.
TEST(NodeDomainAnalysis_Test, harmonise_idempotent_bits_only)
{
  boot();
  Context c;

  for (unsigned width = 1; width <= 5; width++)
  {
    unsigned configs = 1;
    for (unsigned i = 0; i < width; i++)
      configs *= 3;
    const unsigned values = 1u << width;

    for (unsigned config = 0; config < configs; config++)
    {
      stp::FixedBits* bits = new stp::FixedBits(bitsFromTernary(width, config));
      stp::UnsignedInterval* interval = nullptr;

      const std::string input = describe(bits, interval);

      std::vector<bool> memberBefore(values);
      for (unsigned v = 0; v < values; v++)
        memberBefore[v] = contains(bits, interval, width, v);

      checkIdempotent(c, bits, interval, input);
      if (::testing::Test::HasFatalFailure())
        return;

      for (unsigned v = 0; v < values; v++)
        ASSERT_EQ(memberBefore[v], contains(bits, interval, width, v))
            << "value " << v << " input: " << input << ", output: "
            << describe(bits, interval);

      delete bits;
      delete interval;
    }
  }
}

// An interval with no fixed bits: harmonise builds the fixed bits, and
// must still be idempotent.
TEST(NodeDomainAnalysis_Test, harmonise_idempotent_interval_only)
{
  boot();
  Context c;

  for (unsigned width = 1; width <= 5; width++)
  {
    const unsigned values = 1u << width;

    for (unsigned lo = 0; lo < values; lo++)
      for (unsigned hi = lo; hi < values; hi++)
      {
        stp::FixedBits* bits = nullptr;
        stp::UnsignedInterval* interval = new stp::UnsignedInterval(
            cbvFromUnsigned(width, lo), cbvFromUnsigned(width, hi));

        const std::string input = describe(bits, interval);

        std::vector<bool> memberBefore(values);
        for (unsigned v = 0; v < values; v++)
          memberBefore[v] = contains(bits, interval, width, v);

        checkIdempotent(c, bits, interval, input);
        if (::testing::Test::HasFatalFailure())
          return;

        for (unsigned v = 0; v < values; v++)
          ASSERT_EQ(memberBefore[v], contains(bits, interval, width, v))
              << "value " << v << " input: " << input << ", output: "
              << describe(bits, interval);

        delete bits;
        delete interval;
      }
  }
}

// Checks harmonise produces the tightest possible domains: the interval
// exactly [min, max] of the shared values, and a bit fixed if and only
// if all the shared values agree on it.
TEST(NodeDomainAnalysis_Test, harmonise_perfectly_tight)
{
  boot();
  Context c;

  unsigned imperfect = 0;
  unsigned total = 0;
  std::string example;

  for (unsigned width = 1; width <= 5; width++)
  {
    unsigned configs = 1;
    for (unsigned i = 0; i < width; i++)
      configs *= 3;
    const unsigned values = 1u << width;

    for (unsigned config = 0; config < configs; config++)
    {
      const stp::FixedBits pattern = bitsFromTernary(width, config);

      for (unsigned lo = 0; lo < values; lo++)
        for (unsigned hi = lo; hi < values; hi++)
        {
          std::vector<unsigned> sharedValues;
          for (unsigned v = lo; v <= hi; v++)
            if (bitsContain(pattern, v))
              sharedValues.push_back(v);
          if (sharedValues.empty())
            continue;

          stp::FixedBits* bits = new stp::FixedBits(pattern);
          stp::UnsignedInterval* interval = new stp::UnsignedInterval(
              cbvFromUnsigned(width, lo), cbvFromUnsigned(width, hi));
          const std::string input = describe(bits, interval);

          c.domain.harmonise(bits, interval);
          total++;

          bool tight = true;

          // The tightest interval is [min,max] of the shared values.
          stp::CBV best = cbvFromUnsigned(width, sharedValues.front());
          if (CONSTANTBV::BitVector_Lexicompare(best, interval->minV) != 0)
            tight = false;
          CONSTANTBV::BitVector_Destroy(best);
          best = cbvFromUnsigned(width, sharedValues.back());
          if (CONSTANTBV::BitVector_Lexicompare(best, interval->maxV) != 0)
            tight = false;
          CONSTANTBV::BitVector_Destroy(best);

          // A bit should be fixed exactly when the shared values all
          // agree on it, and to the value they agree on.
          for (unsigned i = 0; i < width; i++)
          {
            bool agree = true;
            for (unsigned v : sharedValues)
              if (((v >> i) & 1) != ((sharedValues.front() >> i) & 1))
              {
                agree = false;
                break;
              }
            const bool isFixed = (bits != nullptr) && bits->isFixed(i);
            if (agree != isFixed)
              tight = false;
            else if (isFixed &&
                     bits->getValue(i) != (((sharedValues.front() >> i) & 1) != 0))
              tight = false;
          }

          if (!tight)
          {
            imperfect++;
            if (example.empty())
              example = "input: " + input + ", output: " + describe(bits, interval);
          }

          delete bits;
          delete interval;
        }
    }
  }

  ASSERT_EQ(0u, imperfect) << imperfect << " of " << total
                           << " harmonised domains are not optimally tight,"
                           << " e.g. " << example;
}

static stp::CBV randomCBV(unsigned width, MTRand& rand)
{
  stp::CBV result = CONSTANTBV::BitVector_Create(width, true);
  for (unsigned i = 0; i < width; i++)
    if (rand.randInt() & 1)
      CONSTANTBV::BitVector_Bit_On(result, i);
  return result;
}

// Random fixed bits and intervals at widths too big to enumerate.
TEST(NodeDomainAnalysis_Test, harmonise_idempotent_random)
{
  boot();
  Context c;
  MTRand rand(10U);

  const unsigned widths[] = {8, 20, 33, 64, 100};

  for (unsigned width : widths)
    for (unsigned iteration = 0; iteration < 500; iteration++)
    {
      stp::FixedBits* bits = new stp::FixedBits(
          stp::FixedBits::createRandom(width, rand.randInt() % 101, rand));

      // A random member of the fixed bits, so the interval built around
      // it is guaranteed to intersect them.
      stp::CBV member = CONSTANTBV::BitVector_Create(width, true);
      for (unsigned i = 0; i < width; i++)
      {
        const bool bit =
            bits->isFixed(i) ? bits->getValue(i) : ((rand.randInt() & 1) != 0);
        if (bit)
          CONSTANTBV::BitVector_Bit_On(member, i);
      }

      stp::UnsignedInterval* interval = nullptr;
      if (iteration % 4 != 0) // every 4th iteration leaves the interval null.
      {
        stp::CBV lo = randomCBV(width, rand);
        if (CONSTANTBV::BitVector_Lexicompare(lo, member) > 0)
          CONSTANTBV::BitVector_Copy(lo, member);
        stp::CBV hi = randomCBV(width, rand);
        if (CONSTANTBV::BitVector_Lexicompare(hi, member) < 0)
          CONSTANTBV::BitVector_Copy(hi, member);
        interval = new stp::UnsignedInterval(lo, hi);
      }
      CONSTANTBV::BitVector_Destroy(member);

      const std::string input = describe(bits, interval);
      checkIdempotent(c, bits, interval, input);
      if (::testing::Test::HasFatalFailure())
        return;

      delete bits;
      delete interval;
    }
}

