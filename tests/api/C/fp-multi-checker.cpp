#include <gtest/gtest.h>
#include <stp/c_interface.h>
#include <stp/STPManager/STPManager.h> // for the checker-reuse test
#include <stp/FloatBlaster/symbolic_fp.h>
#include <stp/NodeFactory/SimplifyingNodeFactory.h>
#include <cstdint>
#include <cstdlib>
#include <condition_variable>
#include <memory>
#include <mutex>
#include <thread>

// Two independent validity checkers, both using floating point, interleaved.
// This used to corrupt the second checker: floating-point blasting bound a
// process-global symfpu backend to the first checker to use it. Each checker
// now blasts into its own manager, so both give correct results.
TEST(fp_multi_checker, two_live_checkers)
{
  VC v1 = vc_createValidityChecker();
  VC v2 = vc_createValidityChecker();

  // v1: a is 2.0 (half); a*a is 4.0.
  Expr a = vc_varExpr(v1, "a", vc_fpType(v1, 5, 11));
  vc_assertFormula(
      v1, vc_fpEqExpr(v1, a,
                      vc_fpConstFromBits(v1, 5, 11,
                                         vc_bvConstExprFromLL(v1, 16, 0x4000))));
  Expr prod = vc_fpMulExpr(v1, vc_fpRoundingMode(v1, VC_RM_RNE), a, a);

  // v2: b is 3.0 (double).
  Expr b = vc_varExpr(v2, "b", vc_fpType(v2, 11, 53));
  vc_assertFormula(
      v2, vc_fpEqExpr(v2, b,
                      vc_fpConstFromBits(
                          v2, 11, 53,
                          vc_bvConstExprFromLL(v2, 64, 0x4008000000000000ULL))));

  ASSERT_EQ(0, vc_query(v1, vc_falseExpr(v1)));
  ASSERT_EQ(0, vc_query(v2, vc_falseExpr(v2)));

  // Read from both, interleaved.
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(v1, a)));
  EXPECT_EQ((unsigned long long)0x4008000000000000ULL,
            getBVUnsignedLongLong(vc_getCounterExample(v2, b)));
  EXPECT_EQ((unsigned long long)0x4400, // 2.0 * 2.0 = 4.0
            getBVUnsignedLongLong(vc_getCounterExample(v1, prod)));
  EXPECT_EQ((unsigned long long)0x4000, // v1 still intact after reading v2
            getBVUnsignedLongLong(vc_getCounterExample(v1, a)));

  vc_Destroy(v1);
  vc_Destroy(v2);
}

// The symfpu traits API has no context parameter, so STP binds its backend to
// a manager through symbolic_fp::init.  The binding must be per-thread: with a
// process-global binding, the deliberately ordered init(v2) below redirects
// the first thread's subsequent backend operation into v2's manager.
TEST(fp_multi_checker, concurrent_backend_contexts_are_thread_local)
{
  struct Coordination
  {
    std::mutex mutex;
    std::condition_variable changed;
    bool first_initialised = false;
    bool second_initialised = false;
    bool first_checked = false;
  } coordination;

  bool first_uses_own_manager = false;
  bool second_uses_own_manager = false;

  stp::STPMgr first_bm;
  std::unique_ptr<SimplifyingNodeFactory> first_nf(
      new SimplifyingNodeFactory(*first_bm.hashingNodeFactory, first_bm));
  first_bm.defaultNodeFactory = first_nf.get();

  stp::STPMgr second_bm;
  std::unique_ptr<SimplifyingNodeFactory> second_nf(
      new SimplifyingNodeFactory(*second_bm.hashingNodeFactory, second_bm));
  second_bm.defaultNodeFactory = second_nf.get();

  const stp::ASTNode first_lhs =
      first_bm.CreateSymbol("first_rm_lhs", 0, 5);
  const stp::ASTNode first_rhs =
      first_bm.CreateSymbol("first_rm_rhs", 0, 5);
  const stp::ASTNode first_expected =
      first_bm.CreateNode(stp::EQ, first_lhs, first_rhs);

  const stp::ASTNode second_lhs =
      second_bm.CreateSymbol("second_rm_lhs", 0, 5);
  const stp::ASTNode second_rhs =
      second_bm.CreateSymbol("second_rm_rhs", 0, 5);
  const stp::ASTNode second_expected =
      second_bm.CreateNode(stp::EQ, second_lhs, second_rhs);

  std::thread first([&]() {
    stp::symbolic_fp::init(&first_bm);
    {
      std::lock_guard<std::mutex> lock(coordination.mutex);
      coordination.first_initialised = true;
    }
    coordination.changed.notify_all();

    {
      std::unique_lock<std::mutex> lock(coordination.mutex);
      coordination.changed.wait(
          lock, [&]() { return coordination.second_initialised; });
    }

    const stp::ASTNode n =
        stp::symbolic_fp::roundingMode(first_lhs) ==
        stp::symbolic_fp::roundingMode(first_rhs);
    first_uses_own_manager = n == first_expected;

    {
      std::lock_guard<std::mutex> lock(coordination.mutex);
      coordination.first_checked = true;
    }
    coordination.changed.notify_all();
  });

  std::thread second([&]() {
    {
      std::unique_lock<std::mutex> lock(coordination.mutex);
      coordination.changed.wait(
          lock, [&]() { return coordination.first_initialised; });
    }

    stp::symbolic_fp::init(&second_bm);
    {
      std::lock_guard<std::mutex> lock(coordination.mutex);
      coordination.second_initialised = true;
    }
    coordination.changed.notify_all();

    {
      std::unique_lock<std::mutex> lock(coordination.mutex);
      coordination.changed.wait(lock,
                                [&]() { return coordination.first_checked; });
    }

    const stp::ASTNode n =
        stp::symbolic_fp::roundingMode(second_lhs) ==
        stp::symbolic_fp::roundingMode(second_rhs);
    second_uses_own_manager = n == second_expected;
  });

  first.join();
  second.join();

  EXPECT_TRUE(first_uses_own_manager);
  EXPECT_TRUE(second_uses_own_manager);
}

// Exercise the complete concurrent path too.  In addition to the symfpu
// binding above, CNF derivation must not route two independent AIGs through
// ABC's process-global convenience manager.
TEST(fp_multi_checker, concurrent_floating_point_queries)
{
  struct StartGate
  {
    std::mutex mutex;
    std::condition_variable changed;
    unsigned ready = 0;
    bool go = false;
  } gate;

  bool solved[2] = {false, false};
  auto solve = [&](unsigned worker, unsigned exponent_bits,
                   unsigned significand_bits) {
    VC vc = vc_createValidityChecker();
    Type type = vc_fpType(vc, exponent_bits, significand_bits);
    Expr rm = vc_fpRoundingMode(vc, VC_RM_RNE);
    Expr x = vc_varExpr(vc, worker == 0 ? "concurrent_x0" : "concurrent_x1",
                       type);
    Expr root = vc_fpSqrtExpr(vc, rm, x);
    Expr result = vc_fpFMAExpr(vc, rm, root, x, x);
    vc_assertFormula(vc, vc_fpIsNormalExpr(vc, result));

    {
      std::unique_lock<std::mutex> lock(gate.mutex);
      ++gate.ready;
      if (gate.ready == 2)
      {
        gate.go = true;
        gate.changed.notify_all();
      }
      else
      {
        gate.changed.wait(lock, [&]() { return gate.go; });
      }
    }

    solved[worker] = vc_query(vc, vc_falseExpr(vc)) == 0;
    vc_Destroy(vc);
  };

  std::thread first(solve, 0, 5, 11);
  std::thread second(solve, 1, 8, 24);
  first.join();
  second.join();

  EXPECT_TRUE(solved[0]);
  EXPECT_TRUE(solved[1]);
}

// Printing the FIRST checker's counterexample after the SECOND has queried:
// the model-printing path must evaluate against its own manager. (The
// blaster takes the manager explicitly; this pins that no path still leans
// on whichever manager bound last.)
TEST(fp_multi_checker, print_counterexample_across_checkers)
{
  VC v1 = vc_createValidityChecker();
  VC v2 = vc_createValidityChecker();

  Expr a = vc_varExpr(v1, "a", vc_fpType(v1, 5, 11));
  vc_assertFormula(v1, vc_fpEqExpr(v1, a, vc_fpConstFromBits(
                                              v1, 5, 11,
                                              vc_bvConstExprFromLL(v1, 16,
                                                                   0x4000))));
  EXPECT_EQ(0, vc_query(v1, vc_falseExpr(v1)));

  Expr b = vc_varExpr(v2, "b", vc_fpType(v2, 8, 24));
  vc_assertFormula(v2, vc_fpIsNormalExpr(v2, b));
  EXPECT_EQ(0, vc_query(v2, vc_falseExpr(v2))); // v2 queried last

  // Print v1's counterexample into a buffer; it must not touch v2's manager.
  char* buf = NULL;
  size_t len = 0;
  vc_printCounterExampleToBuffer(v1, &buf, &len);
  EXPECT_TRUE(buf != NULL);
  EXPECT_TRUE(len > 0);
  free(buf);

  // And v1's values still read correctly.
  EXPECT_EQ((unsigned long long)0x4000,
            getBVUnsignedLongLong(vc_getCounterExample(v1, a)));

  vc_Destroy(v1);
  vc_Destroy(v2);
}

// vc_createValidityCheckerReuse solves over nodes built through the C++
// objects' manager, and vc_Destroy still tears the pair down.
TEST(fp_multi_checker, checker_reuse_over_existing_manager)
{
  stp::STPMgr* bm = new stp::STPMgr();
  VC vc = vc_createValidityCheckerReuse(bm);

  Expr x = vc_varExpr(vc, "x", vc_fpType(vc, 5, 11));
  vc_assertFormula(vc, vc_fpIsZeroExpr(vc, x));
  vc_assertFormula(vc, vc_fpIsNegativeExpr(vc, x));
  EXPECT_EQ(0, vc_query(vc, vc_falseExpr(vc)));
  EXPECT_EQ((unsigned long long)0x8000, // -0.0 in binary16
            getBVUnsignedLongLong(vc_getCounterExample(vc, x)));

  vc_Destroy(vc);
}
