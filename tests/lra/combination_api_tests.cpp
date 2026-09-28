#include "stp/c_interface.h"

#include <atomic>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

namespace {

void require(bool condition, const char* detail)
{
  if (!condition)
    throw std::runtime_error(detail);
}

class OwnedVc final
{
public:
  explicit OwnedVc(bool array_equality = false)
      : vc_(vc_createValidityChecker())
  {
    if (array_equality)
      vc_setFlag(vc_, 'x');
  }
  ~OwnedVc()
  {
    for (auto it = expressions_.rbegin(); it != expressions_.rend(); ++it)
      vc_DeleteExpr(*it);
    vc_Destroy(vc_);
  }
  OwnedVc(const OwnedVc&) = delete;
  OwnedVc& operator=(const OwnedVc&) = delete;

  operator VC() const noexcept { return vc_; }
  Expr own(Expr expression)
  {
    expressions_.push_back(expression);
    return expression;
  }
  int solve() { return vc_query(vc_, own(vc_falseExpr(vc_))); }

private:
  VC vc_;
  std::vector<Expr> expressions_;
};

Expr real(OwnedVc& owner, const char* text)
{
  return owner.own(vc_realConstExprFromStr(owner, text));
}

Expr realSymbol(OwnedVc& owner, const char* name)
{
  return owner.own(vc_varExpr(owner, name, vc_realType(owner)));
}

void bvAndReal()
{
  OwnedVc owner;
  VC vc = owner;
  Expr x = realSymbol(owner, "x");
  Expr b = owner.own(vc_varExpr(vc, "b", vc_bvType(vc, 8)));
  Expr lra = owner.own(vc_eqExpr(vc, x, real(owner, "7/3")));
  Expr bv = owner.own(vc_eqExpr(
      vc, b, owner.own(vc_bvConstExprFromLL(vc, 8, 0xa5))));
  vc_assertFormula(vc, owner.own(vc_orExpr(vc, lra, bv)));
  vc_assertFormula(vc, lra);
  vc_assertFormula(vc, bv);
  require(owner.solve() == 0, "BV/LRA Boolean combination was not SAT");
  char* value = vc_getRealModelValue(vc, x);
  require(vc_hasRealModel(vc) == 1 && value != nullptr &&
              std::string(value) == "7/3",
          "BV/LRA combined exact model mismatch");
  vc_deleteString(value);
}


// A Real query that also carries floating-point operations, with the
// floating-point abstraction switched on: the abstraction declines, since
// the exact linear Real coordinator owns the solve's refinement loop, and
// both verdicts come out as the exact encoding decides them.
void fpAbstractionBesideReal(bool unsat)
{
  OwnedVc owner;
  VC vc = owner;
  vc_setInterfaceFlags(vc, FP_ABSTRACTION, 1);
  vc_setInterfaceFlags(vc, FP_ABSTRACTION_WIDTH, 1);
  Type single = vc_fpType(vc, 8, 24);
  // The floating-point constructors return handles the validity checker
  // owns (vc_Destroy releases them), so only the others are owned here.
  const auto constant = [&](unsigned long long bits) {
    return vc_fpConstFromBits(
        vc, 8, 24, owner.own(vc_bvConstExprFromLL(vc, 32, bits)));
  };
  Expr x = realSymbol(owner, "x");
  Expr a = owner.own(vc_varExpr(vc, "a", single));
  Expr b = owner.own(vc_varExpr(vc, "b", single));
  Expr rne = vc_fpRoundingMode(vc, VC_RM_RNE);
  // a = 3, a * b = 6 under RNE: b is exactly 2.
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, a, constant(0x40400000))));
  vc_assertFormula(
      vc, owner.own(vc_eqExpr(vc, vc_fpMulExpr(vc, rne, a, b),
                              constant(0x40c00000))));
  if (unsat)
  {
    Expr two = owner.own(vc_eqExpr(vc, b, constant(0x40000000)));
    vc_assertFormula(vc, owner.own(vc_notExpr(vc, two)));
  }
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "7/3"))));

  const int result = owner.solve();
  require(result == (unsat ? 1 : 0),
          "Real query with an abstractable floating-point operation returned "
          "the wrong verdict");
  if (!unsat)
  {
    char* value = vc_getRealModelValue(vc, x);
    require(value != nullptr && std::string(value) == "7/3",
            "Real model beside a floating-point operation mismatch");
    vc_deleteString(value);
  }
}

void arrayOutcome(bool lra_conflict, bool array_conflict)
{
  OwnedVc owner(true);
  VC vc = owner;
  Expr x = realSymbol(owner, "x");
  Type index = vc_bvType(vc, 2);
  Type value = vc_bvType(vc, 4);
  Type array = vc_arrayType(vc, index, value);
  Expr a = owner.own(vc_varExpr(vc, "a", array));
  Expr b = owner.own(vc_varExpr(vc, "b", array));
  Expr zero_index = owner.own(vc_bvConstExprFromLL(vc, 2, 0));
  Expr three = owner.own(vc_bvConstExprFromLL(vc, 4, 3));
  Expr other = owner.own(
      vc_bvConstExprFromLL(vc, 4, array_conflict ? 4 : 3));

  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, a, b)));
  Expr read_a = owner.own(vc_readExpr(vc, a, zero_index));
  Expr read_b = owner.own(vc_readExpr(vc, b, zero_index));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, read_a, three)));
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, read_b, other)));
  vc_assertFormula(
      vc, owner.own(vc_realLtExpr(vc, x, real(owner, "2"))));
  if (lra_conflict)
    vc_assertFormula(
        vc, owner.own(vc_realGeExpr(vc, x, real(owner, "2"))));
  else
    vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "1"))));

  const int result = owner.solve();
  const bool expected_sat = !lra_conflict && !array_conflict;
  if (result != (expected_sat ? 0 : 1))
  {
    std::ostringstream detail;
    detail << "LRA/array outcome combination returned " << result
           << " for lra_conflict=" << lra_conflict
           << " array_conflict=" << array_conflict;
    throw std::runtime_error(detail.str());
  }
  require(vc_hasRealModel(vc) == (expected_sat ? 1 : 0),
          "LRA/array outcome published or lost an exact model");
}

void legacyArrayReadAfterLraStage()
{
  OwnedVc owner;
  VC vc = owner;
  Expr x = realSymbol(owner, "x");
  Type bv4 = vc_bvType(vc, 4);
  vc_assertFormula(vc, owner.own(vc_eqExpr(vc, x, real(owner, "9/4"))));

  const auto impossibleReadBranch = [&](const char* array_name,
                                        const char* left_name,
                                        const char* right_name) {
    Expr array = owner.own(
        vc_varExpr(vc, array_name, vc_arrayType(vc, bv4, bv4)));
    Expr left = owner.own(vc_varExpr(vc, left_name, bv4));
    Expr right = owner.own(vc_varExpr(vc, right_name, bv4));
    Expr same_index = owner.own(vc_eqExpr(vc, left, right));
    Expr left_read = owner.own(vc_readExpr(vc, array, left));
    Expr right_read = owner.own(vc_readExpr(vc, array, right));
    Expr different_values = owner.own(
        vc_notExpr(vc, owner.own(vc_eqExpr(vc, left_read, right_read))));

    // Keep each array's initial read count above the eager
    // Ackermannisation threshold so the legacy candidate checker owns the
    // two independent refinement rounds.
    for (int k = 0; k != 10; ++k)
    {
      Expr index = owner.own(
          vc_bvConstExprFromLL(vc, 4, static_cast<unsigned>(k)));
      Expr read = owner.own(vc_readExpr(vc, array, index));
      vc_assertFormula(
          vc, owner.own(vc_eqExpr(
                  vc, read,
                  owner.own(vc_bvConstExprFromLL(
                      vc, 4, static_cast<unsigned>(k))))));
    }
    return owner.own(vc_andExpr(vc, same_index, different_values));
  };

  Expr first = impossibleReadBranch("a", "i", "j");
  Expr second = impossibleReadBranch("b", "k", "l");
  vc_assertFormula(vc, owner.own(vc_orExpr(vc, first, second)));

  vc_setFlags(vc, 's');
  std::ostringstream diagnostics;
  std::streambuf* old_buffer = std::cerr.rdbuf(diagnostics.rdbuf());
  int result = 0;
  try
  {
    result = owner.solve();
  }
  catch (...)
  {
    std::cerr.rdbuf(old_buffer);
    throw;
  }
  std::cerr.rdbuf(old_buffer);
  require(result == 1,
          "legacy array-read refinement after LRA stage was not UNSAT");
  require(vc_hasRealModel(vc) == 0,
          "legacy array refinement retained a staged Real model");

  const std::string trace = diagnostics.str();
  const std::string key = "\"legacy_refinements\":";
  const std::size_t position = trace.find(key);
  require(position != std::string::npos,
          "legacy coordinator diagnostics were not emitted");
  std::size_t value_position = position + key.size();
  unsigned refinements = 0;
  while (value_position < trace.size() &&
         trace[value_position] >= '0' && trace[value_position] <= '9')
  {
    refinements = refinements * 10U +
                  static_cast<unsigned>(trace[value_position] - '0');
    ++value_position;
  }
  if (refinements < 2)
    throw std::runtime_error(
        "legacy array fixture did not require multiple candidate rounds: " +
        std::to_string(refinements) + "\n" + trace);
}

void interleavedManagers()
{
  OwnedVc first_owner;
  OwnedVc second_owner;
  VC first = first_owner;
  VC second = second_owner;
  Expr x = realSymbol(first_owner, "x");
  Expr y = realSymbol(second_owner, "y");
  vc_assertFormula(first, first_owner.own(
                              vc_eqExpr(first, x, real(first_owner, "11/13"))));
  vc_assertFormula(
      second, second_owner.own(
                  vc_eqExpr(second, y, real(second_owner, "-17/19"))));
  require(first_owner.solve() == 0 && second_owner.solve() == 0 &&
              first_owner.solve() == 0,
          "interleaved independent managers disagreed");
  char* xv = vc_getRealModelValue(first, x);
  char* yv = vc_getRealModelValue(second, y);
  require(std::string(xv) == "11/13" && std::string(yv) == "-17/19",
          "interleaved manager models mixed values");
  vc_deleteString(xv);
  vc_deleteString(yv);
}

void concurrentManagers()
{
  std::atomic<unsigned> failures{0};
  std::vector<std::thread> workers;
  for (unsigned worker = 0; worker != 4; ++worker)
  {
    workers.emplace_back([worker, &failures]() {
      try
      {
        for (unsigned round = 0; round != 20; ++round)
        {
          OwnedVc owner;
          VC vc = owner;
          Expr x = realSymbol(owner, "thread_x");
          const std::string expected =
              std::to_string(worker * 20 + round + 1) + "/997";
          vc_assertFormula(
              vc, owner.own(
                      vc_eqExpr(vc, x, real(owner, expected.c_str()))));
          if (owner.solve() != 0)
            throw std::runtime_error("concurrent solve failed");
          char* value = vc_getRealModelValue(vc, x);
          const std::string actual(value);
          vc_deleteString(value);
          if (actual != expected)
            throw std::runtime_error("concurrent model mismatch");
        }
      }
      catch (...)
      {
        failures.fetch_add(1, std::memory_order_relaxed);
      }
    });
  }
  for (std::thread& worker : workers)
    worker.join();
  require(failures.load(std::memory_order_relaxed) == 0,
          "independent concurrent managers failed");
}

} // namespace

int main()
{
  try
  {
    bvAndReal();
    fpAbstractionBesideReal(false);
    fpAbstractionBesideReal(true);
    arrayOutcome(true, true);
    arrayOutcome(true, false);
    arrayOutcome(false, true);
    arrayOutcome(false, false);
    legacyArrayReadAfterLraStage();
    interleavedManagers();
    concurrentManagers();
    std::cout << "PASS combination-api\n";
    return 0;
  }
  catch (const std::exception& failure)
  {
    std::cerr << "FAIL " << failure.what() << '\n';
    return 1;
  }
}
