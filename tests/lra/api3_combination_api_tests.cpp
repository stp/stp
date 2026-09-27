/********************************************************************
 * AUTHORS: Andrew Teylu
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

// api3_combination_api_tests.cpp -- exact Real arithmetic beside the other
// theories, through the 3.x C++ API: a Boolean combination with a bit-vector,
// floating-point operations under the floating-point abstraction, extensional
// arrays in every combination of verdicts, the array-read refinement after the
// Real stage, and independent managers, interleaved and on threads.
//
// A plain executable: every case runs in order and the first failed check
// ends the run with a non-zero exit.

#include <stp/stp.hpp>

#include <atomic>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <thread>
#include <vector>

using namespace stp;

namespace
{

void require(bool condition, const char* detail)
{
  if (!condition)
    throw std::runtime_error(detail);
}

Term realSymbol(TermManager& tm, const char* name)
{
  return tm.declare(name, tm.mk_real_sort());
}

// The exact value the last satisfiable check gave a Real term, as "n/d" or
// "n". A model exists only after a check that answered sat; 2.x's separate
// question of whether an exact Real model had been published is that one.
std::string realValue(const Solver& s, const Term& term)
{
  return s.model().real_value(term).str();
}

// Whether the solver has no model to give: the last check did not answer
// sat, so model() refuses with NO_MODEL.
bool hasNoModel(const Solver& s)
{
  try
  {
    (void)s.model();
  }
  catch (const RecoverableError& error)
  {
    return error.code() == ErrorCode::NO_MODEL;
  }
  return false;
}

void bvAndReal()
{
  TermManager tm;
  Solver s(tm);
  const Term x = realSymbol(tm, "x");
  const Term b = tm.declare("b", tm.mk_bv_sort(8));
  const Term lra = x == tm.mk_real("7/3");
  const Term bv = b == tm.mk_bv(8, 0xa5);
  s.add(lra || bv);
  s.add(lra);
  s.add(bv);
  require(s.check_sat().is_sat(), "BV/LRA Boolean combination was not SAT");
  require(s.model().in_core(x) && realValue(s, x) == "7/3",
          "BV/LRA combined exact model mismatch");
}

// A Real query that also carries floating-point operations, with the
// floating-point abstraction switched on: the abstraction declines, since
// the exact linear Real coordinator owns the solve's refinement loop, and
// both verdicts come out as the exact encoding decides them.
void fpAbstractionBesideReal(bool unsat)
{
  TermManager tm;
  Solver s(tm);
  s.options().set_bool("fp-abstraction", true);
  s.options().set_uint("fp-abstraction-width", 1);
  const Sort single = tm.mk_fp_sort(8, 24);
  const auto constant = [&](std::uint64_t bits) {
    return tm.mk_fp_from_bits(single, tm.mk_bv(32, bits));
  };
  const Term x = realSymbol(tm, "x");
  const Term a = tm.declare("a", single);
  const Term b = tm.declare("b", single);
  // a = 3, a * b = 6 under RNE: b is exactly 2.
  s.add(a == constant(0x40400000));
  s.add(fp_mul(RoundingMode::RNE, a, b) == constant(0x40c00000));
  if (unsat)
    s.add(!(b == constant(0x40000000)));
  s.add(x == tm.mk_real("7/3"));

  const Result result = s.check_sat();
  require(unsat ? result.is_unsat() : result.is_sat(),
          "Real query with an abstractable floating-point operation returned "
          "the wrong verdict");
  if (!unsat)
    require(realValue(s, x) == "7/3",
            "Real model beside a floating-point operation mismatch");
}

void arrayOutcome(bool lra_conflict, bool array_conflict)
{
  TermManager tm;
  Solver s(tm);
  // 2.x's 'x' flag: whole-array equality decided by lemmas on demand.
  s.options().set_str("array-equality", "on");
  const Term x = realSymbol(tm, "x");
  const Sort index = tm.mk_bv_sort(2);
  const Sort value = tm.mk_bv_sort(4);
  const Sort array = tm.mk_array_sort(index, value);
  const Term a = tm.declare("a", array);
  const Term b = tm.declare("b", array);
  const Term zero_index = tm.mk_bv(2, 0);
  const Term three = tm.mk_bv(4, 3);
  const Term other = tm.mk_bv(4, array_conflict ? 4 : 3);

  s.add(a == b);
  s.add(a[zero_index] == three);
  s.add(b[zero_index] == other);
  s.add(real_lt(x, tm.mk_real(2)));
  if (lra_conflict)
    s.add(real_ge(x, tm.mk_real(2)));
  else
    s.add(x == tm.mk_real(1));

  const Result result = s.check_sat();
  const bool expected_sat = !lra_conflict && !array_conflict;
  if (expected_sat ? !result.is_sat() : !result.is_unsat())
  {
    std::ostringstream detail;
    detail << "LRA/array outcome combination returned " << result
           << " for lra_conflict=" << lra_conflict
           << " array_conflict=" << array_conflict;
    throw std::runtime_error(detail.str());
  }
  // A model, with x's exact value, exactly when the check answered sat.
  if (expected_sat)
    require(realValue(s, x) == "1", "LRA/array outcome lost its exact model");
  else
    require(hasNoModel(s), "LRA/array outcome published a model for unsat");
}

// The value of `"key":<digits>` in a diagnostic trace, or -1 if absent.
long long traceCounter(const std::string& trace, const std::string& key)
{
  const std::string quoted = "\"" + key + "\":";
  const std::size_t position = trace.find(quoted);
  if (position == std::string::npos)
    return -1;
  long long value = 0;
  for (std::size_t i = position + quoted.size();
       i < trace.size() && trace[i] >= '0' && trace[i] <= '9'; ++i)
    value = value * 10 + (trace[i] - '0');
  return value;
}

void legacyArrayReadAfterLraStage()
{
  TermManager tm;
  Solver s(tm);
  const Term x = realSymbol(tm, "x");
  const Sort bv4 = tm.mk_bv_sort(4);
  s.add(x == tm.mk_real("9/4"));

  const auto impossibleReadBranch = [&](const char* array_name,
                                        const char* left_name,
                                        const char* right_name) {
    const Term array = tm.declare(array_name, tm.mk_array_sort(bv4, bv4));
    const Term left = tm.declare(left_name, bv4);
    const Term right = tm.declare(right_name, bv4);
    const Term same_index = left == right;
    const Term different_values = !(array[left] == array[right]);

    // Keep each array's initial read count above the eager
    // Ackermannisation threshold so the legacy candidate checker owns the
    // two independent refinement rounds.
    for (std::uint64_t k = 0; k != 10; ++k)
      s.add(array[tm.mk_bv(4, k)] == tm.mk_bv(4, k));
    return same_index && different_values;
  };

  const Term first = impossibleReadBranch("a", "i", "j");
  const Term second = impossibleReadBranch("b", "k", "l");
  s.add(first || second);

  // 2.x's 's' flag: the coordinator's metrics, which carry the number of
  // legacy refinement rounds, are diagnostic output.
  s.options().set_bool("print-functionstat", true);
  std::string diagnostics;
  s.set_diagnostic_sink(
      [&diagnostics](std::string_view text) { diagnostics.append(text); });
  const Result result = s.check_sat();
  s.set_diagnostic_sink(nullptr);
  require(result.is_unsat(),
          "legacy array-read refinement after LRA stage was not UNSAT");
  require(hasNoModel(s), "legacy array refinement retained a staged Real model");

  const long long refinements =
      traceCounter(diagnostics, "legacy_refinements");
  require(refinements >= 0, "legacy coordinator diagnostics were not emitted");
  if (refinements < 2)
    throw std::runtime_error(
        "legacy array fixture did not require multiple candidate rounds: " +
        std::to_string(refinements) + "\n" + diagnostics);
}

void interleavedManagers()
{
  TermManager first_tm;
  TermManager second_tm;
  Solver first(first_tm);
  Solver second(second_tm);
  const Term x = realSymbol(first_tm, "x");
  const Term y = realSymbol(second_tm, "y");
  first.add(x == first_tm.mk_real("11/13"));
  second.add(y == second_tm.mk_real("-17/19"));
  require(first.check_sat().is_sat() && second.check_sat().is_sat() &&
              first.check_sat().is_sat(),
          "interleaved independent managers disagreed");
  require(realValue(first, x) == "11/13" && realValue(second, y) == "-17/19",
          "interleaved manager models mixed values");
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
          TermManager tm;
          Solver s(tm);
          const Term x = realSymbol(tm, "thread_x");
          const std::string expected =
              std::to_string(worker * 20 + round + 1) + "/997";
          s.add(x == tm.mk_real(expected));
          if (!s.check_sat().is_sat())
            throw std::runtime_error("concurrent solve failed");
          if (realValue(s, x) != expected)
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
