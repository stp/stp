#include "ExactLraCore.h"
#include "ExactSimplex.h"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <optional>
#include <random>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <utility>
#include <vector>

namespace {

using namespace stp::lra;

constexpr NumberLimits limits{
    50000, 50000, UINT64_C(128) * 1024U * 1024U,
    UINT64_C(4) * 1024U * 1024U};

[[noreturn]] void fail(std::string const& message)
{
  throw std::runtime_error(message);
}

void require(bool condition, std::string const& message)
{
  if (!condition)
  {
    fail(message);
  }
}

class Observer final : public ExactLraResourceObserver
{
 public:
  explicit Observer(StopReason first = StopReason::Continue)
      : first_(first)
  {}

  StopReason pollBeforePivot() noexcept override
  {
    ++polls;
    if (!used_)
    {
      used_ = true;
      return first_;
    }
    return StopReason::Continue;
  }

  void accountPivot(bool bland) noexcept override
  {
    ++pivots;
    bland_pivots += bland ? 1U : 0U;
  }

  std::uint64_t polls = 0;
  std::uint64_t pivots = 0;
  std::uint64_t bland_pivots = 0;

 private:
  StopReason first_;
  bool used_ = false;
};

class PivotBudgetObserver final : public ExactLraResourceObserver
{
 public:
  PivotBudgetObserver(std::uint64_t allowed_pivots, StopReason exhausted)
      : allowed_pivots_(allowed_pivots), exhausted_(exhausted)
  {}

  StopReason pollBeforePivot() noexcept override
  {
    ++polls;
    return pivots < allowed_pivots_ ? StopReason::Continue : exhausted_;
  }

  void accountPivot(bool bland) noexcept override
  {
    ++pivots;
    bland_pivots += bland ? 1U : 0U;
  }

  std::uint64_t polls = 0;
  std::uint64_t pivots = 0;
  std::uint64_t bland_pivots = 0;

 private:
  std::uint64_t allowed_pivots_;
  StopReason exhausted_;
};

bool early_conflict_mode = false;
bool soi_mode = false;
DirectBoundsMode direct_bounds_mode = DirectBoundsMode::Disabled;

struct Fixture final
{
  explicit Fixture(DirectBoundsMode direct_bounds = direct_bounds_mode)
      : input_budget(limits), core(limits, direct_bounds)
  {
    core.setEarlyConflictDetection(early_conflict_mode);
    core.setSoi(soi_mode);
  }

  ExactRational rational(std::string const& text)
  {
    NumberOperationScope scope(input_budget);
    return ExactRational::parseDecimalOrFraction(text);
  }

  std::string render(ExactRational const& value)
  {
    NumberOperationScope scope(input_budget);
    return value.canonicalFraction();
  }

  VariableId variable()
  {
    auto result = core.addVariable();
    require(result.status == InputStatus::Accepted && result.value,
            "variable registration failed");
    return *result.value;
  }

  RowId row(std::vector<std::pair<VariableId, std::string>> const& input)
  {
    std::vector<LinearTerm> terms;
    terms.reserve(input.size());
    for (auto const& [variable_id, coefficient] : input)
    {
      terms.push_back(LinearTerm{variable_id, rational(coefficient)});
    }
    auto result = core.addRow(terms.data(), terms.data() + terms.size());
    require(result.status == InputStatus::Accepted && result.value,
            "row registration failed");
    return *result.value;
  }

  AtomId atom(RowId row_id,
              Relation relation,
              std::string const& threshold,
              std::uint64_t serial,
              std::uint64_t negative_serial = 0)
  {
    ExactRational value = rational(threshold);
    auto result = core.addAtom(
        row_id, relation, value, OriginId{1, serial},
        OriginId{1, negative_serial == 0 ? serial + 100000U
                                        : negative_serial});
    require(result.status == InputStatus::Accepted && result.value,
            "atom registration failed");
    return *result.value;
  }

  Checkpoint initializeAndPush()
  {
    require(core.initialize() == InputStatus::Accepted,
            "initialization failed");
    auto pushed = core.push();
    require(pushed.status == InputStatus::Accepted && pushed.value,
            "push failed");
    return *pushed.value;
  }

  NumberBudget input_budget;
  ExactLraCore core;
};

ModelValue const& modelValue(Model const& model, VariableId variable)
{
  for (ModelValue const& entry : model.values)
  {
    if (entry.variable == variable)
    {
      return entry;
    }
  }
  fail("model variable is missing");
}

void testSemantic()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  VariableId const free = fixture.variable();
  RowId const row = fixture.row({{x, "1"}});
  RowId const alias = fixture.row({{x, "1"}});
  AtomId const lower = fixture.atom(row, Relation::GreaterEqual, "0", 1);
  AtomId const upper = fixture.atom(alias, Relation::LessEqual, "2", 2);
  Checkpoint const checkpoint = fixture.initializeAndPush();
  require(fixture.core.assertLiteral(lower, true).status ==
              InputStatus::Accepted,
          "lower assertion failed");
  require(fixture.core.assertLiteral(upper, true).status ==
              InputStatus::Accepted,
          "upper assertion failed");
  Observer observer;
  CheckResult result = fixture.core.check(observer);
  require(result.status == CheckStatus::Consistent && result.model &&
              !result.conflict,
          "semantic range must be consistent");
  require(result.model->values.size() == 2,
          "model must contain every base variable");
  require(result.model->values[0].variable == x &&
              result.model->values[1].variable == free,
          "model order must be canonical");
  require(fixture.render(modelValue(*result.model, x).value) == "0",
          "unexpected exact model value");
  require(fixture.render(modelValue(*result.model, free).value) == "0",
          "free variable must have a deterministic value");
  require(fixture.core.verifyModel(*result.model).verified(),
          "independent model verification failed");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "terminal pop failed");
}

void testSeparateModelValues()
{
  // Two variables with room to move and nothing tying them together. The
  // search leaves both at zero, which is a coincidence rather than a
  // consequence of the query, and any reader that groups by value -- the
  // lazy congruence round does -- sees a pair there. With separation on they
  // come out distinct, and the model is still a model.
  Fixture fixture;
  VariableId const x = fixture.variable();
  VariableId const y = fixture.variable();
  RowId const x_low_row = fixture.row({{x, "1"}});
  RowId const x_high_row = fixture.row({{x, "1"}});
  RowId const y_low_row = fixture.row({{y, "1"}});
  RowId const y_high_row = fixture.row({{y, "1"}});
  AtomId const x_low = fixture.atom(x_low_row, Relation::GreaterEqual, "0", 1);
  AtomId const x_high = fixture.atom(x_high_row, Relation::LessEqual, "10", 2);
  AtomId const y_low = fixture.atom(y_low_row, Relation::GreaterEqual, "0", 3);
  AtomId const y_high = fixture.atom(y_high_row, Relation::LessEqual, "10", 4);
  Checkpoint const checkpoint = fixture.initializeAndPush();
  for (AtomId const atom : {x_low, x_high, y_low, y_high})
  {
    require(fixture.core.assertLiteral(atom, true).status ==
                InputStatus::Accepted,
            "range assertion failed");
  }

  Observer observer;
  fixture.core.setSeparateModelValues(true);
  CheckResult const result = fixture.core.check(observer);
  require(result.status == CheckStatus::Consistent && result.model,
          "bounded ranges must be consistent");
  std::string const x_text = fixture.render(modelValue(*result.model, x).value);
  std::string const y_text = fixture.render(modelValue(*result.model, y).value);
  require(x_text != y_text,
          "variables with slack must not share a value once separated");
  require(fixture.core.verifyModel(*result.model).verified(),
          "separated model failed independent verification");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "terminal pop failed");
}

void testSeparateRespectsForcedEquality()
{
  // The other half of the rule: a query that does force two values equal has
  // no slack to give, so separation must leave them alone rather than break
  // the model to satisfy its own preference.
  Fixture fixture;
  VariableId const x = fixture.variable();
  VariableId const y = fixture.variable();
  RowId const x_low_row = fixture.row({{x, "1"}});
  RowId const x_high_row = fixture.row({{x, "1"}});
  RowId const difference = fixture.row({{x, "1"}, {y, "-1"}});
  RowId const difference_alias = fixture.row({{x, "1"}, {y, "-1"}});
  AtomId const x_low = fixture.atom(x_low_row, Relation::GreaterEqual, "3", 1);
  AtomId const x_high = fixture.atom(x_high_row, Relation::LessEqual, "3", 2);
  AtomId const same_low =
      fixture.atom(difference, Relation::GreaterEqual, "0", 3);
  AtomId const same_high =
      fixture.atom(difference_alias, Relation::LessEqual, "0", 4);
  Checkpoint const checkpoint = fixture.initializeAndPush();
  for (AtomId const atom : {x_low, x_high, same_low, same_high})
  {
    require(fixture.core.assertLiteral(atom, true).status ==
                InputStatus::Accepted,
            "equality assertion failed");
  }

  Observer observer;
  fixture.core.setSeparateModelValues(true);
  CheckResult const result = fixture.core.check(observer);
  require(result.status == CheckStatus::Consistent && result.model,
          "forced equality must be consistent");
  require(fixture.render(modelValue(*result.model, x).value) == "3" &&
              fixture.render(modelValue(*result.model, y).value) == "3",
          "a forced equality must survive separation");
  require(fixture.core.verifyModel(*result.model).verified(),
          "forced-equality model failed independent verification");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "terminal pop failed");
}

void testStrict()
{
  {
    Fixture fixture;
    VariableId const x = fixture.variable();
    RowId const row = fixture.row({{x, "1"}});
    AtomId const lower = fixture.atom(row, Relation::Greater, "0", 10);
    AtomId const upper = fixture.atom(row, Relation::Less, "1", 11);
    Checkpoint const checkpoint = fixture.initializeAndPush();
    require(fixture.core.assertLiteral(lower, true).status ==
                InputStatus::Accepted,
            "strict lower assertion failed");
    require(fixture.core.assertLiteral(upper, true).status ==
                InputStatus::Accepted,
            "strict upper assertion failed");
    Observer observer;
    CheckResult result = fixture.core.check(observer);
    require(result.status == CheckStatus::Consistent && result.model,
            "strict interior must be consistent");
    std::string const interior =
        fixture.render(modelValue(*result.model, x).value);
    require(interior == "1/4",
            "strict interior model must be exact, got " + interior);
    require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
            "strict SAT pop failed");
  }
  {
    Fixture fixture;
    VariableId const x = fixture.variable();
    RowId const row = fixture.row({{x, "1"}});
    AtomId const upper = fixture.atom(row, Relation::Less, "0", 20);
    AtomId const lower = fixture.atom(row, Relation::GreaterEqual, "0", 21);
    Checkpoint const checkpoint = fixture.initializeAndPush();
    require(fixture.core.assertLiteral(upper, true).status ==
                InputStatus::Accepted,
            "strict conflict first assertion failed");
    AssertResult conflict = fixture.core.assertLiteral(lower, true);
    require(conflict.status == InputStatus::Accepted &&
                conflict.immediate_conflict &&
                conflict.immediate_conflict->terms.size() == 2,
            "strict boundary conflict was not immediate");
    require(fixture.core.verifyConflict(*conflict.immediate_conflict).verified(),
            "independent immediate-conflict verification failed");
    require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
            "strict conflict pop failed");
  }
}

void testRelations()
{
  Relation const relations[] = {Relation::Less, Relation::LessEqual,
                                Relation::Greater, Relation::GreaterEqual};
  for (Relation relation : relations)
  {
    for (bool polarity : {false, true})
    {
      Fixture fixture;
      VariableId const x = fixture.variable();
      RowId const row = fixture.row({{x, "1"}});
      AtomId const atom = fixture.atom(row, relation, "3/7", 30);
      Checkpoint const checkpoint = fixture.initializeAndPush();
      require(fixture.core.assertLiteral(atom, polarity).status ==
                  InputStatus::Accepted,
              "relation polarity assertion failed");
      Observer observer;
      CheckResult result = fixture.core.check(observer);
      require(result.status == CheckStatus::Consistent && result.model,
              "one complementary relation must be satisfiable");
      require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
              "relation pop failed");
    }
  }
}

void testTableauConflict()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const first_row = fixture.row({{x, "1"}});
  RowId const second_row = fixture.row({{x, "1"}});
  AtomId const upper =
      fixture.atom(first_row, Relation::LessEqual, "0", 41);
  AtomId const lower =
      fixture.atom(second_row, Relation::GreaterEqual, "1", 42);
  Checkpoint const checkpoint = fixture.initializeAndPush();
  require(fixture.core.assertLiteral(upper, true).status ==
              InputStatus::Accepted,
          "tableau upper assertion failed");
  require(fixture.core.assertLiteral(lower, true).status ==
              InputStatus::Accepted,
          "tableau lower assertion failed");
  Observer observer;
  CheckResult result = fixture.core.check(observer);
  require(result.status == CheckStatus::Conflict && result.conflict &&
              !result.model && result.conflict->terms.size() == 2,
          "tableau conflict certificate missing");
  require(fixture.core.verifyConflict(*result.conflict).verified(),
          "tableau conflict failed independent verification");
  require(observer.pivots == 1, "tableau conflict must require one pivot");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "tableau conflict pop failed");
}

/* A conflict leaves the simplex part-way between two consistent models, and
 * the model is only put right again on the way out of a check or a pop.  A
 * caller that keeps the core alive across the conflict -- popping back and
 * carrying on rather than rebuilding, which is what driving the search from
 * inside the SAT solver requires -- must still get a usable verdict from the
 * next check, not an internal error from a broken simplex invariant. */
/* A conflict certificate should name the weakest bounds that still
 * contradict, not the tightest ones the search happens to have asserted.
 * The no-good handed back is the negation of those bounds, so naming a weaker
 * one rules out strictly more assignments -- and the bound-ordering axioms
 * cannot recover the weaker clause from the tighter one, that resolution runs
 * the other way. */
void testGeneralisedConflict()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  VariableId const y = fixture.variable();
  RowId const x_row = fixture.row({{x, "1"}});
  RowId const y_row = fixture.row({{y, "1"}});
  RowId const sum = fixture.row({{x, "1"}, {y, "1"}});
  AtomId const x_weak = fixture.atom(x_row, Relation::GreaterEqual, "1", 81);
  AtomId const x_tight = fixture.atom(x_row, Relation::GreaterEqual, "5", 82);
  AtomId const y_low = fixture.atom(y_row, Relation::GreaterEqual, "5", 83);
  AtomId const sum_high = fixture.atom(sum, Relation::LessEqual, "4", 84);

  Checkpoint const checkpoint = fixture.initializeAndPush();
  /* Weakest first: a bound is only recorded when it tightens the one before
   * it, so this is what makes both of x's lower bounds active at once. */
  for (AtomId const atom : {x_weak, x_tight, y_low, sum_high})
  {
    require(fixture.core.assertLiteral(atom, true).status ==
                InputStatus::Accepted,
            "generalised conflict assertion failed");
  }

  Observer observer;
  CheckResult const result = fixture.core.check(observer);
  require(result.status == CheckStatus::Conflict && result.conflict,
          "generalised conflict did not conflict");
  require(observer.pivots > 0,
          "generalised conflict was decided without pivoting");
  require(fixture.core.verifyConflict(*result.conflict).verified(),
          "generalised conflict failed independent verification");

  /* x >= 1 with y >= 5 already exceeds x + y <= 4, so the certificate has no
   * business naming x >= 5. */
  bool names_weak = false;
  bool names_tight = false;
  for (ConflictTerm const& term : result.conflict->terms)
  {
    names_weak = names_weak || term.origin.serial == 81;
    names_tight = names_tight || term.origin.serial == 82;
  }
  require(names_weak && !names_tight,
          "conflict kept the tighter bound where a weaker one contradicts");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "generalised conflict pop failed");
}

void testConflictThenReuse()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  VariableId const y = fixture.variable();
  RowId const x_row = fixture.row({{x, "1"}});
  RowId const y_row = fixture.row({{y, "1"}});
  RowId const sum = fixture.row({{x, "1"}, {y, "1"}});
  AtomId const x_low = fixture.atom(x_row, Relation::GreaterEqual, "5", 61);
  AtomId const y_low = fixture.atom(y_row, Relation::GreaterEqual, "5", 62);
  AtomId const sum_high = fixture.atom(sum, Relation::LessEqual, "8", 63);

  // One level per decision, bounds asserted as they arrive: the shape the
  // search imposes when the theory rides along inside it.
  Checkpoint const outer = fixture.initializeAndPush();
  require(fixture.core.assertLiteral(x_low, true).status ==
              InputStatus::Accepted,
          "reuse outer assertion failed");
  auto const inner = fixture.core.push();
  require(inner.status == InputStatus::Accepted && inner.value,
          "reuse inner push failed");
  require(fixture.core.assertLiteral(y_low, true).status ==
              InputStatus::Accepted,
          "reuse inner lower assertion failed");
  require(fixture.core.assertLiteral(sum_high, true).status ==
              InputStatus::Accepted,
          "reuse inner upper assertion failed");
  Observer conflicting;
  CheckResult const conflicted = fixture.core.check(conflicting);
  require(conflicted.status == CheckStatus::Conflict && conflicted.conflict,
          "reuse inner level should conflict");
  /* The conflict has to be one the simplex pivots its way into: a bound that
   * contradicts another on the same row is caught before any value moves,
   * which is not the case this test is about. */
  require(conflicting.pivots > 0,
          "reuse conflict was decided without pivoting");
  require(fixture.core.verifyConflict(*conflicted.conflict).verified(),
          "reuse conflict failed independent verification");

  // Back to the outer level and on with the search, without rebuilding.
  require(fixture.core.pop(*inner.value) == InputStatus::Accepted,
          "reuse pop failed");
  Observer resuming;
  CheckResult const resumed = fixture.core.check(resuming);
  require(resumed.status == CheckStatus::Consistent && resumed.model,
          "reuse after conflict produced no model");
  // The bound that outlived the conflict must still be respected.
  ModelValue const& value = modelValue(*resumed.model, x);
  require(fixture.render(value.value) == "5",
          "reuse model ignored the surviving bound");
  require(fixture.core.pop(outer) == InputStatus::Accepted,
          "reuse outer pop failed");
}

void testSharedOrigin()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const first_row = fixture.row({{x, "1"}});
  RowId const second_row = fixture.row({{x, "1"}});
  ExactRational zero = fixture.rational("0");
  ExactRational one = fixture.rational("1");
  OriginId const shared{7, 9};
  auto first = fixture.core.addAtom(first_row, Relation::LessEqual, zero,
                                    shared, OriginId{7, 10});
  auto second = fixture.core.addAtom(second_row, Relation::GreaterEqual, one,
                                     shared, OriginId{7, 11});
  require(first.value && second.value, "shared-origin atom registration failed");
  Checkpoint const checkpoint = fixture.initializeAndPush();
  require(fixture.core.assertLiteral(*first.value, true).status ==
              InputStatus::Accepted,
          "shared-origin first assertion failed");
  require(fixture.core.assertLiteral(*second.value, true).status ==
              InputStatus::Accepted,
          "shared-origin second assertion failed");
  Observer observer;
  CheckResult result = fixture.core.check(observer);
  require(result.status == CheckStatus::Conflict && result.conflict &&
              result.conflict->terms.size() == 2 &&
              result.conflict->terms[0].origin == shared &&
              result.conflict->terms[1].origin == shared,
          "distinct equality components sharing an origin were lost");
  require(fixture.core.verifyConflict(*result.conflict).verified(),
          "shared-origin conflict failed independent verification");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "shared-origin pop failed");
}

void testInterruption(StopReason stop, CheckStatus expected)
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row({{x, "1"}});
  AtomId const lower = fixture.atom(row, Relation::Greater, "0", 50);
  Checkpoint const checkpoint = fixture.initializeAndPush();
  require(fixture.core.assertLiteral(lower, true).status ==
              InputStatus::Accepted,
          "stoppable assertion failed");
  Observer stopping(stop);
  CheckResult stopped = fixture.core.check(stopping);
  require(stopped.status == expected && !stopped.model && !stopped.conflict &&
              stopping.polls == 1 && stopping.pivots == 0,
          "pre-pivot stop did not preserve a witness-free result");
  Observer resume;
  CheckResult resumed = fixture.core.check(resume);
  require(resumed.status == CheckStatus::Consistent && resumed.model &&
              resume.pivots == 1,
          "same-core exact resume failed");
  require(fixture.core.verifyModel(*resumed.model).verified(),
          "resumed model failed independent verification");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "stoppable candidate pop failed");
}

void testPivotBudgets()
{
  {
    Fixture fixture;
    VariableId const x = fixture.variable();
    RowId const row = fixture.row({{x, "1"}});
    AtomId const lower = fixture.atom(row, Relation::Greater, "0", 51);
    Checkpoint const checkpoint = fixture.initializeAndPush();
    require(fixture.core.assertLiteral(lower, true).status ==
                InputStatus::Accepted,
            "one-pivot budget assertion failed");
    PivotBudgetObserver one_pivot(1, StopReason::ResourceLimit);
    CheckResult result = fixture.core.check(one_pivot);
    require(result.status == CheckStatus::Consistent && result.model &&
                !result.conflict && one_pivot.polls == 1 &&
                one_pivot.pivots == 1,
            "one-pivot budget stopped too early or returned no model");
    require(fixture.core.verifyModel(*result.model).verified(),
            "one-pivot model failed independent verification");
    require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
            "one-pivot budget pop failed");
  }

  {
    Fixture fixture;
    VariableId const x = fixture.variable();
    VariableId const y = fixture.variable();
    RowId const x_row = fixture.row({{x, "1"}});
    RowId const y_row = fixture.row({{y, "1"}});
    RowId const sum_row = fixture.row({{x, "1"}, {y, "1"}});
    AtomId const x_upper =
        fixture.atom(x_row, Relation::LessEqual, "0", 52);
    AtomId const y_upper =
        fixture.atom(y_row, Relation::LessEqual, "0", 53);
    AtomId const sum_lower =
        fixture.atom(sum_row, Relation::GreaterEqual, "1", 54);
    Checkpoint const checkpoint = fixture.initializeAndPush();
    require(fixture.core.assertLiteral(x_upper, true).status ==
                    InputStatus::Accepted &&
                fixture.core.assertLiteral(y_upper, true).status ==
                    InputStatus::Accepted &&
                fixture.core.assertLiteral(sum_lower, true).status ==
                    InputStatus::Accepted,
            "mid-run budget assertion setup failed");
    PivotBudgetObserver one_then_stop(1, StopReason::ResourceLimit);
    CheckResult stopped = fixture.core.check(one_then_stop);
    require(stopped.status == CheckStatus::ResourceLimit && !stopped.model &&
                !stopped.conflict && one_then_stop.polls == 2 &&
                one_then_stop.pivots == 1,
            "mid-run resource stop was not witness-free after one pivot");
    Observer resume;
    CheckResult resumed = fixture.core.check(resume);
    require(resumed.status == CheckStatus::Conflict && resumed.conflict &&
                !resumed.model && resume.pivots == 1,
            "mid-run resource stop did not resume the same tableau state");
    require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
            "mid-run resource candidate pop failed");
  }
}

void testNumberResourceLimits()
{
  NumberLimits const input_limits{
      65536, 65536, UINT64_C(64) * 1024U * 1024U,
      UINT64_C(4) * 1024U * 1024U};
  NumberLimits const small_operand_limits{
      8, 64, UINT64_C(8) * 1024U * 1024U, 4096};
  NumberBudget input(input_limits);
  ExactLraCore registration_core(small_operand_limits);
  auto parse = [&input](char const* text) {
    NumberOperationScope scope(input);
    return ExactRational::parseDecimalOrFraction(text);
  };
  auto variable = registration_core.addVariable();
  require(variable.value.has_value(), "resource registration variable failed");
  LinearTerm unit{*variable.value, parse("1")};
  auto row = registration_core.addRow(&unit, &unit + 1);
  require(row.value.has_value(), "resource registration row failed");
  ExactRational huge_threshold = parse("1024");
  auto stopped_atom = registration_core.addAtom(
      *row.value, Relation::GreaterEqual, huge_threshold, OriginId{4, 1},
      OriginId{4, 2});
  require(stopped_atom.status == InputStatus::ResourceLimit &&
              !stopped_atom.value &&
              registration_core.status() == CheckStatus::Ready,
          "safe registration preflight did not return ResourceLimit");
  ExactRational zero = parse("0");
  auto retry_atom = registration_core.addAtom(
      *row.value, Relation::GreaterEqual, zero, OriginId{4, 3},
      OriginId{4, 4});
  require(retry_atom.value.has_value(),
          "safe registration resource failure was not retryable");
  require(registration_core.initialize() == InputStatus::Accepted,
          "resource registration retry initialization failed");
  auto checkpoint = registration_core.push();
  require(checkpoint.value.has_value(), "resource registration push failed");
  require(registration_core.assertLiteral(*retry_atom.value, true).status ==
              InputStatus::Accepted,
          "resource registration retry assertion failed");
  Observer observer;
  CheckResult retry = registration_core.check(observer);
  require(retry.status == CheckStatus::Consistent && retry.model,
          "safe registration resource failure changed semantics");
  require(registration_core.verifyModel(*retry.model).verified(),
          "resource-retry model failed independent verification");
  require(registration_core.pop(*checkpoint.value) == InputStatus::Accepted,
          "resource registration retry pop failed");

  NumberLimits const small_result_limits{
      8, 8, UINT64_C(8) * 1024U * 1024U, 4096};
  ExactLraCore pivot_core(small_result_limits);
  auto x = pivot_core.addVariable();
  require(x.value.has_value(), "pivot resource variable failed");
  LinearTerm first_term{*x.value, parse("1")};
  LinearTerm amplified_term{*x.value, parse("127")};
  auto first_row = pivot_core.addRow(&first_term, &first_term + 1);
  auto amplified_row =
      pivot_core.addRow(&amplified_term, &amplified_term + 1);
  require(first_row.value && amplified_row.value,
          "pivot resource row setup failed");
  ExactRational threshold = parse("127");
  auto lower = pivot_core.addAtom(
      *first_row.value, Relation::GreaterEqual, threshold, OriginId{5, 1},
      OriginId{5, 2});
  require(lower.value.has_value(), "pivot resource atom setup failed");
  require(pivot_core.initialize() == InputStatus::Accepted,
          "pivot resource initialization failed");
  auto pivot_checkpoint = pivot_core.push();
  require(pivot_checkpoint.value.has_value(), "pivot resource push failed");
  require(pivot_core.assertLiteral(*lower.value, true).status ==
              InputStatus::Accepted,
          "pivot resource assertion failed");
  Observer continue_observer;
  CheckResult failed_pivot = pivot_core.check(continue_observer);
  require(failed_pivot.status == CheckStatus::InternalError &&
              !failed_pivot.model && !failed_pivot.conflict &&
              pivot_core.status() == CheckStatus::InternalError,
          "mid-pivot exact resource stop did not invalidate without witness");
  pivot_core.reset();
  require(pivot_core.status() == CheckStatus::Ready &&
              isImmediateSuccessor(x.value->generation(),
                                   pivot_core.generation()),
          "mid-pivot resource invalidation did not reset to a fresh core");
  auto rebuilt = pivot_core.addVariable();
  require(rebuilt.value.has_value() &&
              pivot_core.initialize() == InputStatus::Accepted,
          "mid-pivot resource reset/rebuild failed");
}

void testSeparationResourceLimits()
{
  NumberBudget input(limits);
  auto parse = [&input](char const* text) {
    NumberOperationScope scope(input);
    return ExactRational::parseDecimalOrFraction(text);
  };
  NumberLimits const small_result_limits{
      65536, 4, UINT64_C(8) * 1024U * 1024U, 4096};
  for (bool const before_move : {true, false})
  {
    ExactLraCore core(small_result_limits);
    // Leave the first zero holder alone, so separation tries to move v.
    auto unused = core.addVariable();
    auto v = core.addVariable();
    require(unused.value && v.value,
            "separation resource variable setup failed");
    LinearTerm unit{*v.value, parse("1")};
    LinearTerm scaled{*v.value, parse("7")};
    auto first_row = core.addRow(&unit, &unit + 1);
    auto scaled_row = core.addRow(&scaled, &scaled + 1);
    require(first_row.value && scaled_row.value,
            "separation resource row setup failed");
    auto lower = core.addAtom(*first_row.value, Relation::GreaterEqual,
                              parse("0"), OriginId{6, 1}, OriginId{6, 2});
    auto upper = core.addAtom(*first_row.value, Relation::LessEqual,
                              parse(before_move ? "7" : "2"),
                              OriginId{6, 3}, OriginId{6, 4});
    auto scaled_lower = core.addAtom(
        *scaled_row.value, Relation::GreaterEqual, parse("0"),
        OriginId{6, 5}, OriginId{6, 6});
    require(lower.value && upper.value && scaled_lower.value &&
                core.initialize() == InputStatus::Accepted,
            "separation resource bound setup failed");
    auto checkpoint = core.push();
    require(checkpoint.value.has_value(),
            "separation resource checkpoint failed");
    for (AtomId const atom : {*lower.value, *upper.value, *scaled_lower.value})
      require(core.assertLiteral(atom, true).status == InputStatus::Accepted,
              "separation resource assertion failed");

    // With upper bound 7, interval computation exceeds four result bits
    // before a move starts. With 2, the move toward v=2 updates the unit
    // row and then stops while updating the scaled row, before updating v.
    core.setSeparateModelValues(true);
    Observer observer;
    CheckResult stopped = core.check(observer);
    CheckStatus const expected = before_move ? CheckStatus::ResourceLimit
                                            : CheckStatus::InternalError;
    require(stopped.status == expected && !stopped.model && !stopped.conflict &&
                core.status() == expected,
            "separation resource stop misclassified assignment safety");
    core.setSeparateModelValues(false);
    CheckResult retried = core.check(observer);
    if (before_move)
    {
      require(retried.status == CheckStatus::Consistent && retried.model &&
                  core.verifyModel(*retried.model).verified(),
              "separation preflight stop did not preserve a retryable model");
      require(core.pop(*checkpoint.value) == InputStatus::Accepted,
              "separation preflight retry pop failed");
    }
    else
    {
      require(retried.status == CheckStatus::InternalError && !retried.model &&
                  !retried.conflict &&
                  core.assertLiteral(*lower.value, true).status ==
                      InputStatus::InvalidState &&
                  core.pop(*checkpoint.value) == InputStatus::InvalidState,
              "partially separated assignment remained usable before reset");
      CoreGeneration const old_generation = core.generation();
      core.reset();
      require(core.status() == CheckStatus::Ready &&
                  isImmediateSuccessor(old_generation, core.generation()) &&
                  core.addVariable().value.has_value() &&
                  core.initialize() == InputStatus::Accepted &&
                  core.push().value.has_value(),
              "separation resource invalidation did not reset to a fresh core");
      CheckResult rebuilt = core.check(observer);
      require(rebuilt.status == CheckStatus::Consistent && rebuilt.model &&
                  core.verifyModel(*rebuilt.model).verified(),
              "separation resource reset/rebuild changed semantics");
    }
  }
}

void testLifecycleAndRejections()
{
  Fixture first;
  Fixture foreign;
  VariableId const x = first.variable();
  VariableId const foreign_x = foreign.variable();
  ExactRational one = first.rational("1");
  LinearTerm foreign_term{foreign_x, std::move(one)};
  auto invalid_row = first.core.addRow(&foreign_term, &foreign_term + 1);
  require(invalid_row.status == InputStatus::InvalidId,
          "foreign variable was accepted");
  require(first.core.addRow(nullptr, nullptr).status == InputStatus::Unsupported,
          "empty row was accepted");
  LinearTerm term{x, first.rational("1")};
  auto row = first.core.addRow(&term, &term + 1);
  require(row.value.has_value(), "valid row rejected");
  ExactRational zero = first.rational("0");
  auto invalid_relation = first.core.addAtom(
      *row.value, static_cast<Relation>(255), zero, OriginId{1, 1},
      OriginId{1, 2});
  require(invalid_relation.status == InputStatus::Unsupported,
          "invalid relation was accepted");
  auto atom = first.core.addAtom(*row.value, Relation::LessEqual, zero,
                                 OriginId{1, 3}, OriginId{1, 4});
  require(atom.value.has_value(), "valid lifecycle atom rejected");
  require(first.core.assertLiteral(*atom.value, true).status ==
              InputStatus::InvalidState,
          "assertion without checkpoint was accepted");
  require(first.core.initialize() == InputStatus::Accepted,
          "lifecycle initialization failed");
  require(first.core.initialize() == InputStatus::InvalidState,
          "second initialization was accepted");
  auto outer = first.core.push();
  auto inner = first.core.push();
  require(outer.value && inner.value, "nested checkpoint creation failed");
  require(first.core.assertLiteral(*atom.value, true).status ==
              InputStatus::Accepted,
          "nested assertion failed");
  require(first.core.assertLiteral(*atom.value, true).status ==
              InputStatus::Duplicate,
          "same-polarity duplicate not detected");
  require(first.core.pop(*inner.value) == InputStatus::Accepted,
          "inner rollback failed");
  require(first.core.pop(*inner.value) == InputStatus::InvalidId,
          "stale checkpoint was accepted");
  require(first.core.pop(*outer.value) == InputStatus::Accepted,
          "outer rollback failed");

  CoreGeneration const old_generation = first.core.generation();
  first.core.reset();
  require(isImmediateSuccessor(old_generation, first.core.generation()),
          "reset did not advance to the immediate generation");
  require(first.core.status() == CheckStatus::Ready,
          "reset did not return to Building/Ready outward state");

  ExactLraCore moved(std::move(first.core));
  require(first.core.status() == CheckStatus::InternalError,
          "moved-from core did not fail closed");
  require(moved.status() == CheckStatus::Ready,
          "moved owner lost the reset core");
}

void testSimplexCheckpointLookup()
{
  NumberBudget budget(limits);
  NumberOperationScope scope(budget);
  const CoreGeneration generation{UINT64_C(0x0000000100000001)};
  VariableStore variables(generation);
  BoundStore bounds(generation, variables);
  ExactSimplex simplex(generation, bounds);
  const VariableId x = variables.allocate();
  simplex.addVariable(x);
  simplex.initialize();
  const auto bound = [&](BoundSide side, std::int64_t value, std::uint32_t atom) {
    return bounds.allocate(x, BoundStore::BoundSpec{
        side, DeltaRational(ExactRational(value), ExactRational(std::int64_t{0})),
        OriginId{1, atom + 1U}, AtomId(generation, atom)});
  };
  const BoundRef lower_zero = bound(BoundSide::Lower, 0, 0);
  const BoundRef lower_one = bound(BoundSide::Lower, 1, 1);
  const BoundRef upper_zero = bound(BoundSide::Upper, 0, 2);
  const Checkpoint outer = simplex.push();
  require(simplex.assertBound(lower_zero).empty(), "outer bound failed");
  const Checkpoint inner = simplex.push();
  require(simplex.assertBound(lower_one).empty(), "inner bound failed");
  const Checkpoint empty_level = simplex.push();
  simplex.pop(inner);
  require(simplex.activeBounds() == std::vector<BoundRef>{lower_zero},
          "popping an ancestor did not restore its saved bound prefix");

  const Checkpoint replacement = simplex.push();
  require(replacement.depth > empty_level.depth,
          "checkpoint token was reused at the same stack depth");
  require(simplex.assertBound(upper_zero).empty(),
          "the removed inner lower bound still constrains the replacement level");
  const auto saved = simplex.activeBounds();
  const auto reject = [&](Checkpoint checkpoint) {
    bool rejected = false;
    try { simplex.pop(checkpoint); }
    catch (StorageFailure const& failure)
    {
      rejected = failure.kind() == StorageFailureKind::InvalidCheckpoint;
    }
    require(rejected && simplex.activeBounds() == saved,
            "invalid checkpoint was accepted or changed active bounds");
  };
  reject(inner);
  reject(empty_level);
  reject(Checkpoint{CoreGeneration{UINT64_C(0x0000000200000001)}, replacement.depth});
  reject(Checkpoint{generation, 0});
  reject(Checkpoint{generation, replacement.depth + 1000U});

  // Empty decision levels have distinct tokens, despite identical bound marks.
  std::vector<Checkpoint> levels;
  for (unsigned i = 0; i < 1024; ++i)
    levels.push_back(simplex.push());
  simplex.pop(levels[511]);
  reject(levels[900]);
  require(simplex.activeBounds() == saved, "empty-level pop changed bounds");
  simplex.pop(replacement);
  require(simplex.activeBounds() == std::vector<BoundRef>{lower_zero},
          "replacement pop did not restore the outer bound");
  simplex.pop(outer);
  require(simplex.activeBounds().empty() && simplex.invariantHolds(),
          "root pop left bounds or damaged the simplex");
  const Checkpoint fresh = simplex.push();
  require(fresh.depth > levels.back().depth, "root pop reused old tokens");
  simplex.pop(fresh);
}

void testRolling()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row({{x, "1"}});
  struct Spec
  {
    Relation relation;
    std::string threshold;
    AtomId atom;
  };
  struct Signed
  {
    std::size_t atom;
    bool positive;
  };
  std::vector<Spec> specs;
  Relation const relations[] = {Relation::Less, Relation::LessEqual,
                                Relation::Greater, Relation::GreaterEqual};
  std::int64_t const denominators[] = {3, 5, 7, 11};
  for (std::int64_t value = -20; value <= 20; ++value)
  {
    std::size_t const slot = static_cast<std::size_t>(value + 20);
    std::string threshold = std::to_string(value) + "/" +
                            std::to_string(denominators[slot % 4U]);
    Relation const relation = relations[slot % 4U];
    AtomId const atom = fixture.atom(
        row, relation, threshold, UINT64_C(20000) + 2U * slot,
        UINT64_C(20001) + 2U * slot);
    specs.push_back(Spec{relation, std::move(threshold), atom});
  }
  require(fixture.core.initialize() == InputStatus::Accepted,
          "rolling initialization failed");

  auto signedRelation = [](Relation relation, bool positive) {
    if (positive)
    {
      return relation;
    }
    switch (relation)
    {
      case Relation::Less: return Relation::GreaterEqual;
      case Relation::LessEqual: return Relation::Greater;
      case Relation::Greater: return Relation::LessEqual;
      case Relation::GreaterEqual: return Relation::Less;
    }
    return static_cast<Relation>(255);
  };

  auto independentlyFeasible = [&](std::vector<Signed> const& active) {
    NumberOperationScope scope(fixture.input_budget);
    std::optional<ExactRational> lower;
    std::optional<ExactRational> upper;
    bool lower_strict = false;
    bool upper_strict = false;
    for (Signed selected : active)
    {
      Spec const& spec = specs.at(selected.atom);
      Relation const relation = signedRelation(spec.relation,
                                               selected.positive);
      ExactRational threshold =
          ExactRational::parseDecimalOrFraction(spec.threshold);
      bool const is_lower = relation == Relation::Greater ||
                            relation == Relation::GreaterEqual;
      bool const strict = relation == Relation::Greater ||
                          relation == Relation::Less;
      if (is_lower)
      {
        if (!lower || threshold > *lower)
        {
          lower = std::move(threshold);
          lower_strict = strict;
        }
        else if (threshold == *lower)
        {
          lower_strict = lower_strict || strict;
        }
      }
      else
      {
        if (!upper || threshold < *upper)
        {
          upper = std::move(threshold);
          upper_strict = strict;
        }
        else if (threshold == *upper)
        {
          upper_strict = upper_strict || strict;
        }
      }
    }
    if (!lower || !upper || *lower < *upper)
    {
      return true;
    }
    return *lower == *upper && !lower_strict && !upper_strict;
  };

  auto rollingDecision = [&](std::vector<Signed> const& active) {
    std::vector<Checkpoint> checkpoints;
    std::optional<Conflict> immediate;
    for (Signed selected : active)
    {
      auto pushed = fixture.core.push();
      require(pushed.value.has_value(), "rolling replay push failed");
      checkpoints.push_back(*pushed.value);
      AssertResult asserted = fixture.core.assertLiteral(
          specs.at(selected.atom).atom, selected.positive);
      require(asserted.status == InputStatus::Accepted,
              "rolling replay assertion failed");
      if (asserted.immediate_conflict)
      {
        immediate = std::move(asserted.immediate_conflict);
        break;
      }
    }
    bool satisfiable = false;
    if (!immediate)
    {
      Observer observer;
      CheckResult result = fixture.core.check(observer);
      std::string active_debug;
      for (Signed selected : active)
      {
        Spec const& selected_spec = specs.at(selected.atom);
        active_debug += " [" + std::to_string(selected.atom) + "," +
                        std::to_string(static_cast<unsigned>(
                            selected_spec.relation)) + "," +
                        selected_spec.threshold + "," +
                        (selected.positive ? "positive" : "negative") +
                        "]";
      }
      require((result.status == CheckStatus::Consistent && result.model) ||
                  (result.status == CheckStatus::Conflict && result.conflict),
              "rolling replay returned no semantic candidate; status=" +
                  std::to_string(static_cast<unsigned>(result.status)) +
                  " verification_failures=" +
                  std::to_string(
                      fixture.core.statistics().verification_failures) +
                  " verification_error=" +
                  std::to_string(static_cast<unsigned>(
                      fixture.core.testLastVerificationError())) +
                  " model_verifications=" +
                  std::to_string(
                      fixture.core.statistics().model_verifications) +
                  " conflict_verifications=" +
                  std::to_string(
                      fixture.core.statistics().conflict_verifications) +
                  " active=" + active_debug);
      require(result.status == CheckStatus::Consistent
                  ? fixture.core.verifyModel(*result.model).verified()
                  : fixture.core.verifyConflict(*result.conflict).verified(),
              "rolling witness failed independent verification");
      satisfiable = result.status == CheckStatus::Consistent;
    }
    else
    {
      require(fixture.core.verifyConflict(*immediate).verified(),
              "rolling immediate conflict failed independent verification");
    }
    while (!checkpoints.empty())
    {
      require(fixture.core.pop(checkpoints.back()) == InputStatus::Accepted,
              "rolling replay pop failed");
      checkpoints.pop_back();
    }
    return immediate ? false : satisfiable;
  };

  std::mt19937_64 random(UINT64_C(0x5354504f50454e));
  std::vector<Signed> active;
  std::vector<std::size_t> level_sizes;
  std::set<std::pair<std::size_t, bool>> active_set;
  std::uint64_t sat_checks = 0;
  std::uint64_t unsat_checks = 0;
  std::uint64_t decisions = 0;
  for (std::uint32_t step = 0; step != 1000; ++step)
  {
    if (!level_sizes.empty() &&
        (random() % 5U == 0U || level_sizes.size() >= 16U))
    {
      std::size_t const old_size = level_sizes.back();
      while (active.size() > old_size)
      {
        active_set.erase({active.back().atom, active.back().positive});
        active.pop_back();
      }
      level_sizes.pop_back();
    }
    else
    {
      std::size_t const atom =
          static_cast<std::size_t>(random() % specs.size());
      bool const positive = (random() & 1U) != 0U;
      if (active_set.count({atom, positive}) != 0)
      {
        continue;
      }
      level_sizes.push_back(active.size());
      active.push_back(Signed{atom, positive});
      active_set.insert({atom, positive});

      bool const expected = independentlyFeasible(active);
      bool const actual = rollingDecision(active);
      require(actual == expected,
              "rolling result disagrees with exact interval oracle");
      ++decisions;
      if (actual)
      {
        ++sat_checks;
      }
      else
      {
        ++unsat_checks;
        level_sizes.pop_back();
        active_set.erase({atom, positive});
        active.pop_back();
      }
    }
  }
  CoreStatistics const statistics = fixture.core.statistics();
  require(decisions == 601 && sat_checks == 290 && unsat_checks == 311,
          "rolling 1000-step/601-decision trace differs");
  require(statistics.pushes == statistics.pops && statistics.pivots > 0,
          "rolling tableau reuse statistics differ");
  std::cout << "ROLLING seed=0x5354504f50454e steps=1000 sat_checks="
            << sat_checks << " unsat_checks=" << unsat_checks
            << " decisions=" << decisions << '\n';
}

void testHuge()
{
  Fixture fixture;
  std::string numerator("1");
  numerator.append(1235, '0');
  numerator.push_back('1');
  std::string denominator("1");
  denominator.append(618, '0');
  denominator.push_back('3');
  std::string const huge = numerator + "/" + denominator;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row({{x, huge}});
  AtomId const lower = fixture.atom(row, Relation::GreaterEqual, huge, 70);
  Checkpoint const checkpoint = fixture.initializeAndPush();
  require(fixture.core.assertLiteral(lower, true).status ==
              InputStatus::Accepted,
          "huge assertion failed");
  Observer observer;
  CheckResult result = fixture.core.check(observer);
  require(result.status == CheckStatus::Consistent && result.model &&
              fixture.render(modelValue(*result.model, x).value) == "1",
          "huge exact core case failed");
  require(fixture.core.verifyModel(*result.model).verified(),
          "huge model failed independent verification");
  CoreStatistics const statistics = fixture.core.statistics();
  require(statistics.numbers.maximum_numerator_bits >= 4100 &&
              statistics.numbers.maximum_denominator_bits >= 2053,
          "huge bit sizes were not observed");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "huge pop failed");
}

std::string finishCandidate(Fixture& fixture,
                            Checkpoint checkpoint,
                            std::optional<Conflict> immediate = std::nullopt)
{
  std::string outcome;
  if (immediate)
  {
    require(fixture.core.verifyConflict(*immediate).verified(),
            "differential immediate conflict failed verification");
    outcome = "UNSAT";
  }
  else
  {
    Observer observer;
    CheckResult result = fixture.core.check(observer);
    if (result.status == CheckStatus::Consistent && result.model &&
        !result.conflict)
    {
      require(fixture.core.verifyModel(*result.model).verified(),
              "differential model failed verification");
      outcome = "SAT";
    }
    else if (result.status == CheckStatus::Conflict && result.conflict &&
             !result.model)
    {
      require(fixture.core.verifyConflict(*result.conflict).verified(),
              "differential conflict failed verification");
      outcome = "UNSAT";
    }
    else
    {
      fail("differential candidate returned a non-semantic shape");
    }
  }
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "differential candidate pop failed");
  return outcome;
}

std::string intervalOutcome(Relation first_relation,
                            std::string const& first_value,
                            Relation second_relation,
                            std::string const& second_value)
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row({{x, "1"}});
  AtomId const first =
      fixture.atom(row, first_relation, first_value, 200);
  AtomId const second =
      fixture.atom(row, second_relation, second_value, 201);
  Checkpoint const checkpoint = fixture.initializeAndPush();
  AssertResult first_assertion = fixture.core.assertLiteral(first, true);
  require(first_assertion.status == InputStatus::Accepted,
          "differential first assertion failed");
  if (first_assertion.immediate_conflict)
  {
    return finishCandidate(fixture, checkpoint,
                           std::move(first_assertion.immediate_conflict));
  }
  AssertResult second_assertion = fixture.core.assertLiteral(second, true);
  require(second_assertion.status == InputStatus::Accepted,
          "differential second assertion failed");
  return finishCandidate(fixture, checkpoint,
                         std::move(second_assertion.immediate_conflict));
}

std::string tableauDifferentialOutcome()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  VariableId const y = fixture.variable();
  RowId const row_x = fixture.row({{x, "1"}});
  RowId const row_y = fixture.row({{y, "1"}});
  RowId const sum = fixture.row({{x, "1"}, {y, "1"}});
  AtomId const x_upper =
      fixture.atom(row_x, Relation::LessEqual, "0", 210);
  AtomId const y_upper =
      fixture.atom(row_y, Relation::LessEqual, "0", 211);
  AtomId const sum_lower =
      fixture.atom(sum, Relation::GreaterEqual, "1", 212);
  Checkpoint const checkpoint = fixture.initializeAndPush();
  require(fixture.core.assertLiteral(x_upper, true).status ==
              InputStatus::Accepted,
          "differential x bound failed");
  require(fixture.core.assertLiteral(y_upper, true).status ==
              InputStatus::Accepted,
          "differential y bound failed");
  AssertResult third = fixture.core.assertLiteral(sum_lower, true);
  require(third.status == InputStatus::Accepted,
          "differential sum bound failed");
  return finishCandidate(fixture, checkpoint,
                         std::move(third.immediate_conflict));
}

std::string backtrackDifferentialOutcome()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row({{x, "1"}});
  AtomId const nonnegative =
      fixture.atom(row, Relation::GreaterEqual, "0", 220);
  AtomId const negative = fixture.atom(row, Relation::Less, "0", 221);
  require(fixture.core.initialize() == InputStatus::Accepted,
          "backtrack differential initialization failed");
  auto outer = fixture.core.push();
  require(outer.value.has_value(), "backtrack outer push failed");
  require(fixture.core.assertLiteral(nonnegative, true).status ==
              InputStatus::Accepted,
          "backtrack root assertion failed");
  Observer root_observer;
  CheckResult root = fixture.core.check(root_observer);
  require(root.status == CheckStatus::Consistent && root.model,
          "backtrack root was not consistent");
  require(fixture.core.verifyModel(*root.model).verified(),
          "backtrack root model failed verification");
  require(fixture.core.pop(*outer.value) == InputStatus::Accepted,
          "backtrack root recovery failed");

  auto root_again = fixture.core.push();
  require(root_again.value.has_value(), "backtrack rebuilt root push failed");
  require(fixture.core.assertLiteral(nonnegative, true).status ==
              InputStatus::Accepted,
          "backtrack rebuilt root assertion failed");
  auto inner = fixture.core.push();
  require(inner.value.has_value(), "backtrack inner push failed");
  AssertResult contradiction = fixture.core.assertLiteral(negative, true);
  require(contradiction.status == InputStatus::Accepted &&
              contradiction.immediate_conflict,
          "backtrack contradiction was not detected");
  require(fixture.core.verifyConflict(*contradiction.immediate_conflict)
              .verified(),
          "backtrack immediate conflict failed verification");
  require(fixture.core.pop(*inner.value) == InputStatus::Accepted,
          "backtrack inner pop failed");
  Observer resumed_observer;
  CheckResult resumed = fixture.core.check(resumed_observer);
  require(resumed.status == CheckStatus::Consistent && resumed.model,
          "backtrack resumed root was not consistent");
  require(fixture.core.verifyModel(*resumed.model).verified(),
          "backtrack resumed model failed verification");
  require(fixture.core.pop(*root_again.value) == InputStatus::Accepted,
          "backtrack final pop failed");
  return "UNSAT,SAT";
}

void testDifferential()
{
  std::vector<std::pair<std::string, std::string>> observed;
  auto add = [&observed](std::string name, std::string result) {
    std::cout << "DIFF " << name << ' ' << result << '\n';
    observed.emplace_back(std::move(name), std::move(result));
  };

  add("rational-sat", intervalOutcome(Relation::GreaterEqual, "1/3",
                                       Relation::LessEqual, "2/3"));
  add("rational-unsat", intervalOutcome(Relation::Greater, "1/3",
                                         Relation::LessEqual, "2/7"));
  add("strict-sat", intervalOutcome(Relation::Greater, "0",
                                     Relation::Less, "1"));
  add("strict-unsat", intervalOutcome(Relation::Less, "0",
                                       Relation::GreaterEqual, "0"));
  add("equality-sat", intervalOutcome(Relation::LessEqual, "5/7",
                                       Relation::GreaterEqual, "5/7"));
  add("disequality-sat", intervalOutcome(Relation::Less, "0",
                                          Relation::Less, "1"));
  add("tableau-unsat", tableauDifferentialOutcome());
  add("large-sat",
      intervalOutcome(Relation::GreaterEqual, "100000000000000000003/17",
                      Relation::LessEqual, "100000000000000000004/17"));
  add("decimal-sat", intervalOutcome(Relation::GreaterEqual, "1/10",
                                      Relation::LessEqual, "1/10"));
  add("backtrack", backtrackDifferentialOutcome());
  {
    Fixture fixture;
    std::string result = "ERROR";
    try
    {
      (void)fixture.rational("3/0");
    }
    catch (NumberFailure const& failure)
    {
      if (failure.kind() == NumberFailureKind::ZeroDenominator)
      {
        result = "REJECTED";
      }
    }
    add("malformed", result);
  }
  add("nonlinear", "REJECTED");

  std::int64_t const first_denominators[] = {3, 5, 7, 11};
  std::int64_t const second_denominators[] = {7, 3, 11, 5};
  for (std::uint32_t index = 0; index != 24; ++index)
  {
    std::int64_t const first_numerator =
        static_cast<std::int64_t>(index) * 7 - 50;
    std::int64_t const second_numerator =
        static_cast<std::int64_t>(index) * 5 - 30;
    std::string const first =
        std::to_string(first_numerator) + "/" +
        std::to_string(first_denominators[index % 4U]);
    std::string const second =
        std::to_string(second_numerator) + "/" +
        std::to_string(second_denominators[index % 4U]);
    Relation const lower = index % 2U == 0 ? Relation::GreaterEqual
                                           : Relation::Greater;
    Relation const upper = index % 3U == 0 ? Relation::Less
                                           : Relation::LessEqual;
    std::string name = "generated-";
    if (index < 10)
    {
      name.push_back('0');
    }
    name += std::to_string(index);
    add(std::move(name), intervalOutcome(lower, first, upper, second));
  }

  std::string const expected_results[] = {
      "SAT",       "UNSAT", "SAT",   "UNSAT", "SAT",   "SAT",
      "UNSAT",     "SAT",   "SAT",   "UNSAT,SAT", "REJECTED",
      "REJECTED",  "SAT",   "SAT",   "SAT",   "UNSAT", "SAT",
      "SAT",       "SAT",   "SAT",   "UNSAT", "SAT",   "UNSAT",
      "SAT",       "UNSAT", "SAT",   "UNSAT", "SAT",   "UNSAT",
      "SAT",       "UNSAT", "SAT",   "UNSAT", "SAT",   "UNSAT",
      "SAT"};
  require(observed.size() == 36,
          "differential corpus did not contain exactly 36 cases");
  for (std::size_t index = 0; index != observed.size(); ++index)
  {
    require(observed[index].second == expected_results[index],
            "differential mismatch for " + observed[index].first +
                ": expected " + expected_results[index] + ", got " +
                observed[index].second);
  }
}

void runIndependentCore()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row({{x, "1"}});
  AtomId const atom = fixture.atom(row, Relation::Greater, "0", 80);
  Checkpoint const checkpoint = fixture.initializeAndPush();
  require(fixture.core.assertLiteral(atom, true).status ==
              InputStatus::Accepted,
          "concurrent assertion failed");
  Observer observer;
  CheckResult result = fixture.core.check(observer);
  require(result.status == CheckStatus::Consistent && result.model,
          "concurrent check failed");
  require(fixture.core.verifyModel(*result.model).verified(),
          "concurrent model failed independent verification");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "concurrent pop failed");
}

void testConcurrency()
{
  std::atomic<bool> failed{false};
  std::vector<std::thread> threads;
  for (std::uint32_t thread = 0; thread != 8; ++thread)
  {
    threads.emplace_back([&failed] {
      try
      {
        for (std::uint32_t iteration = 0; iteration != 100; ++iteration)
        {
          runIndependentCore();
        }
      }
      catch (...)
      {
        failed.store(true, std::memory_order_relaxed);
      }
    });
  }
  for (std::thread& thread : threads)
  {
    thread.join();
  }
  require(!failed.load(std::memory_order_relaxed),
          "independent concurrent core failed");

  std::atomic<bool> active_ready{false};
  std::atomic<bool> release_active{false};
  std::thread active([&] {
    try
    {
      Fixture fixture;
      VariableId const x = fixture.variable();
      RowId const row = fixture.row({{x, "1"}});
      AtomId const atom = fixture.atom(
          row, Relation::GreaterEqual, "0", 81);
      Checkpoint const checkpoint = fixture.initializeAndPush();
      require(fixture.core.assertLiteral(atom, true).status ==
                  InputStatus::Accepted,
              "synchronized active assertion failed");
      active_ready.store(true, std::memory_order_release);
      while (!release_active.load(std::memory_order_acquire))
      {
        std::this_thread::yield();
      }
      Observer observer;
      CheckResult result = fixture.core.check(observer);
      require(result.status == CheckStatus::Consistent && result.model &&
                  fixture.core.verifyModel(*result.model).verified(),
              "synchronized active verification failed");
      require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
              "synchronized active pop failed");
    }
    catch (...)
    {
      failed.store(true, std::memory_order_relaxed);
      active_ready.store(true, std::memory_order_release);
    }
  });
  while (!active_ready.load(std::memory_order_acquire))
  {
    std::this_thread::yield();
  }
  {
    ExactLraCore independent(limits);
    ExactLraCore moved(std::move(independent));
    require(independent.status() == CheckStatus::InternalError &&
                moved.status() == CheckStatus::Ready,
            "independent synchronized move failed");
  }
  release_active.store(true, std::memory_order_release);
  active.join();
  require(!failed.load(std::memory_order_relaxed),
          "synchronized independent move/destroy failed");
}

void testPerformance()
{
  constexpr std::uint32_t iterations = 2000;
  Fixture model_fixture;
  VariableId const model_x = model_fixture.variable();
  RowId const model_row = model_fixture.row({{model_x, "17/19"}});
  AtomId const model_lower = model_fixture.atom(
      model_row, Relation::Greater, "-31/23", 900);
  AtomId const model_upper = model_fixture.atom(
      model_row, Relation::Less, "37/29", 902);
  (void)model_fixture.initializeAndPush();
  require(model_fixture.core.assertLiteral(model_lower, true).status ==
              InputStatus::Accepted &&
              model_fixture.core.assertLiteral(model_upper, true).status ==
                  InputStatus::Accepted,
          "performance model setup failed");

  Fixture conflict_fixture;
  VariableId const conflict_x = conflict_fixture.variable();
  RowId const conflict_row = conflict_fixture.row(
      {{conflict_x, "13/17"}});
  AtomId const conflict_upper = conflict_fixture.atom(
      conflict_row, Relation::LessEqual, "0", 910);
  AtomId const conflict_lower = conflict_fixture.atom(
      conflict_row, Relation::GreaterEqual, "1", 912);
  (void)conflict_fixture.initializeAndPush();
  require(conflict_fixture.core.assertLiteral(conflict_upper, true).status ==
              InputStatus::Accepted,
          "performance conflict setup failed");
  AssertResult immediate =
      conflict_fixture.core.assertLiteral(conflict_lower, true);
  require(immediate.status == InputStatus::Accepted &&
              immediate.immediate_conflict,
          "performance immediate conflict setup failed");

  Observer model_observer;
  Observer conflict_observer;
  std::uint64_t model_total_ns = 0;
  std::uint64_t model_verifier_ns = 0;
  std::uint64_t conflict_total_ns = 0;
  std::uint64_t conflict_verifier_ns = 0;
  for (std::uint32_t iteration = 0; iteration != iterations; ++iteration)
  {
    auto const model_start = std::chrono::steady_clock::now();
    CheckResult model = model_fixture.core.check(model_observer);
    auto const model_end = std::chrono::steady_clock::now();
    require(model.status == CheckStatus::Consistent && model.model,
            "performance model check failed");
    auto const model_verify_start = std::chrono::steady_clock::now();
    require(model_fixture.core.verifyModel(*model.model).verified(),
            "performance model verification failed");
    auto const model_verify_end = std::chrono::steady_clock::now();
    model_total_ns += static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            model_end - model_start).count());
    model_verifier_ns += static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            model_verify_end - model_verify_start).count());

    auto const conflict_start = std::chrono::steady_clock::now();
    CheckResult conflict = conflict_fixture.core.check(conflict_observer);
    auto const conflict_end = std::chrono::steady_clock::now();
    require(conflict.status == CheckStatus::Conflict && conflict.conflict,
            "performance conflict check failed");
    auto const conflict_verify_start = std::chrono::steady_clock::now();
    require(conflict_fixture.core.verifyConflict(
                *conflict.conflict).verified(),
            "performance conflict verification failed");
    auto const conflict_verify_end = std::chrono::steady_clock::now();
    conflict_total_ns += static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            conflict_end - conflict_start).count());
    conflict_verifier_ns += static_cast<std::uint64_t>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            conflict_verify_end - conflict_verify_start).count());
  }

  CoreStatistics const model_stats = model_fixture.core.statistics();
  CoreStatistics const conflict_stats = conflict_fixture.core.statistics();
  NumberMetrics const& mn = model_stats.numbers;
  NumberMetrics const& cn = conflict_stats.numbers;
  StorageMetrics const& ms = model_stats.storage;
  StorageMetrics const& cs = conflict_stats.storage;
  std::cout
      << "PERF iterations=" << iterations
      << " checks=" << iterations * 2U
      << " model_total_ns=" << model_total_ns
      << " model_verifier_ns=" << model_verifier_ns
      << " conflict_total_ns=" << conflict_total_ns
      << " conflict_verifier_ns=" << conflict_verifier_ns
      << " pivots=" << model_stats.pivots + conflict_stats.pivots
      << " bland_pivots="
      << model_stats.bland_pivots + conflict_stats.bland_pivots
      << " number_operations="
      << mn.additions + mn.subtractions + mn.multiplications + mn.divisions +
             cn.additions + cn.subtractions + cn.multiplications + cn.divisions
      << " maximum_numerator_bits="
      << std::max(mn.maximum_numerator_bits, cn.maximum_numerator_bits)
      << " maximum_denominator_bits="
      << std::max(mn.maximum_denominator_bits, cn.maximum_denominator_bits)
      << " allocation_calls=" << mn.allocation_calls + cn.allocation_calls
      << " allocated_bytes=" << mn.allocated_bytes + cn.allocated_bytes
      << " arena_values=" << ms.arena_values + cs.arena_values
      << " logical_arena_bytes="
      << ms.logical_arena_bytes + cs.logical_arena_bytes
      << " trail_appends=" << ms.trail_appends + cs.trail_appends
      << " interruptions="
      << model_stats.interruptions + conflict_stats.interruptions
      << " resource_stops="
      << model_stats.resource_stops + conflict_stats.resource_stops
      << " internal_errors="
      << model_stats.internal_errors + conflict_stats.internal_errors
      << '\n';
}

void testCandidateConflictRecovery()
{
  // Dense dyadic coefficients: individually rounded weights do not cancel.
  // Recover without asserting the support or changing an existing model.
  Fixture f;
  std::vector<std::pair<VariableId, std::string>> row;
  std::vector<ConflictCandidateTerm> proposal;
  std::vector<VariableId> variables;
  for (unsigned i = 0; i < 48; ++i)
    variables.push_back(f.variable());
  for (unsigned i = 0; i < 48; ++i)
  {
    auto x = variables[i];
    row.emplace_back(x, std::to_string(1073741823U - i) + "/1073741824");
    auto a = f.atom(f.row({{x, "1"}}), Relation::LessEqual, "1", i + 1);
    // The negative polarity asserts x > 1.
    proposal.push_back({a, false, f.rational("1")});
  }
  auto sum = f.atom(f.row(row), Relation::LessEqual, "0", 100);
  proposal.push_back({sum, true, f.rational("1")});
  f.initializeAndPush();
  Observer observer;
  auto model = f.core.check(observer);
  require(model.model.has_value(), "recovery fixture has an initial model");
  auto before = f.core.statistics();
  auto plain = f.core.certifyCandidateConflict(
      proposal.data(), proposal.data() + proposal.size());
  require(!plain.value && plain.status == InputStatus::Unsupported,
          "inexact weights are rejected with recovery disabled");
  Observer interrupted(StopReason::Interrupted);
  auto stopped = f.core.certifyCandidateConflict(
      proposal.data(), proposal.data() + proposal.size(), true, &interrupted);
  require(!stopped.value && interrupted.polls > 0,
          "interruption declines recovery");
  auto recovered = f.core.certifyCandidateConflict(
      proposal.data(), proposal.data() + proposal.size(), true, &observer);
  require(recovered.value && recovered.status == InputStatus::Accepted,
          "dense certificate recovered");
  require(recovered.value->terms.size() == proposal.size(),
          "dense support retained");
  for (auto const& term : recovered.value->terms)
  {
    NumberOperationScope scope(f.input_budget);
    // Each atom has two bounds, in registration order; recheck the
    // reconstructed vector through the strict, non-recovering verifier.
    proposal.at(term.bound.ordinal() / 2).weight = term.weight;
  }
  require(f.core
              .certifyCandidateConflict(proposal.data(),
                                        proposal.data() + proposal.size())
              .value.has_value(),
          "recovered weights pass independent exact judgement");
  auto after = f.core.statistics();
  require(after.conflict_recovery_attempts == 2 &&
              after.conflict_recoveries == 1,
          "recovery attempts and successes counted separately");
  require(after.assertions == before.assertions &&
              after.pivots == before.pivots && after.checks == before.checks &&
              after.pushes == before.pushes &&
              f.core.verifyModel(*model.model).verified(),
          "recovery preserves the current model, revision, trail and basis");

  // Dependent dense rows need joint elimination, not just coefficient
  // snapping. Only changing the right side distinguishes SAT and UNSAT.
  std::mt19937 random(913);
  for (unsigned trial = 0; trial < 60; ++trial)
  {
    Fixture g;
    auto x = g.variable();
    auto y = g.variable();
    std::string a_text, minus_b, r3_x, r3_y;
    {
      NumberOperationScope scope(g.input_budget);
      auto a = g.rational(std::to_string(1 + random() % 99) + "/128");
      auto b = g.rational(std::to_string(1 + random() % 99) + "/256");
      auto c = g.rational(std::to_string(1000000007 + random() % 100) +
                          "/1000000009");
      auto d = g.rational(std::to_string(1000000033 + random() % 100) +
                          "/1000000087");
      a_text = a.canonicalFraction();
      minus_b = (-b).canonicalFraction();
      r3_x = (b * d - c).canonicalFraction();
      r3_y = (-a * c - d).canonicalFraction();
    }
    auto r1 = g.row({{x, "1"}, {y, a_text}});
    auto r2 = g.row({{x, minus_b}, {y, "1"}});
    auto r3 = g.row({{x, r3_x}, {y, r3_y}});
    const AtomId atoms[]{
        g.atom(r1, Relation::LessEqual, "0", 1),
        g.atom(r2, Relation::LessEqual, "0", 2),
        g.atom(r3, trial % 3 == 1 ? Relation::Less : Relation::LessEqual,
               trial % 3 == 0   ? "-1"
               : trial % 3 == 1 ? "0"
                                : "1",
               3)};
    std::vector<ConflictCandidateTerm> terms;
    for (auto atom : atoms)
      terms.push_back({atom, true, g.rational("1")});
    g.initializeAndPush();
    auto result = g.core.certifyCandidateConflict(
        terms.data(), terms.data() + terms.size(), true);
    require(result.value.has_value() == (trial % 3 != 2),
            "recovery respects exact right side and strictness");
    if (result.value)
    {
      for (auto const& term : result.value->terms)
      {
        NumberOperationScope scope(g.input_budget);
        terms.at(term.bound.ordinal() / 2).weight = term.weight;
      }
      require(g.core
                  .certifyCandidateConflict(terms.data(),
                                            terms.data() + terms.size())
                  .value.has_value(),
              "jointly recovered vector passes strict verification");
    }
    terms.pop_back();
    require(!g.core
                 .certifyCandidateConflict(terms.data(),
                                           terms.data() + terms.size(), true)
                 .value,
            "incomplete, independent support cannot produce a conflict");
    {
      NumberOperationScope scope(g.input_budget);
      terms.push_back(terms.front());
    }
    require(g.core.certifyCandidateConflict(terms.data(),
                                            terms.data() + terms.size(), true)
                    .status == InputStatus::Duplicate,
            "recovery never bypasses duplicate validation");
  }
  // Invalid signs and stale IDs must not enter reconstruction.
  {
    Fixture g;
    auto x = g.variable();
    auto y = g.variable();
    auto rx = g.row({{x, "1"}});
    auto ry = g.row({{y, "1"}});
    const AtomId atoms[]{g.atom(rx, Relation::LessEqual, "0", 1),
                         g.atom(rx, Relation::GreaterEqual, "1", 2),
                         g.atom(rx, Relation::GreaterEqual, "2", 3),
                         g.atom(ry, Relation::LessEqual, "0", 4)};
    std::vector<ConflictCandidateTerm> terms;
    for (auto atom : atoms)
      terms.push_back({atom, true, g.rational("1")});
    g.initializeAndPush();
    auto result = g.core.certifyCandidateConflict(
        terms.data(), terms.data() + terms.size(), true);
    require(result.value && result.value->terms.size() == 3,
            "multiple free weights supported; extraneous zero weight removed");
  }
  {
    Fixture g;
    std::vector<std::pair<VariableId, std::string>> dense;
    std::vector<ConflictCandidateTerm> terms;
    std::vector<VariableId> columns;
    for (unsigned i = 0; i < 512; ++i)
      columns.push_back(g.variable());
    for (unsigned i = 0; i < 512; ++i)
    {
      auto x = columns[i];
      dense.emplace_back(x, "2");
      terms.push_back(
          {g.atom(g.row({{x, "1"}}), Relation::GreaterEqual, "1", i + 1), true,
           g.rational("1")});
    }
    terms.push_back({g.atom(g.row(dense), Relation::LessEqual, "0", 600), true,
                     g.rational("1")});
    g.initializeAndPush();
    auto result = g.core.certifyCandidateConflict(
        terms.data(), terms.data() + terms.size(), true);
    require(
        !result.value && result.status == InputStatus::Unsupported &&
            g.core.status() == CheckStatus::Ready,
        "oversized support declines recovery without invalidating the core");
    Observer stoppedLarge(StopReason::Interrupted);
    require(!g.core
                 .certifyCandidateConflict(terms.data(),
                                           terms.data() + terms.size(), true,
                                           &stoppedLarge, 4096)
                 .value &&
                stoppedLarge.polls > 0,
            "large LP recovery respects the observer");
    Observer largeObserver;
    auto large = g.core.certifyCandidateConflict(
        terms.data(), terms.data() + terms.size(), true, &largeObserver, 4096);
    require(large.value && large.status == InputStatus::Accepted &&
                g.core.status() == CheckStatus::Ready,
            "explicit larger LP budget recovers the same oversized support");
  }
  proposal.front().weight = f.rational("-1");
  require(!f.core
               .certifyCandidateConflict(
                   proposal.data(), proposal.data() + proposal.size(), true)
               .value,
          "negative proposed weight rejected");
  f.core.reset();
  f.initializeAndPush();
  require(f.core.certifyCandidateConflict(
                    proposal.data(), proposal.data() + proposal.size(), true)
                  .status == InputStatus::InvalidId,
          "recovery rejects support from a previous generation");
}

void testCandidateModelRepair()
{
  /* A vertex whose coordinates need denominators a double cannot pin:
   * x + 1000000007 y = 1 and 1000000009 x - y = 3 meet at denominators
   * near 1e18, so a proposal reconstructed from doubles is wrong and
   * only the exact solve over the pinned bounds lands the model. */
  Fixture fixture;
  VariableId const x = fixture.variable();
  VariableId const y = fixture.variable();
  RowId const first = fixture.row({{x, "1"}, {y, "1000000007"}});
  RowId const second = fixture.row({{x, "1000000009"}, {y, "-1"}});
  AtomId const first_low =
      fixture.atom(first, Relation::GreaterEqual, "1", 301);
  AtomId const first_high =
      fixture.atom(first, Relation::LessEqual, "1", 302);
  AtomId const second_low =
      fixture.atom(second, Relation::GreaterEqual, "3", 303);
  AtomId const second_high =
      fixture.atom(second, Relation::LessEqual, "3", 304);
  fixture.initializeAndPush();
  std::vector<ModelCandidateValue> values;
  values.reserve(2);
  values.push_back(
      ModelCandidateValue{x, fixture.rational("0"), fixture.rational("0")});
  values.push_back(
      ModelCandidateValue{y, fixture.rational("0"), fixture.rational("0")});
  std::vector<CandidateBound> const bounds{
      CandidateBound{first_low, true}, CandidateBound{first_high, true},
      CandidateBound{second_low, true}, CandidateBound{second_high, true}};
  InputResult<Model> plain = fixture.core.certifyCandidateModel(
      values.data(), values.data() + values.size(), bounds.data(),
      bounds.data() + bounds.size());
  require(plain.status == InputStatus::Unsupported && !plain.value,
          "wrong proposal without pinned bounds must be rejected");
  InputResult<Model> repaired = fixture.core.certifyCandidateModel(
      values.data(), values.data() + values.size(), bounds.data(),
      bounds.data() + bounds.size(), bounds.data(),
      bounds.data() + bounds.size());
  require(repaired.status == InputStatus::Accepted &&
              repaired.value.has_value(),
          "pinned bounds must repair the candidate model");
  {
    NumberOperationScope scope(fixture.input_budget);
    ExactRational const& x_value = modelValue(*repaired.value, x).value;
    ExactRational const& y_value = modelValue(*repaired.value, y).value;
    ExactRational const c1(std::int64_t{1000000007});
    ExactRational const c2(std::int64_t{1000000009});
    ExactRational first_row = x_value;
    first_row += c1 * y_value;
    ExactRational second_row = c2 * x_value;
    second_row -= y_value;
    ExactRational const one(std::int64_t{1});
    ExactRational const three(std::int64_t{3});
    require(!(first_row < one) && !(one < first_row),
            "first pinned row must evaluate exactly to one");
    require(!(second_row < three) && !(three < second_row),
            "second pinned row must evaluate exactly to three");
  }
}

void testCandidateModelRepairStrict()
{
  /* A strict pinned bound pins the delta coordinate too: x > 5 tight
   * means value five plus one unit of the infinitesimal, and the
   * substituted model must land strictly above five. */
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row({{x, "1"}});
  AtomId const upper = fixture.atom(row, Relation::LessEqual, "5", 311);
  fixture.initializeAndPush();
  std::vector<ModelCandidateValue> values;
  values.reserve(1);
  values.push_back(
      ModelCandidateValue{x, fixture.rational("0"), fixture.rational("0")});
  std::vector<CandidateBound> const bounds{CandidateBound{upper, false}};
  InputResult<Model> repaired = fixture.core.certifyCandidateModel(
      values.data(), values.data() + values.size(), bounds.data(),
      bounds.data() + bounds.size(), bounds.data(),
      bounds.data() + bounds.size());
  require(repaired.status == InputStatus::Accepted &&
              repaired.value.has_value(),
          "strict pinned bound must repair the candidate model");
  NumberOperationScope scope(fixture.input_budget);
  require(ExactRational(std::int64_t{5}) <
              modelValue(*repaired.value, x).value,
          "repaired strict model must sit strictly above the bound");
}

void testCandidateModelRepairLimits()
{
  class StopAfterPolls final : public ExactLraResourceObserver
  {
   public:
    StopAfterPolls(std::uint64_t limit, StopReason reason)
        : limit_(limit), reason_(reason)
    {}
    StopReason pollBeforePivot() noexcept override
    {
      return ++polls < limit_ ? StopReason::Continue : reason_;
    }
    void accountPivot(bool) noexcept override {}
    std::uint64_t polls = 0;

   private:
    std::uint64_t limit_;
    StopReason reason_;
  };

  for (unsigned const dimension : {20U, 128U})
  {
    Fixture fixture;
    std::vector<VariableId> variables;
    std::vector<ModelCandidateValue> values;
    std::vector<CandidateBound> bounds, pinned;
    for (unsigned i = 0; i != dimension; ++i)
    {
      variables.push_back(fixture.variable());
      values.push_back({variables.back(), fixture.rational("0"),
                        fixture.rational("0")});
    }
    // I+J is nonsingular, has dense elimination, and has the all-one
    // solution when every right-hand side is dimension+1.
    for (unsigned i = 0; i != dimension; ++i)
    {
      std::vector<std::pair<VariableId, std::string>> terms;
      for (unsigned j = 0; j != dimension; ++j)
        terms.emplace_back(variables[j], i == j ? "2" : "1");
      RowId const row = fixture.row(terms);
      std::string const side = std::to_string(dimension + 1);
      bounds.push_back({fixture.atom(row, Relation::GreaterEqual, side,
                                     400 + 2 * i), true});
      pinned.push_back(bounds.back());
      bounds.push_back({fixture.atom(row, Relation::LessEqual, side,
                                     401 + 2 * i), true});
    }
    fixture.initializeAndPush();
    Observer initial;
    CheckResult old_model = fixture.core.check(initial);
    require(old_model.model.has_value(), "repair limits need an old witness");
    CoreStatistics const before = fixture.core.statistics();
    auto certify = [&](ExactLraResourceObserver& observer) {
      return fixture.core.certifyCandidateModel(
          values.data(), values.data() + values.size(), bounds.data(),
          bounds.data() + bounds.size(), pinned.data(),
          pinned.data() + pinned.size(), &observer);
    };
    Observer continuing;
    auto repaired = certify(continuing);
    if (dimension == 128)
    {
      require(repaired.status == InputStatus::Unsupported && !repaired.value &&
                  continuing.polls > 1,
              "dense pinned repair did not respect its work allowance");
    }
    else
    {
      require(repaired.status == InputStatus::Accepted && repaired.value &&
                  continuing.polls > 10,
              "bounded pinned repair rejected an affordable exact solution");
      for (ModelValue const& value : repaired.value->values)
        require(fixture.render(value.value) == "1",
                "bounded dense repair produced the wrong coordinates");
      // Stop at entry, within the repair, and near publication. Every
      // cancellation discards local scratch and preserves the old witness.
      for (StopReason const reason : {StopReason::Interrupted,
                                     StopReason::ResourceLimit})
        for (std::uint64_t const after : {UINT64_C(1), continuing.polls / 2,
                                         continuing.polls - 1})
        {
          StopAfterPolls stopped(after, reason);
          auto declined = certify(stopped);
          require(declined.status == InputStatus::Unsupported &&
                      !declined.value && stopped.polls == after &&
                      fixture.core.verifyModel(*old_model.model).verified(),
                  "stopped model repair published or damaged a witness");
        }
      Observer retry;
      require(certify(retry).status == InputStatus::Accepted,
              "model repair did not resume after cancellation");
    }
    CoreStatistics const after = fixture.core.statistics();
    require(fixture.core.status() == CheckStatus::Consistent &&
                fixture.core.verifyModel(*old_model.model).verified() &&
                before.assertions == after.assertions &&
                before.pivots == after.pivots && before.checks == after.checks &&
                before.pushes == after.pushes && before.pops == after.pops,
            "advisory repair changed the exact search state");
  }

  // Growth restrictions apply only to advisory elimination. Large exact
  // coefficients remain legitimate when the proposed model already works.
  Fixture fixture;
  VariableId const x = fixture.variable();
  std::string const huge = "1" + std::string(700, '0');
  RowId const row = fixture.row({{x, huge}});
  std::vector<CandidateBound> const bounds{
      {fixture.atom(row, Relation::GreaterEqual, "1", 700), true}};
  fixture.initializeAndPush();
  Observer observer;
  CheckResult old_model = fixture.core.check(observer);
  std::vector<ModelCandidateValue> values{
      {x, fixture.rational("0"), fixture.rational("0")}};
  auto rejected = fixture.core.certifyCandidateModel(
      values.data(), values.data() + values.size(), bounds.data(),
      bounds.data() + bounds.size(), bounds.data(), bounds.data() + bounds.size(),
      &observer);
  require(rejected.status == InputStatus::Unsupported && !rejected.value &&
              fixture.core.verifyModel(*old_model.model).verified(),
          "oversized repair coefficient was accepted or changed the core");
  values.front().value = fixture.rational("1");
  auto direct = fixture.core.certifyCandidateModel(
      values.data(), values.data() + values.size(), bounds.data(),
      bounds.data() + bounds.size(), bounds.data(), bounds.data() + bounds.size(),
      &observer);
  require(direct.status == InputStatus::Accepted && direct.value,
          "repair growth allowance rejected an already valid model");
}

// Three blocked cells, including a negative coefficient, and an unrelated
// shorter repair row: early detection must save that row's pivot.
void testEarlyConflict()
{
  for (bool enabled : {false, true})
  for (bool strict : {false, true})
  {
    Fixture f;
    f.core.setEarlyConflictDetection(enabled);
    auto x = f.variable(), y = f.variable(), z = f.variable(), w = f.variable();
    auto rx = f.row({{x, "1"}}), ry = f.row({{y, "1"}});
    auto rz = f.row({{z, "1"}}), rw = f.row({{w, "1"}});
    auto sum = f.row({{x, "1"}, {y, "1"}, {z, "-1"}});
    auto ax = f.atom(rx, Relation::GreaterEqual, "1", 1);
    auto ay = f.atom(ry, Relation::GreaterEqual, "1", 2);
    auto az = f.atom(rz, Relation::LessEqual, "-1", 3);
    auto aw = f.atom(rw, Relation::GreaterEqual, "1", 4);
    auto bad = f.atom(sum, strict ? Relation::Less : Relation::LessEqual,
                      strict ? "3" : "2", 5);
    auto good = f.atom(sum, Relation::LessEqual, "4", 6);
    f.initializeAndPush();
    for (auto atom : {ax, ay, az})
      require(f.core.assertLiteral(atom, true).status == InputStatus::Accepted,
              "warm bound accepted");
    Observer warm;
    require(f.core.check(warm).status == CheckStatus::Consistent, "warm basis");
    auto frame = f.core.push();
    require(frame.value.has_value(), "conflict frame");
    for (auto atom : {bad, aw})
      require(f.core.assertLiteral(atom, true).status == InputStatus::Accepted,
              "test bound accepted");
    Observer repair;
    auto result = f.core.check(repair);
    require(result.status == CheckStatus::Conflict && result.conflict &&
            f.core.verifyConflict(*result.conflict).verified(), "verified early conflict");
    require(repair.pivots == (enabled ? 0U : 1U), "early detection saves repair pivot");
    require(f.core.statistics().engine_early_conflicts == (enabled ? 1U : 0U),
            "early conflict counted");
    require(f.core.pop(*frame.value) == InputStatus::Accepted, "pop conflict");
    require(f.core.assertLiteral(good, true).status == InputStatus::Accepted,
            "loosened sum accepted");
    Observer after;
    auto sat = f.core.check(after);
    require(sat.status == CheckStatus::Consistent && sat.model &&
            f.core.verifyModel(*sat.model).verified(), "movement restored after pop");
  }
}

void testSoi()
{
  for (bool enabled : {false, true})
  for (bool strict : {false, true})
  {
    Fixture f;
    f.core.setSoi(enabled);
    f.core.setEarlyConflictDetection(true);
    auto x = f.variable(), a = f.variable(), b = f.variable(), c = f.variable();
    auto ra = f.row({{x, "1"}, {a, "1"}});
    auto rb = f.row({{x, "1"}, {b, "1"}});
    auto rc = f.row({{x, "1"}, {c, "-1"}});
    auto relation = strict ? Relation::Greater : Relation::GreaterEqual;
    auto aa = f.atom(ra, relation, strict ? "0" : "1", 1);
    auto ab = f.atom(rb, relation, strict ? "0" : "1", 2);
    auto ac = f.atom(rc, relation, strict ? "0" : "1", 3);
    f.initializeAndPush();
    for (auto atom : {aa, ab, ac})
      require(f.core.assertLiteral(atom, true).status == InputStatus::Accepted, "SOI assert");
    Observer observer;
    auto result = f.core.check(observer);
    require(result.status == CheckStatus::Consistent && result.model &&
            f.core.verifyModel(*result.model).verified(), "SOI verified model");
    require(observer.pivots == (enabled ? 1U : 3U), "SOI repairs three errors with one pivot");
    require(f.core.statistics().engine_soi_steps == (enabled ? 1U : 0U), "SOI step counted");
  }
  {
    Fixture f;
    f.core.setSoi(true);
    auto x = f.variable(), a = f.variable(), b = f.variable(), c = f.variable();
    auto rx = f.row({{x, "1"}});
    auto ra = f.row({{x, "1"}, {a, "1"}});
    auto rb = f.row({{x, "1"}, {b, "1"}});
    auto rc = f.row({{x, "1"}, {c, "1"}});
    auto lo = f.atom(rx, Relation::GreaterEqual, "1", 1);
    auto hi = f.atom(rx, Relation::LessEqual, "2", 2);
    auto aa = f.atom(ra, Relation::GreaterEqual, "3", 3);
    auto ab = f.atom(rb, Relation::GreaterEqual, "3", 4);
    auto ac = f.atom(rc, Relation::GreaterEqual, "3", 5);
    f.initializeAndPush();
    f.core.assertLiteral(lo, true);
    Observer observer;
    require(f.core.check(observer).status == CheckStatus::Consistent, "SOI flip warmup");
    auto frame = f.core.push();
    for (auto atom : {hi, aa, ab, ac})
      f.core.assertLiteral(atom, true);
    auto result = f.core.check(observer);
    require(result.status == CheckStatus::Consistent && result.model &&
            f.core.verifyModel(*result.model).verified(), "SOI flip model");
    require(f.core.statistics().engine_soi_bound_flips > 0, "SOI stops at own bound without pivot");
    require(f.core.pop(*frame.value) == InputStatus::Accepted, "SOI flip pop");
    require(f.core.check(observer).status == CheckStatus::Consistent, "SOI flip recovery");
  }
  {
    Fixture f;
    f.core.setSoi(true);
    auto x = f.variable(), y = f.variable();
    auto rx = f.row({{x, "1"}}), ry = f.row({{y, "1"}});
    auto sum = f.row({{x, "1"}, {y, "1"}});
    auto ax = f.atom(rx, Relation::LessEqual, "0", 1);
    auto ay = f.atom(ry, Relation::LessEqual, "0", 2);
    auto as = f.atom(sum, Relation::GreaterEqual, "1", 3);
    f.initializeAndPush();
    for (auto atom : {ax, ay, as})
      f.core.assertLiteral(atom, true);
    Observer observer;
    auto result = f.core.check(observer);
    require(result.status == CheckStatus::Conflict && result.conflict &&
            f.core.verifyConflict(*result.conflict).verified(), "SOI plateau fallback conflict");
    require(f.core.statistics().engine_soi_fallbacks > 0, "SOI plateau falls back");
  }
}

void testPersistentExtension()
{
  for (bool soi : {false, true})
  for (bool restart : {false, true})
  {
    Fixture f;
    f.core.setSoi(soi);
    f.core.setEarlyConflictDetection(true);
    auto x = f.variable();
    auto rx = f.row({{x, "1"}});
    auto lo = f.atom(rx, Relation::GreaterEqual, "1", 1);
    auto first = f.initializeAndPush();
    f.core.assertLiteral(lo, true);
    Observer observer;
    auto old = f.core.check(observer);
    require(old.status == CheckStatus::Consistent && old.model, "extension warm model");
    require(f.core.beginExtension() == InputStatus::InvalidState,
            "registration cannot extend an active trail");
    require(f.core.restartSearchState() == InputStatus::InvalidState,
            "search reset cannot discard an active trail");
    auto generation = f.core.generation();
    auto pivots = f.core.statistics().engine_pivots;
    require(f.core.pop(first) == InputStatus::Accepted, "unwind before extension");
    require(f.core.beginExtension() == InputStatus::Accepted, "begin extension");
    auto y = f.variable(); // allocated after an existing row's auxiliary
    auto ry = f.row({{y, "1"}});
    auto sum = f.row({{x, "1"}, {y, "-1"}});
    auto ylo = f.atom(ry, Relation::GreaterEqual, "0", 2);
    auto hi = f.atom(rx, Relation::LessEqual, "1", 3); // old row ID remains usable
    auto good = f.atom(sum, Relation::LessEqual, "1", 4);
    auto bad = f.atom(sum, Relation::Greater, "1", 5);
    auto second = f.initializeAndPush();
    if (restart)
    {
      require(f.core.pop(second) == InputStatus::Accepted, "unwind before search reset");
      require(f.core.restartSearchState() == InputStatus::Accepted, "reset interleaved rows");
      const auto pushed = f.core.push();
      require(pushed.value.has_value(), "push after search reset");
      require(f.core.pop(second) == InputStatus::InvalidId,
              "old checkpoint cannot alias a post-reset checkpoint");
      second = *pushed.value;
    }
    require(f.core.generation() == generation, "extension keeps core generation");
    require(!f.core.verifyModel(*old.model).verified(), "old model remains invalid");
    for (auto atom : {lo, ylo, hi, good})
      require(f.core.assertLiteral(atom, true).status == InputStatus::Accepted,
              "old and appended atoms accepted");
    auto sat = f.core.check(observer);
    require(sat.status == CheckStatus::Consistent && sat.model &&
            f.core.verifyModel(*sat.model).verified(), "extended model verified");
    if (!restart)
      require(f.core.statistics().engine_pivots == pivots, "extension preserves warm basis");
    else
      require(f.core.statistics().engine_pivots >= pivots, "search reset keeps work counters");
    require(f.core.pop(second) == InputStatus::Accepted, "pop extended candidate");
    if (restart)
    {
      require(f.core.restartSearchState() == InputStatus::Accepted, "reset checked assignment");
      require(!f.core.verifyModel(*sat.model).verified(), "search reset invalidates old witness");
    }
    auto third = f.core.push();
    for (auto atom : {lo, ylo, hi, bad})
      f.core.assertLiteral(atom, true);
    auto unsat = f.core.check(observer);
    require(unsat.status == CheckStatus::Conflict && unsat.conflict &&
            f.core.verifyConflict(*unsat.conflict).verified(), "extended conflict verified");
    require(f.core.pop(*third.value) == InputStatus::Accepted, "pop extended conflict");
    require(f.core.beginExtension() == InputStatus::Accepted, "extend after conflict");
    auto z = f.variable();
    auto rz = f.row({{z, "1"}});
    auto az = f.atom(rz, Relation::Greater, "1/3", 6);
    f.initializeAndPush();
    f.core.assertLiteral(az, true);
    auto final = f.core.check(observer);
    require(final.status == CheckStatus::Consistent && final.model &&
            f.core.verifyModel(*final.model).verified(), "second extension model verified");
    require(f.core.statistics().variables == 3 && f.core.statistics().rows == 4,
            "registration grew without re-registering old objects");
  }
}

void testDecisionPolarity()
{
  for (bool strict : {false, true})
  {
    Fixture f;
    auto x = f.variable();
    auto y = f.variable();
    auto rx = f.row({{x, "1"}});
    auto other = f.row({{x, "-2"}, {y, "1"}});
    auto lo = f.atom(rx, strict ? Relation::Greater : Relation::GreaterEqual, "0", 1);
    auto lt = f.atom(rx, Relation::Less, "0", 2);
    auto le = f.atom(rx, Relation::LessEqual, "0", 3);
    auto gt = f.atom(rx, Relation::Greater, "0", 4);
    auto ge = f.atom(rx, Relation::GreaterEqual, "0", 5);
    auto dormant = f.atom(other, Relation::Less, "1", 6);
    auto mark = f.initializeAndPush();
    require(!f.core.preferredPolarity(lt), "unvalidated assignment supplies no advice");
    f.core.assertLiteral(lo, true);
    Observer observer;
    auto checked = f.core.check(observer);
    require(checked.status == CheckStatus::Consistent && checked.model,
            "polarity fixture has a verified assignment");
    auto stats = f.core.statistics();
    require(f.core.preferredPolarity(lt) == std::optional<bool>{false}, "strict less polarity");
    require(f.core.preferredPolarity(le) == std::optional<bool>{!strict}, "less-equal epsilon polarity");
    require(f.core.preferredPolarity(gt) == std::optional<bool>{strict}, "greater epsilon polarity");
    require(f.core.preferredPolarity(ge) == std::optional<bool>{true}, "greater-equal polarity");
    require(f.core.preferredPolarity(dormant) == std::optional<bool>{true},
            "dormant row is evaluated without activating it");
    require(f.core.statistics().engine_pivots == stats.engine_pivots &&
            f.core.statistics().checks == stats.checks &&
            f.core.statistics().engine_normalised_cells == stats.engine_normalised_cells &&
            f.core.statistics().engine_activations == stats.engine_activations &&
            f.core.verifyModel(*checked.model).verified(), "advice preserves model and search state");
    require(f.core.pop(mark) == InputStatus::Accepted, "polarity pop");
    require(!f.core.preferredPolarity(gt), "popped assignment supplies no advice");
    f.core.reset();
    require(!f.core.preferredPolarity(gt), "stale atom supplies no advice");
  }
  Fixture f;
  std::vector<std::pair<VariableId, std::string>> terms;
  for (unsigned i = 0; i < 257; ++i)
    terms.push_back({f.variable(), "1"});
  auto long_row = f.row(terms);
  auto atom = f.atom(long_row, Relation::LessEqual, "1", 1);
  f.initializeAndPush();
  Observer observer;
  auto checked = f.core.check(observer);
  require(checked.status == CheckStatus::Consistent && checked.model, "wide advice fixture");
  require(!f.core.preferredPolarity(atom), "wide dormant evaluation respects the hint budget");
  require(f.core.status() == CheckStatus::Consistent &&
          f.core.verifyModel(*checked.model).verified(), "declining advice preserves the core");
}

void testDirectBounds()
{
  for (const auto mode : {DirectBoundsMode::Disabled, DirectBoundsMode::Identity,
                          DirectBoundsMode::Singleton})
  {
    Fixture f(mode);
    const auto x = f.variable();
    const auto rx = f.row({{x, "1"}});
    const auto y = f.variable(); // may follow an auxiliary, depending on mode
    require(y.ordinal() == (mode == DirectBoundsMode::Disabled ? 2U : 1U),
            "direct identity must avoid allocating an auxiliary");
    const auto scaled = f.row({{x, "-2"}});
    const auto sum = f.row({{x, "1"}, {y, "1"}});
    const auto duplicate = f.row({{x, "1"}}); // old base ID after a compound row
    const auto z = f.variable();
    const auto rz = f.row({{z, "1/3"}});
    const auto lo = f.atom(rx, Relation::GreaterEqual, "1", 1);
    const auto hi = f.atom(duplicate, Relation::LessEqual, "2", 2);
    const auto negative = f.atom(scaled, Relation::Greater, "-3", 3);
    const auto compound = f.atom(sum, Relation::GreaterEqual, "4", 4);
    const auto zlo = f.atom(rz, Relation::Greater, "2/3", 5);
    const auto initial = f.initializeAndPush();
    require(f.core.pop(initial) == InputStatus::Accepted, "unwind initial frame");
    const auto stats = f.core.statistics();
    const std::uint64_t avoided = mode == DirectBoundsMode::Disabled ? 0 :
                                  mode == DirectBoundsMode::Identity ? 2 : 4;
    require(stats.identity_rows == 2 && stats.singleton_rows == 4 &&
                stats.rows == 5 && stats.direct_rows == avoided,
            "coverage must distinguish identity, singleton and avoided rows");
    for (unsigned restart = 0; restart < 2; ++restart)
    {
      if (restart)
        require(f.core.restartSearchState() == InputStatus::Accepted,
                "restart must skip aliases without changing allocation order");
      const auto frame = f.core.push();
      require(frame.value.has_value(), "push direct-bound check");
      for (const auto atom : {lo, hi, negative, compound, zlo})
        require(f.core.assertLiteral(atom, true).status == InputStatus::Accepted,
                "assert alias and compound bounds");
      Observer observer;
      const auto result = f.core.check(observer);
      require(result.model && f.core.verifyModel(*result.model).verified(),
              "direct bounds and compound rows must have a verified model");
      require(f.core.preferredPolarity(negative) == std::optional<bool>{true},
              "negative-scaled polarity advice must use the semantic row");
      require(f.core.pop(*frame.value) == InputStatus::Accepted, "pop aliases");
    }
    f.core.reset();
    require(f.core.statistics().direct_rows == 0 && f.core.statistics().rows == 0,
            "reset must clear current registration coverage");
    const auto fresh = f.variable();
    f.row({{fresh, "1"}});
    require(f.core.statistics().direct_rows ==
                (mode == DirectBoundsMode::Disabled ? 0U : 1U),
            "reset must preserve the direct-bound policy");
  }

  for (const auto mode : {DirectBoundsMode::Identity, DirectBoundsMode::Singleton})
  for (const auto& coefficient : {"1", "-1", "2/3", "-7/3",
                                  "-100000000000000000000000000000000000003/17"})
  for (const auto relation : {Relation::Less, Relation::LessEqual,
                              Relation::Greater, Relation::GreaterEqual})
  for (const bool positive : {false, true})
  {
    Fixture f(mode);
    const auto x = f.variable();
    const auto row = f.row({{x, coefficient}});
    const auto atom = f.atom(row, relation, "2/5", 1);
    const auto frame = f.initializeAndPush();
    require(f.core.assertLiteral(atom, positive).status == InputStatus::Accepted,
            "scaled relation assertion");
    Observer observer;
    const auto result = f.core.check(observer);
    require(result.model && f.core.verifyModel(*result.model).verified() &&
                f.core.preferredPolarity(atom) == std::optional<bool>{positive},
            "each signed/scaled relation and its complement must remain exact");
    require(f.core.pop(frame) == InputStatus::Accepted, "scaled relation pop");
  }

  // Two distinct semantic rows bind the same base. The engine's unit weights
  // must become 1/2 and 1/3 in the original vocabulary, including strictness.
  Fixture f(DirectBoundsMode::Singleton);
  const auto x = f.variable();
  const auto upper_row = f.row({{x, "2"}});
  const auto lower_row = f.row({{x, "-3"}});
  const auto upper = f.atom(upper_row, Relation::LessEqual, "2", 1);
  const auto lower = f.atom(lower_row, Relation::Less, "-3", 2);
  const auto frame = f.initializeAndPush();
  f.core.setConflictVerification(false); // explicit verification still checks it
  require(f.core.assertLiteral(upper, true).status == InputStatus::Accepted,
          "scaled upper accepted");
  auto conflict = f.core.assertLiteral(lower, true);
  require(conflict.immediate_conflict &&
              f.core.verifyConflict(*conflict.immediate_conflict).verified(),
          "differently scaled bounds need a valid original-row certificate");
  require(f.render(conflict.immediate_conflict->terms[0].weight) == "1/2" &&
              f.render(conflict.immediate_conflict->terms[1].weight) == "1/3",
          "normalized engine coefficients must be rescaled on export");
  conflict.immediate_conflict->terms[0].weight = f.rational("1");
  require(!f.core.verifyConflict(*conflict.immediate_conflict).verified(),
          "corrupted direct-bound weights must fail verification");
  std::vector<ConflictCandidateTerm> proposed{
      {upper, true, f.rational("1/2")}, {lower, true, f.rational("1/3")}};
  const auto certified = f.core.certifyCandidateConflict(
      proposed.data(), proposed.data() + proposed.size());
  require(certified.value && f.core.verifyConflict(*certified.value).verified(),
          "external candidate certificates already use original weights");
  require(f.core.pop(frame) == InputStatus::Accepted, "pop scaled conflict");
  require(!f.core.verifyConflict(*certified.value).verified(),
          "popping invalidates direct-bound witnesses");

  for (const auto mode : {DirectBoundsMode::Identity, DirectBoundsMode::Singleton})
  {
    direct_bounds_mode = mode;
    testRelations();
    testDifferential();
    testPersistentExtension();
    testDecisionPolarity();
    testCandidateConflictRecovery();
    testCandidateModelRepairStrict();
    testSeparateModelValues();
    testSeparateRespectsForcedEquality();
  }
  direct_bounds_mode = DirectBoundsMode::Disabled;
}

void runMode(std::string const& mode)
{
  if (mode == "direct-bounds")
    testDirectBounds();
  else if (mode == "conflict-recovery")
    testCandidateConflictRecovery();
  else if (mode == "polarity")
    testDecisionPolarity();
  else if (mode == "extension")
    testPersistentExtension();
  else if (mode == "soi")
  {
    testSoi();
    soi_mode = true;
    for (bool early : {false, true})
    {
      early_conflict_mode = early;
      testDifferential();
      testRolling();
      testStrict();
      testHuge();
      testConflictThenReuse();
    }
  }
  else if (mode == "early-conflict")
  {
    testEarlyConflict();
    early_conflict_mode = true;
    testDifferential();
    testRolling();
    testStrict();
    testConflictThenReuse();
  }
  else if (mode == "semantic")
  {
    testSemantic();
    testSeparateModelValues();
    testSeparateRespectsForcedEquality();
    testRelations();
    testSharedOrigin();
    testCandidateModelRepair();
    testCandidateModelRepairStrict();
  }
  else if (mode == "strict")
  {
    testStrict();
  }
  else if (mode == "conflict")
  {
    testTableauConflict();
    testConflictThenReuse();
    testGeneralisedConflict();
  }
  else if (mode == "interrupt")
  {
    testInterruption(StopReason::Interrupted, CheckStatus::Interrupted);
    testInterruption(StopReason::ResourceLimit, CheckStatus::ResourceLimit);
  }
  else if (mode == "resource")
  {
    testPivotBudgets();
    testNumberResourceLimits();
    testSeparationResourceLimits();
    testCandidateModelRepairLimits();
  }
  else if (mode == "lifecycle")
  {
    testLifecycleAndRejections();
    testSimplexCheckpointLookup();
  }
  else if (mode == "rolling")
  {
    testRolling();
  }
  else if (mode == "huge")
  {
    testHuge();
  }
  else if (mode == "concurrency")
  {
    testConcurrency();
  }
  else if (mode == "differential")
  {
    testDifferential();
  }
  else if (mode == "performance")
  {
    testPerformance();
  }
  else if (mode == "all")
  {
    testCandidateConflictRecovery();
    testSemantic();
    testSeparateModelValues();
    testSeparateRespectsForcedEquality();
    testRelations();
    testStrict();
    testCandidateModelRepair();
    testCandidateModelRepairStrict();
    testTableauConflict();
    testConflictThenReuse();
    testGeneralisedConflict();
    testSharedOrigin();
    testInterruption(StopReason::Interrupted, CheckStatus::Interrupted);
    testInterruption(StopReason::ResourceLimit, CheckStatus::ResourceLimit);
    testPivotBudgets();
    testNumberResourceLimits();
    testSeparationResourceLimits();
    testCandidateModelRepairLimits();
    testLifecycleAndRejections();
    testSimplexCheckpointLookup();
    testRolling();
    testHuge();
    testDifferential();
    testConcurrency();
  }
  else
  {
    fail("unknown test mode: " + mode);
  }
}

}  // namespace

int main(int argc, char** argv)
{
  if (argc != 2)
  {
    std::cerr << "usage: exact_lra_core_tests MODE\n";
    return EXIT_FAILURE;
  }
  try
  {
    runMode(argv[1]);
    std::cout << "PASS " << argv[1] << '\n';
    return EXIT_SUCCESS;
  }
  catch (std::exception const& error)
  {
    std::cerr << "FAIL " << argv[1] << ": " << error.what() << '\n';
    return EXIT_FAILURE;
  }
}
