#include "ExactLraCore.h"

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <string>
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
  StopReason pollBeforePivot() noexcept override
  {
    return StopReason::Continue;
  }
  void accountPivot(bool) noexcept override {}
};

struct Fixture final
{
  Fixture() : input(limits), core(limits) {}

  ExactRational rational(char const* text)
  {
    NumberOperationScope scope(input);
    return ExactRational::parseDecimalOrFraction(text);
  }

  VariableId variable()
  {
    auto result = core.addVariable();
    require(result.status == InputStatus::Accepted && result.value,
            "variable registration failed");
    return *result.value;
  }

  RowId row(VariableId variable_id)
  {
    LinearTerm term{variable_id, rational("1")};
    auto result = core.addRow(&term, &term + 1);
    require(result.status == InputStatus::Accepted && result.value,
            "row registration failed");
    return *result.value;
  }

  AtomId atom(RowId row_id, Relation relation, char const* threshold,
              std::uint64_t serial)
  {
    ExactRational value = rational(threshold);
    auto result = core.addAtom(row_id, relation, value,
                               OriginId{11, serial},
                               OriginId{11, serial + 1U});
    require(result.status == InputStatus::Accepted && result.value,
            "atom registration failed");
    return *result.value;
  }

  Checkpoint start()
  {
    require(core.initialize() == InputStatus::Accepted,
            "initialization failed");
    auto pushed = core.push();
    require(pushed.status == InputStatus::Accepted && pushed.value,
            "push failed");
    return *pushed.value;
  }

  NumberBudget input;
  ExactLraCore core;
};

void automaticAndPublicVerification()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row(x);
  AtomId const lower = fixture.atom(row, Relation::GreaterEqual, "0", 10);
  AtomId const upper = fixture.atom(row, Relation::LessEqual, "2", 20);
  Checkpoint const checkpoint = fixture.start();
  require(fixture.core.assertLiteral(lower, true).status ==
              InputStatus::Accepted &&
              fixture.core.assertLiteral(upper, true).status ==
                  InputStatus::Accepted,
          "model assertions failed");
  Observer observer;
  CheckResult result = fixture.core.check(observer);
  require(result.status == CheckStatus::Consistent && result.model &&
              !result.conflict,
          "verified model was not published");
  require(fixture.core.verifyModel(*result.model).verified(),
          "public model verification failed");
  CoreStatistics const stats = fixture.core.statistics();
  require(stats.models_produced == 1 && stats.model_verifications >= 2 &&
              stats.verification_failures == 0,
          "model verification statistics are incomplete");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "model verification pop failed");

  Fixture conflict_fixture;
  VariableId const conflict_x = conflict_fixture.variable();
  RowId const conflict_row = conflict_fixture.row(conflict_x);
  AtomId const strict = conflict_fixture.atom(
      conflict_row, Relation::Less, "0", 30);
  Checkpoint const conflict_checkpoint = conflict_fixture.start();
  require(conflict_fixture.core.assertLiteral(strict, true).status ==
              InputStatus::Accepted,
          "conflict first assertion failed");
  AssertResult immediate =
      conflict_fixture.core.assertLiteral(strict, false);
  require(immediate.status == InputStatus::Accepted &&
              immediate.immediate_conflict,
          "verified immediate conflict was not published");
  require(conflict_fixture.core.verifyConflict(
              *immediate.immediate_conflict).verified(),
          "public immediate-conflict verification failed");
  CoreStatistics const conflict_stats = conflict_fixture.core.statistics();
  require(conflict_stats.conflicts_produced == 1 &&
              conflict_stats.conflict_verifications >= 2 &&
              conflict_stats.verification_failures == 0,
          "conflict verification statistics are incomplete");
  require(conflict_fixture.core.pop(conflict_checkpoint) ==
              InputStatus::Accepted,
          "conflict verification pop failed");
  std::cout << "VERIFY automatic-public-boundaries PASS\n";
}

void explicitVerificationWithAutomaticDisabled()
{
  Fixture fixture;
  const auto x = fixture.variable();
  const auto strict = fixture.atom(fixture.row(x), Relation::Less, "0", 40);
  (void)fixture.start();
  fixture.core.setConflictVerification(false);
  require(fixture.core.assertLiteral(strict, true).status == InputStatus::Accepted,
          "unchecked conflict first assertion failed");
  const auto immediate = fixture.core.assertLiteral(strict, false);
  require(immediate.status == InputStatus::Accepted && immediate.immediate_conflict,
          "unchecked immediate conflict was not published");
  Observer observer;
  auto checked = fixture.core.check(observer);
  require(checked.status == CheckStatus::Conflict && checked.conflict &&
              fixture.core.statistics().conflict_verifications == 0,
          "disabled automatic checking still verified a produced conflict");

  // Explicit verification is a separate contract, including rejected inputs.
  Conflict const empty{checked.conflict->tag, {}};
  require(fixture.core.verifyConflict(empty).error ==
              VerificationError::NotContradictory,
          "explicit verification accepted an empty conflict while automatic checking was off");
  Conflict altered = [&] {
    NumberOperationScope scope(fixture.input);
    Conflict copy = *checked.conflict;
    copy.terms.front().weight = ExactRational(std::int64_t{0});
    return copy;
  }();
  require(fixture.core.verifyConflict(altered).error == VerificationError::InvalidWeight,
          "explicit verification accepted a zero weight while automatic checking was off");
  Conflict stale = [&] {
    NumberOperationScope scope(fixture.input);
    Conflict copy = *checked.conflict;
    ++copy.tag.state_revision;
    return copy;
  }();
  require(fixture.core.verifyConflict(stale).error == VerificationError::StaleId,
          "explicit verification accepted a stale conflict while automatic checking was off");
  require(fixture.core.verifyConflict(*checked.conflict).verified() &&
              fixture.core.statistics().conflict_verifications == 4 &&
              fixture.core.statistics().verification_failures == 3,
          "explicit conflict verification did not run independently of the automatic flag");

  fixture.core.setConflictVerification(true);
  checked = fixture.core.check(observer);
  require(checked.status == CheckStatus::Conflict && checked.conflict &&
              fixture.core.statistics().conflict_verifications == 5,
          "re-enabling automatic conflict verification had no effect");

  // Exercise the tableau-conflict producer as well as the immediate and
  // pending-conflict producers above: x <= 0, y <= 0, x+y >= 1.
  Fixture tableau;
  const auto tx = tableau.variable();
  const auto ty = tableau.variable();
  const auto upper_x = tableau.atom(tableau.row(tx), Relation::LessEqual, "0", 50);
  const auto upper_y = tableau.atom(tableau.row(ty), Relation::LessEqual, "0", 60);
  LinearTerm const terms[]{{tx, tableau.rational("1")}, {ty, tableau.rational("1")}};
  const auto sum = tableau.core.addRow(terms, terms + 2);
  require(sum.value.has_value(), "unchecked tableau sum registration failed");
  const auto lower_sum = tableau.atom(*sum.value, Relation::GreaterEqual, "1", 70);
  (void)tableau.start();
  tableau.core.setConflictVerification(false);
  for (auto const atom : {upper_x, upper_y, lower_sum})
  {
    const auto asserted = tableau.core.assertLiteral(atom, true);
    require(asserted.status == InputStatus::Accepted && !asserted.immediate_conflict,
            "unchecked tableau setup produced an immediate conflict");
  }
  const auto tableau_conflict = tableau.core.check(observer);
  require(tableau_conflict.status == CheckStatus::Conflict && tableau_conflict.conflict &&
              tableau.core.statistics().tableau_conflicts == 1 &&
              tableau.core.statistics().conflict_verifications == 0,
          "disabled automatic checking still verified a tableau conflict");
  require(tableau.core.verifyConflict(*tableau_conflict.conflict).verified() &&
              tableau.core.statistics().conflict_verifications == 1,
          "explicit tableau verification did not run with automatic checking disabled");
  std::cout << "VERIFY explicit-with-automatic-disabled PASS\n";
}

void witnessLifecycle()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row(x);
  AtomId const lower = fixture.atom(row, Relation::GreaterEqual, "0", 100);
  AtomId const upper = fixture.atom(row, Relation::LessEqual, "2", 110);
  AtomId const tighter = fixture.atom(row, Relation::LessEqual, "1", 120);
  Checkpoint const checkpoint = fixture.start();
  require(fixture.core.assertLiteral(lower, true).status ==
              InputStatus::Accepted &&
              fixture.core.assertLiteral(upper, true).status ==
                  InputStatus::Accepted,
          "lifecycle assertion setup failed");
  Observer observer;
  CheckResult first = fixture.core.check(observer);
  require(first.status == CheckStatus::Consistent && first.model,
          "first lifecycle model failed");
  Model first_model = std::move(*first.model);
  require(fixture.core.verifyModel(first_model).verified(),
          "first lifecycle model did not verify");

  CheckResult second = fixture.core.check(observer);
  require(second.status == CheckStatus::Consistent && second.model,
          "second lifecycle model failed");
  require(fixture.core.verifyModel(first_model).error ==
              VerificationError::StaleId,
          "model survived another check");
  Model second_model = std::move(*second.model);
  require(fixture.core.verifyModel(second_model).verified(),
          "second lifecycle model did not verify");

  require(fixture.core.assertLiteral(tighter, true).status ==
              InputStatus::Accepted,
          "post-model assertion failed");
  require(!fixture.core.verifyModel(second_model).verified(),
          "model survived another assertion");
  CheckResult third = fixture.core.check(observer);
  require(third.status == CheckStatus::Consistent && third.model,
          "post-assertion model failed");
  Model third_model = std::move(*third.model);

  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "lifecycle pop failed");
  require(!fixture.core.verifyModel(third_model).verified(),
          "model survived pop");
  fixture.core.reset();
  require(!fixture.core.verifyModel(third_model).verified(),
          "model survived reset");
  std::cout << "VERIFY stale-witness-lifecycle PASS\n";
}

void copiedImmediateConflictCorruption()
{
  Fixture fixture;
  VariableId const x = fixture.variable();
  RowId const row = fixture.row(x);
  AtomId const strict = fixture.atom(row, Relation::Less, "0", 200);
  Checkpoint const checkpoint = fixture.start();
  require(fixture.core.assertLiteral(strict, true).status ==
              InputStatus::Accepted,
          "copied conflict first assertion failed");
  AssertResult result = fixture.core.assertLiteral(strict, false);
  require(result.status == InputStatus::Accepted &&
              result.immediate_conflict,
          "copied immediate conflict setup failed");
  Conflict original = std::move(*result.immediate_conflict);
  Conflict altered = [&] {
    NumberOperationScope scope(fixture.input);
    Conflict copy = original;
    copy.terms[0].weight = ExactRational(std::int64_t{0});
    return copy;
  }();
  require(fixture.core.verifyConflict(altered).error ==
              VerificationError::InvalidWeight,
          "altered immediate conflict was accepted");
  require(fixture.core.status() == CheckStatus::Conflict &&
              fixture.core.verifyConflict(original).verified(),
          "copied corruption damaged the core or original witness");
  require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
          "copied conflict pop failed");
  require(!fixture.core.verifyConflict(original).verified(),
          "conflict survived pop");
  std::cout << "VERIFY copied-immediate-corruption PASS\n";
}

void automaticVerifierResourceRetry()
{
  {
    Fixture fixture;
    VariableId const x = fixture.variable();
    RowId const row = fixture.row(x);
    AtomId const lower = fixture.atom(
        row, Relation::GreaterEqual, "0", 250);
    Checkpoint const checkpoint = fixture.start();
    require(fixture.core.assertLiteral(lower, true).status ==
                InputStatus::Accepted,
            "model resource assertion failed");
    fixture.core.testForceNextModelVerificationResource();
    Observer observer;
    CheckResult stopped = fixture.core.check(observer);
    require(stopped.status == CheckStatus::ResourceLimit &&
                !stopped.model && !stopped.conflict &&
                fixture.core.testLastVerificationError() ==
                    VerificationError::ResourceLimit,
            "model verifier resource stop published a witness");
    CheckResult retry = fixture.core.check(observer);
    require(retry.status == CheckStatus::Consistent && retry.model &&
                fixture.core.verifyModel(*retry.model).verified(),
            "model verifier resource retry failed");
    require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
            "model resource pop failed");
  }
  {
    Fixture fixture;
    VariableId const x = fixture.variable();
    RowId const row = fixture.row(x);
    AtomId const upper = fixture.atom(
        row, Relation::LessEqual, "0", 260);
    AtomId const lower = fixture.atom(
        row, Relation::GreaterEqual, "1", 270);
    Checkpoint const checkpoint = fixture.start();
    require(fixture.core.assertLiteral(upper, true).status ==
                InputStatus::Accepted,
            "conflict resource first assertion failed");
    fixture.core.testForceNextConflictVerificationResource();
    AssertResult stopped = fixture.core.assertLiteral(lower, true);
    require(stopped.status == InputStatus::ResourceLimit &&
                !stopped.immediate_conflict &&
                fixture.core.status() == CheckStatus::ResourceLimit &&
                fixture.core.testLastVerificationError() ==
                    VerificationError::ResourceLimit,
            "conflict verifier resource stop published a witness");
    Observer observer;
    CheckResult retry = fixture.core.check(observer);
    require(retry.status == CheckStatus::Conflict && retry.conflict &&
                fixture.core.verifyConflict(*retry.conflict).verified(),
            "conflict verifier resource retry lost exact support");
    require(fixture.core.pop(checkpoint) == InputStatus::Accepted,
            "conflict resource pop failed");
  }
  std::cout << "VERIFY automatic-resource-retry PASS\n";
}

void internalSnapshotCorruption()
{
  {
    Fixture fixture;
    VariableId const x = fixture.variable();
    RowId const row = fixture.row(x);
    AtomId const upper = fixture.atom(row, Relation::LessEqual, "1", 300);
    (void)fixture.start();
    require(fixture.core.assertLiteral(upper, true).status ==
                InputStatus::Accepted,
            "row-corruption assertion failed");
    Observer observer;
    CheckResult baseline = fixture.core.check(observer);
    require(baseline.status == CheckStatus::Consistent && baseline.model,
            "row-corruption baseline failed");
    Model old_model = std::move(*baseline.model);
    fixture.core.testCorruptVerificationRow(row);
    CheckResult rejected = fixture.core.check(observer);
    require(rejected.status == CheckStatus::InternalError &&
                !rejected.model && !rejected.conflict &&
                fixture.core.status() == CheckStatus::InternalError,
            "corrupt row snapshot did not invalidate fail closed");
    require(fixture.core.verifyModel(old_model).error ==
                VerificationError::InternalError,
            "verification in InternalError state was not rejected");
  }
  {
    Fixture fixture;
    VariableId const x = fixture.variable();
    RowId const row = fixture.row(x);
    AtomId const strict = fixture.atom(row, Relation::Less, "0", 400);
    (void)fixture.start();
    require(fixture.core.assertLiteral(strict, true).status ==
                InputStatus::Accepted,
            "bound-corruption first assertion failed");
    fixture.core.testCorruptVerificationBound(strict, true);
    AssertResult rejected = fixture.core.assertLiteral(strict, false);
    require(rejected.status == InputStatus::InternalError &&
                !rejected.immediate_conflict &&
                fixture.core.status() == CheckStatus::InternalError,
            "corrupt bound snapshot escaped automatic verification");
  }
  std::cout << "VERIFY internal-snapshot-corruption FAIL_CLOSED\n";
}

}  // namespace

int main()
{
  try
  {
    automaticAndPublicVerification();
    explicitVerificationWithAutomaticDisabled();
    witnessLifecycle();
    copiedImmediateConflictCorruption();
    automaticVerifierResourceRetry();
    internalSnapshotCorruption();
    std::cout << "PASS verifier\n";
    return EXIT_SUCCESS;
  }
  catch (std::exception const& error)
  {
    std::cerr << "FAIL verifier: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
}
