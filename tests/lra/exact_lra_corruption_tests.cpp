#include "ExactLraCore.h"
#include "ExactLraVerificationData.h"

#include <algorithm>
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

struct PairShape final
{
  ExactLraVerificationBoundKind positive_kind;
  std::int64_t positive_delta;
  ExactLraVerificationBoundKind negative_kind;
  std::int64_t negative_delta;
};

PairShape pairShape(Relation relation)
{
  switch (relation)
  {
    case Relation::Less:
      return {ExactLraVerificationBoundKind::Upper, -1,
              ExactLraVerificationBoundKind::Lower, 0};
    case Relation::LessEqual:
      return {ExactLraVerificationBoundKind::Upper, 0,
              ExactLraVerificationBoundKind::Lower, 1};
    case Relation::Greater:
      return {ExactLraVerificationBoundKind::Lower, 1,
              ExactLraVerificationBoundKind::Upper, 0};
    case Relation::GreaterEqual:
      return {ExactLraVerificationBoundKind::Lower, 0,
              ExactLraVerificationBoundKind::Upper, -1};
  }
  fail("invalid relation in neutral fixture");
}

class NeutralFixture final
{
 public:
  enum class Kind : std::uint8_t
  {
    Conflict,
    Model
  };

  explicit NeutralFixture(Kind kind)
      : budget(limits),
        generation{UINT64_C(0x0000000100000001)},
        tag{generation, 17},
        x(generation, 0),
        y(generation, 1)
  {
    NumberOperationScope scope(budget);
    base_variables = {x, y};
    rows.push_back(ExactLraVerificationRow{
        RowId(generation, 0), {{x, ExactRational(std::int64_t{1})}}});
    rows.push_back(ExactLraVerificationRow{
        RowId(generation, 1), {{y, ExactRational(std::int64_t{1})}}});
    rows.push_back(ExactLraVerificationRow{
        RowId(generation, 2),
        {{x, ExactRational(std::int64_t{1})},
         {y, ExactRational(std::int64_t{1})}}});
    if (kind == Kind::Conflict)
    {
      addPair(rows[0].id, Relation::LessEqual,
              ExactRational(std::int64_t{0}), OriginId{7, 10},
              OriginId{7, 11});
      addPair(rows[1].id, Relation::LessEqual,
              ExactRational(std::int64_t{0}), OriginId{7, 20},
              OriginId{7, 21});
      addPair(rows[2].id, Relation::GreaterEqual,
              ExactRational(std::int64_t{1}), OriginId{7, 30},
              OriginId{7, 31});
      active_bounds = {bounds[0].reference, bounds[2].reference,
                       bounds[4].reference};
      conflict = Conflict{
          tag,
          {{bounds[0].origin, bounds[0].reference,
            ExactRational(std::int64_t{1})},
           {bounds[2].origin, bounds[2].reference,
            ExactRational(std::int64_t{1})},
           {bounds[4].origin, bounds[4].reference,
            ExactRational(std::int64_t{1})}}};
    }
    else
    {
      addPair(rows[0].id, Relation::Less,
              ExactRational(std::int64_t{1}), OriginId{8, 10},
              OriginId{8, 11});
      addPair(rows[0].id, Relation::Greater,
              ExactRational(std::int64_t{-1}), OriginId{8, 20},
              OriginId{8, 21});
      addPair(rows[1].id, Relation::LessEqual,
              ExactRational(std::int64_t{2}), OriginId{8, 30},
              OriginId{8, 31});
      addPair(rows[1].id, Relation::GreaterEqual,
              ExactRational(std::int64_t{-2}), OriginId{8, 40},
              OriginId{8, 41});
      addPair(rows[2].id, Relation::LessEqual,
              ExactRational(std::int64_t{3}), OriginId{8, 50},
              OriginId{8, 51});
      active_bounds = {bounds[0].reference, bounds[2].reference,
                       bounds[4].reference, bounds[6].reference,
                       bounds[8].reference};
      model = Model{tag,
                    {{x, ExactRational(std::int64_t{0})},
                     {y, ExactRational(std::int64_t{0})}}};
    }
  }

  ExactRational rational(std::string const& text)
  {
    return ExactRational::parseDecimalOrFraction(text);
  }

  BoundRef addPair(RowId row, Relation relation,
                   ExactRational const& threshold,
                   OriginId positive_origin, OriginId negative_origin)
  {
    AtomId const atom(generation,
                      static_cast<std::uint32_t>(atoms.size()));
    BoundRef const positive(
        generation, static_cast<std::uint32_t>(bounds.size()));
    BoundRef const negative(generation, positive.ordinal() + 1U);
    PairShape const shape = pairShape(relation);
    atoms.push_back(ExactLraVerificationAtom{
        atom, row, relation, threshold, positive_origin, negative_origin,
        positive, negative});
    bounds.push_back(ExactLraVerificationBound{
        positive, row, shape.positive_kind, threshold,
        ExactRational(shape.positive_delta), positive_origin, atom, true});
    bounds.push_back(ExactLraVerificationBound{
        negative, row, shape.negative_kind, threshold,
        ExactRational(shape.negative_delta), negative_origin, atom, false});
    return positive;
  }

  ExactLraVerificationDataView view() const noexcept
  {
    return ExactLraVerificationDataView{
        tag, base_variables, rows, atoms, bounds, active_bounds,
        pending_conflict_bound};
  }

  NumberBudget budget;
  CoreGeneration generation;
  WitnessTag tag;
  VariableId x;
  VariableId y;
  std::vector<VariableId> base_variables;
  std::vector<ExactLraVerificationRow> rows;
  std::vector<ExactLraVerificationAtom> atoms;
  std::vector<ExactLraVerificationBound> bounds;
  std::vector<BoundRef> active_bounds;
  std::optional<BoundRef> pending_conflict_bound;
  Conflict conflict{tag, {}};
  Model model{tag, {}};
};

template <class Mutator>
void rejectConflict(unsigned number, char const* name, Mutator&& mutate)
{
  NeutralFixture fixture(NeutralFixture::Kind::Conflict);
  NumberOperationScope scope(fixture.budget);
  require(verifyExactLraConflict(fixture.view(), fixture.conflict).verified(),
          "neutral conflict baseline was invalid");
  Conflict candidate = fixture.conflict;
  mutate(fixture, candidate);
  VerificationResult const result =
      verifyExactLraConflict(fixture.view(), candidate);
  require(!result.verified(), std::string(name) + " was accepted");
  if (number == 0)
  {
    std::cout << "EXTRA " << name << " REJECTED\n";
  }
  else
  {
    std::cout << "CORRUPT " << number << ' ' << name << " REJECTED\n";
  }
}

template <class Mutator>
void rejectModel(unsigned number, char const* name, Mutator&& mutate)
{
  NeutralFixture fixture(NeutralFixture::Kind::Model);
  NumberOperationScope scope(fixture.budget);
  require(verifyExactLraModel(fixture.view(), fixture.model).verified(),
          "neutral model baseline was invalid");
  Model candidate = fixture.model;
  mutate(fixture, candidate);
  VerificationResult const result = verifyExactLraModel(fixture.view(),
                                                        candidate);
  require(!result.verified(), std::string(name) + " was accepted");
  if (number == 0)
  {
    std::cout << "EXTRA " << name << " REJECTED\n";
  }
  else
  {
    std::cout << "CORRUPT " << number << ' ' << name << " REJECTED\n";
  }
}

void conflictCorruptions()
{
  rejectConflict(1, "empty-conflict", [](auto&, Conflict& conflict) {
    conflict.terms.clear();
  });
  rejectConflict(2, "missing-original-term", [](auto&, Conflict& conflict) {
    conflict.terms.pop_back();
  });
  rejectConflict(3, "duplicate-bound-ref", [](auto&, Conflict& conflict) {
    conflict.terms[1].bound = conflict.terms[0].bound;
  });
  rejectConflict(4, "duplicated-complete-term", [](auto&, Conflict& conflict) {
    conflict.terms.insert(conflict.terms.begin() + 1, conflict.terms[0]);
  });
  rejectConflict(5, "zero-weight", [](NeutralFixture& fixture,
                                       Conflict& conflict) {
    conflict.terms[0].weight = fixture.rational("0");
  });
  rejectConflict(6, "negative-weight", [](NeutralFixture& fixture,
                                           Conflict& conflict) {
    conflict.terms[0].weight = fixture.rational("-1");
  });
  rejectConflict(7, "changed-positive-weight", [](NeutralFixture& fixture,
                                                   Conflict& conflict) {
    conflict.terms[0].weight = fixture.rational("2");
  });
  rejectConflict(8, "stale-conflict-generation", [](NeutralFixture& fixture,
                                                      Conflict& conflict) {
    conflict.tag.generation = CoreGeneration{fixture.generation.value + 1U};
  });
  rejectConflict(9, "foreign-conflict-generation", [](auto&,
                                                        Conflict& conflict) {
    conflict.tag.generation = CoreGeneration{UINT64_C(0x0000000200000001)};
  });
  rejectConflict(10, "stale-conflict-revision", [](auto&,
                                                     Conflict& conflict) {
    ++conflict.tag.state_revision;
  });
  rejectConflict(11, "unknown-bound-ordinal", [](NeutralFixture& fixture,
                                                  Conflict& conflict) {
    conflict.terms.back().bound = BoundRef(fixture.generation, 99);
  });
  rejectConflict(12, "inactive-bound", [](NeutralFixture& fixture,
                                           Conflict&) {
    fixture.active_bounds.erase(fixture.active_bounds.begin() + 1);
  });
  rejectConflict(13, "origin-mismatch", [](auto&, Conflict& conflict) {
    ++conflict.terms[0].origin.serial;
  });
  rejectConflict(14, "altered-bound-kind", [](NeutralFixture& fixture,
                                               Conflict&) {
    fixture.bounds[0].kind = ExactLraVerificationBoundKind::Lower;
  });
  rejectConflict(15, "altered-strict-component", [](NeutralFixture& fixture,
                                                      Conflict&) {
    fixture.bounds[1].infinitesimal = fixture.rational("2");
  });
  rejectConflict(16, "altered-threshold", [](NeutralFixture& fixture,
                                              Conflict&) {
    fixture.bounds[0].threshold = fixture.rational("1");
  });
  rejectConflict(17, "altered-row-coefficient", [](NeutralFixture& fixture,
                                                    Conflict&) {
    fixture.rows[2].terms[0].coefficient = fixture.rational("2");
  });
  rejectConflict(18, "uncancelled-base-coefficient",
                 [](NeutralFixture& fixture, Conflict&) {
                   fixture.rows[2].terms.erase(
                       fixture.rows[2].terms.begin() + 1);
                 });
  rejectConflict(19, "nonnegative-final-delta",
                 [](NeutralFixture& fixture, Conflict&) {
                   ExactRational zero = fixture.rational("0");
                   fixture.atoms[2].threshold = zero;
                   fixture.bounds[4].threshold = zero;
                   fixture.bounds[5].threshold = std::move(zero);
                 });
  rejectConflict(20, "unproved-support", [](auto&, Conflict& conflict) {
    conflict.terms.erase(conflict.terms.begin() + 1);
  });

  rejectConflict(0, "noncanonical-conflict-order",
                 [](auto&, Conflict& conflict) {
                   std::swap(conflict.terms[0], conflict.terms[1]);
                 });

  NeutralFixture shared_origin(NeutralFixture::Kind::Conflict);
  {
    NumberOperationScope scope(shared_origin.budget);
    shared_origin.atoms[1].positive_origin =
        shared_origin.atoms[0].positive_origin;
    shared_origin.bounds[2].origin = shared_origin.bounds[0].origin;
    shared_origin.conflict.terms[1].origin =
        shared_origin.conflict.terms[0].origin;
    require(verifyExactLraConflict(shared_origin.view(),
                                   shared_origin.conflict).verified(),
            "distinct bounds sharing an OriginId must remain valid");
  }
  std::cout << "VERIFY shared-origin-distinct-bounds ACCEPTED\n";
}

void hugeTruncation()
{
  NeutralFixture fixture(NeutralFixture::Kind::Model);
  NumberOperationScope scope(fixture.budget);
  std::string numerator("1");
  numerator.append(1240, '0');
  numerator.push_back('3');
  ExactRational huge =
      ExactRational::fromCanonicalIntegers(numerator, "7");
  BoundRef const huge_lower = fixture.addPair(
      fixture.rows[0].id, Relation::GreaterEqual, huge,
      OriginId{8, 100}, OriginId{8, 101});
  fixture.active_bounds = {huge_lower};
  fixture.model.values[0].value = huge;
  require(verifyExactLraModel(fixture.view(), fixture.model).verified(),
          "huge exact model baseline was invalid");
  Model truncated = fixture.model;
  truncated.values[0].value -= ExactRational(std::int64_t{1});
  require(!verifyExactLraModel(fixture.view(), truncated).verified(),
          "huge truncated model was accepted");
  std::cout << "VERIFY huge-model-truncation REJECTED bits="
            << huge.numeratorBits() << '\n';
}

void modelCorruptions()
{
  rejectModel(21, "empty-model", [](auto&, Model& model) {
    model.values.clear();
  });
  rejectModel(22, "missing-base-variable", [](auto&, Model& model) {
    model.values.pop_back();
  });
  rejectModel(23, "duplicate-model-variable", [](auto&, Model& model) {
    model.values.insert(model.values.begin() + 1, model.values[0]);
  });
  rejectModel(24, "unknown-model-variable", [](NeutralFixture& fixture,
                                                Model& model) {
    model.values[1].variable = VariableId(fixture.generation, 99);
  });
  rejectModel(25, "stale-model-tag", [](NeutralFixture& fixture,
                                        Model& model) {
    model.tag.generation = CoreGeneration{fixture.generation.value + 1U};
  });
  rejectModel(0, "foreign-model-tag", [](auto&, Model& model) {
    model.tag.generation = CoreGeneration{UINT64_C(0x0000000200000001)};
  });
  rejectModel(0, "stale-model-revision", [](auto&, Model& model) {
    ++model.tag.state_revision;
  });
  rejectModel(26, "extra-model-variable", [](NeutralFixture& fixture,
                                              Model& model) {
    model.values.push_back(
        ModelValue{VariableId(fixture.generation, 2),
                   fixture.rational("0")});
  });
  rejectModel(27, "altered-exact-value", [](NeutralFixture& fixture,
                                             Model& model) {
    model.values[0].value = fixture.rational("2");
  });
  rejectModel(28, "row-definition-violation", [](NeutralFixture& fixture,
                                                  Model& model) {
    fixture.active_bounds = {fixture.bounds[8].reference};
    model.values[0].value = fixture.rational("2");
    model.values[1].value = fixture.rational("2");
  });
  rejectModel(29, "strict-upper-equality", [](NeutralFixture& fixture,
                                               Model& model) {
    model.values[0].value = fixture.rational("1");
  });
  rejectModel(30, "strict-lower-equality", [](NeutralFixture& fixture,
                                               Model& model) {
    model.values[0].value = fixture.rational("-1");
  });

  NeutralFixture upper(NeutralFixture::Kind::Model);
  {
    NumberOperationScope scope(upper.budget);
    Model candidate = upper.model;
    candidate.values[1].value = upper.rational("3");
    require(!verifyExactLraModel(upper.view(), candidate).verified(),
            "non-strict upper violation was accepted");
  }
  NeutralFixture lower(NeutralFixture::Kind::Model);
  {
    NumberOperationScope scope(lower.budget);
    Model candidate = lower.model;
    candidate.values[1].value = lower.rational("-3");
    require(!verifyExactLraModel(lower.view(), candidate).verified(),
            "non-strict lower violation was accepted");
  }
  std::cout << "CORRUPT 31 non-strict-upper-and-lower REJECTED\n";

  rejectModel(0, "noncanonical-model-order", [](auto&, Model& model) {
    std::swap(model.values[0], model.values[1]);
  });
  hugeTruncation();
}

void activeBoundSnapshotChecks()
{
  for (auto kind : {NeutralFixture::Kind::Model, NeutralFixture::Kind::Conflict})
  {
    NeutralFixture fixture(kind);
    auto verify = [&](NumberBudget* budget = nullptr) {
      NumberOperationScope scope(budget == nullptr ? fixture.budget : *budget);
      return kind == NeutralFixture::Kind::Model
                 ? verifyExactLraModel(fixture.view(), fixture.model)
                 : verifyExactLraConflict(fixture.view(), fixture.conflict);
    };
    std::reverse(fixture.active_bounds.begin(), fixture.active_bounds.end());
    require(verify().verified(), "active bounds need not be sorted");
    const auto original = fixture.active_bounds;
    fixture.active_bounds.push_back(original.front());
    require(verify().error == VerificationError::InternalError,
            "duplicate active bound escaped snapshot audit");
    fixture.active_bounds = original;
    fixture.active_bounds.back() = BoundRef(
        CoreGeneration{UINT64_C(0x0000000200000001)}, original.back().ordinal());
    require(verify().error == VerificationError::InternalError,
            "foreign active bound with matching ordinal escaped snapshot audit");
    fixture.active_bounds.back() = BoundRef(fixture.generation, 999);
    require(verify().error == VerificationError::InternalError,
            "out-of-range active bound escaped snapshot audit");

    fixture.active_bounds = original;
    fixture.pending_conflict_bound = fixture.active_bounds.back();
    fixture.active_bounds.pop_back();
    require(verify().verified(), "pending bound must remain valid support");
    fixture.active_bounds.push_back(*fixture.pending_conflict_bound);
    require(verify().error == VerificationError::InternalError,
            "pending bound duplicated in active set escaped snapshot audit");
    fixture.active_bounds.pop_back();
    fixture.pending_conflict_bound = BoundRef(
        CoreGeneration{UINT64_C(0x0000000200000001)}, original.back().ordinal());
    require(verify().error == VerificationError::InternalError,
            "foreign pending bound escaped snapshot audit");
    fixture.pending_conflict_bound = BoundRef(fixture.generation, 999);
    require(verify().error == VerificationError::InternalError,
            "out-of-range pending bound escaped snapshot audit");

    fixture.active_bounds = original;
    fixture.pending_conflict_bound.reset();
    NumberLimits tiny = limits;
    tiny.maximum_allocation_bytes = 1;
    NumberBudget restricted(tiny);
    require(verify(&restricted).error == VerificationError::ResourceLimit &&
                restricted.metrics().preflight_stops != 0,
            "active-bound index allocation must respect the verification budget");
    require(verify().verified(), "resource refusal changed the snapshot");
  }
  std::cout << "VERIFY active-bound-index-identities-and-budget PASS\n";
}

void resultShapes()
{
  NeutralFixture fixture(NeutralFixture::Kind::Conflict);
  NumberOperationScope scope(fixture.budget);
  Model model{fixture.tag,
              {{fixture.x, fixture.rational("0")},
               {fixture.y, fixture.rational("0")}}};
  Conflict conflict = fixture.conflict;
  require(!exactLraCheckResultShapeValid(
              CheckResult{CheckStatus::Consistent, std::nullopt,
                          std::nullopt}),
          "Consistent without model shape was accepted");
  require(!exactLraCheckResultShapeValid(
              CheckResult{CheckStatus::Consistent, conflict, model}),
          "Consistent with conflict shape was accepted");
  require(!exactLraCheckResultShapeValid(
              CheckResult{CheckStatus::Conflict, std::nullopt,
                          std::nullopt}),
          "Conflict without conflict shape was accepted");
  require(!exactLraCheckResultShapeValid(
              CheckResult{CheckStatus::Conflict, conflict, model}),
          "Conflict with model shape was accepted");
  CheckStatus const stopped[] = {
      CheckStatus::Ready, CheckStatus::Interrupted,
      CheckStatus::ResourceLimit, CheckStatus::InternalError};
  for (CheckStatus status : stopped)
  {
    require(!exactLraCheckResultShapeValid(
                CheckResult{status, std::nullopt, model}),
            "stopped status with model was accepted");
    require(!exactLraCheckResultShapeValid(
                CheckResult{status, conflict, std::nullopt}),
            "stopped status with conflict was accepted");
  }
  require(!exactLraAssertResultShapeValid(
              AssertResult{InputStatus::ResourceLimit, conflict}),
          "failed assertion with witness was accepted");
  require(exactLraAssertResultShapeValid(
              AssertResult{InputStatus::Accepted, conflict}),
          "valid immediate-conflict shape was rejected");
  std::cout << "CORRUPT 32 illegal-result-shapes REJECTED\n";
}

void resourceMapping()
{
  NeutralFixture fixture(NeutralFixture::Kind::Conflict);
  NumberBudget restricted(
      NumberLimits{50000, 0, UINT64_C(1048576), UINT64_C(1024)});
  {
    NumberOperationScope scope(restricted);
    require(verifyExactLraConflict(fixture.view(), fixture.conflict).error ==
                VerificationError::ResourceLimit,
            "conflict verifier did not map exact resource stop");
  }
  restricted.resetAccounting();
  {
    NeutralFixture model_fixture(NeutralFixture::Kind::Model);
    NumberOperationScope scope(restricted);
    require(verifyExactLraModel(model_fixture.view(), model_fixture.model)
                    .error == VerificationError::ResourceLimit,
            "model verifier did not map exact resource stop");
  }
  std::cout << "VERIFY verifier-resource-mapping PASS\n";
}

}  // namespace

int main()
{
  try
  {
    conflictCorruptions();
    modelCorruptions();
    activeBoundSnapshotChecks();
    resultShapes();
    resourceMapping();
    std::cout << "PASS corruption\n";
    return EXIT_SUCCESS;
  }
  catch (std::exception const& error)
  {
    std::cerr << "FAIL corruption: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
}
