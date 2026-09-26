#include "LraAtomRegistry.h"

#include "ASTRealConst.h"
#include "stp/STPManager/STPManager.h"

#include <algorithm>
#include <atomic>
#include <limits>
#include <map>
#include <new>
#include <set>
#include <sstream>
#include <utility>

namespace stp::lra {

namespace {

std::atomic<std::uint64_t> next_registry_domain{1};

std::uint64_t allocateDomain()
{
  std::uint64_t current =
      next_registry_domain.load(std::memory_order_relaxed);
  for (;;)
  {
    if (current == 0 || current == std::numeric_limits<std::uint64_t>::max())
      throw RegistryFailure(RegistryFailureKind::ResourceLimit,
                            "LRA registry domain space exhausted");
    if (next_registry_domain.compare_exchange_weak(
            current, current + 1, std::memory_order_relaxed,
            std::memory_order_relaxed))
      return current;
  }
}

std::uint64_t allocateSerial(std::uint64_t& next, const char* name)
{
  if (next == 0 || next == std::numeric_limits<std::uint64_t>::max())
  {
    std::ostringstream out;
    out << name << " serial space exhausted";
    throw RegistryFailure(RegistryFailureKind::ResourceLimit, out.str());
  }
  return next++;
}

void advanceGeneration(std::uint64_t& generation)
{
  if (generation == std::numeric_limits<std::uint64_t>::max())
    throw RegistryFailure(RegistryFailureKind::ResourceLimit,
                          "LRA registry generation space exhausted");
  ++generation;
}

void incrementSaturating(std::uint64_t& value) noexcept
{
  if (value != std::numeric_limits<std::uint64_t>::max())
    ++value;
}

RegistryFailure translateNumberFailure(const NumberFailure& failure)
{
  RegistryFailureKind kind = RegistryFailureKind::Invalid;
  switch (failure.kind())
  {
    case NumberFailureKind::ResourceLimit:
      kind = RegistryFailureKind::ResourceLimit;
      break;
    case NumberFailureKind::AllocationFailure:
      kind = RegistryFailureKind::Invalid;
      break;
    case NumberFailureKind::InvalidText:
    case NumberFailureKind::ZeroDenominator:
    case NumberFailureKind::DivisionByZero:
    case NumberFailureKind::NonIntegerOperand:
    case NumberFailureKind::RangeError:
      kind = RegistryFailureKind::Invalid;
      break;
    case NumberFailureKind::InternalError:
      kind = RegistryFailureKind::Invalid;
      break;
  }
  return RegistryFailure(kind, failure.what());
}

RegistryFailure translateFrontendFailure(const FrontendFailure& failure)
{
  RegistryFailureKind kind = RegistryFailureKind::Invalid;
  switch (failure.kind())
  {
    case FrontendFailureKind::ResourceLimit:
      kind = RegistryFailureKind::ResourceLimit;
      break;
    case FrontendFailureKind::AllocationFailure:
      kind = RegistryFailureKind::Invalid;
      break;
    case FrontendFailureKind::Unsupported:
    case FrontendFailureKind::WrongSort:
    case FrontendFailureKind::Malformed:
      kind = RegistryFailureKind::Invalid;
      break;
    case FrontendFailureKind::InternalError:
      kind = RegistryFailureKind::Invalid;
      break;
  }
  return RegistryFailure(kind, failure.what());
}

std::string componentKey(FrontendRelation relation,
                         const std::string& row_key,
                         const ExactRational& threshold)
{
  std::ostringstream out;
  out << static_cast<unsigned>(relation) << ':' << row_key << ";b:"
      << threshold.canonicalFraction();
  return out.str();
}

// Substitute the aliases throughout, bottom up over an explicit stack: the
// formulas this rewrites are as deep as the traces they were unrolled from,
// and a call frame per level overflows on exactly those. The cache makes a
// shared subterm one rewrite, not one per path.
ASTNode rewriteAliases(STPMgr& manager, const ASTNode& node,
                       const ASTNodeMap& aliases, ASTNodeMap& cache)
{
  PreparationPoller poll(manager.preparation_control, PreparationStage::LraRegistry);
  struct Frame
  {
    ASTNode node;
    size_t next = 0;
    ASTVec children;
    bool changed = false;
  };
  auto settled = [&](const ASTNode& current) -> const ASTNode* {
    const auto replacement = aliases.find(current);
    if (replacement != aliases.end())
      return &replacement->second;
    const auto cached = cache.find(current);
    if (cached != cache.end())
      return &cached->second;
    if (current.Degree() == 0)
      return &cache.emplace(current, current).first->second;
    return nullptr;
  };
  if (const ASTNode* done = settled(node))
    return *done;
  std::vector<Frame> stack;
  auto open = [&](const ASTNode& current) {
    Frame frame;
    frame.node = current;
    frame.children.reserve(current.Degree());
    stack.push_back(std::move(frame));
  };
  open(node);
  ASTNode result;
  while (!stack.empty())
  {
    poll();
    Frame& frame = stack.back();
    if (frame.next < frame.node.Degree())
    {
      const ASTNode child = frame.node[frame.next++];
      if (const ASTNode* done = settled(child))
      {
        frame.changed = frame.changed || *done != child;
        frame.children.push_back(*done);
        continue;
      }
      open(child);
      continue;
    }
    const ASTNode built =
        frame.changed ? manager.CreateNode(frame.node.GetKind(), frame.children)
                      : frame.node;
    const ASTNode finished = frame.node;
    cache.emplace(finished, built);
    stack.pop_back();
    if (stack.empty())
    {
      result = built;
      break;
    }
    Frame& parent = stack.back();
    parent.changed = parent.changed || built != finished;
    parent.children.push_back(built);
  }
  return result;
}

template <class Id>
void requireDomain(Id id, std::uint64_t domain, const char* description)
{
  if (!id.valid() || id.domain != domain)
  {
    std::ostringstream out;
    out << "invalid or foreign " << description;
    throw RegistryFailure(RegistryFailureKind::Invalid, out.str());
  }
}

} // namespace

class LraAtomRegistryState final
{
public:
  struct StoredSymbol final
  {
    RegistrySymbol value;
    std::uint64_t frame_references = 0;
  };

  struct StoredRow final
  {
    RegistryRow value;
    std::uint64_t frame_references = 0;
  };

  struct StoredComponent final
  {
    RegistryComponent value;
    std::uint64_t frame_references = 0;
  };

  struct StoredEquality final
  {
    RegistryEqualityGroup value;
  };

  struct FrameRecord final
  {
    LraAssertionFrameId id;
    std::set<LraRegistrySymbolId> symbols;
    std::set<LraCanonicalRowId> rows;
    std::set<LraComponentId> components;
    std::set<LraEqualityGroupId> equalities;
    std::vector<ASTNode> registered_formulas;
  };

  explicit LraAtomRegistryState(std::uint64_t manager_domain)
      : domain(manager_domain)
  {
  }

  void swap(LraAtomRegistryState& other) noexcept
  {
    std::swap(domain, other.domain);
    std::swap(generation, other.generation);
    std::swap(next_symbol_serial, other.next_symbol_serial);
    std::swap(next_row_serial, other.next_row_serial);
    std::swap(next_component_serial, other.next_component_serial);
    std::swap(next_equality_serial, other.next_equality_serial);
    std::swap(next_frame_serial, other.next_frame_serial);
    std::swap(next_solve_epoch, other.next_solve_epoch);
    symbols.swap(other.symbols);
    rows.swap(other.rows);
    components.swap(other.components);
    equalities.swap(other.equalities);
    frames.swap(other.frames);
    active_symbol_by_frontend.swap(other.active_symbol_by_frontend);
    active_row_by_key.swap(other.active_row_by_key);
    active_component_by_key.swap(other.active_component_by_key);
    std::swap(metrics, other.metrics);
  }

  std::uint64_t domain;
  std::uint64_t generation = 1;
  std::uint64_t next_symbol_serial = 1;
  std::uint64_t next_row_serial = 1;
  std::uint64_t next_component_serial = 1;
  std::uint64_t next_equality_serial = 1;
  std::uint64_t next_frame_serial = 1;
  std::uint64_t next_solve_epoch = 1;

  std::map<LraRegistrySymbolId, StoredSymbol> symbols;
  std::map<LraCanonicalRowId, StoredRow> rows;
  std::map<LraComponentId, StoredComponent> components;
  std::map<LraEqualityGroupId, StoredEquality> equalities;
  std::map<LraAssertionFrameId, FrameRecord> frames;
  std::map<LraSymbolId, LraRegistrySymbolId> active_symbol_by_frontend;
  std::map<std::string, LraCanonicalRowId> active_row_by_key;
  std::map<std::string, LraComponentId> active_component_by_key;
  LraRegistryMetrics metrics;
};

namespace {

LraAtomRegistryState::StoredSymbol& requireSymbol(
    LraAtomRegistryState& state, LraRegistrySymbolId id)
{
  requireDomain(id, state.domain, "registry symbol ID");
  const auto found = state.symbols.find(id);
  if (found == state.symbols.end())
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "unknown or inactive registry symbol ID");
  return found->second;
}

LraAtomRegistryState::StoredRow& requireRow(LraAtomRegistryState& state,
                                            LraCanonicalRowId id)
{
  requireDomain(id, state.domain, "canonical row ID");
  const auto found = state.rows.find(id);
  if (found == state.rows.end())
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "unknown or inactive canonical row ID");
  return found->second;
}

LraAtomRegistryState::StoredComponent& requireComponent(
    LraAtomRegistryState& state, LraComponentId id)
{
  requireDomain(id, state.domain, "component ID");
  const auto found = state.components.find(id);
  if (found == state.components.end())
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "unknown or inactive component ID");
  return found->second;
}

/* What one registration adds, so that a failure part-way can take it back.
 * Registration only ever inserts -- new entries into the four stores and
 * their active-key indexes, ids into the frame's sets with a reference on
 * the stored entry, source records onto existing components, the formula
 * onto the frame -- and moves the serial counters, the generation and the
 * metrics; so undoing is erasing what was inserted and putting the scalars
 * back. Every entry is recorded after the insertion it describes, and the
 * vectors are sized from the formula up front, so recording cannot fail
 * once registration has begun and undo cannot throw.
 *
 * Registering into a copy of the whole state and swapping it in on success
 * gave the same guarantee, at the cost of copying every entry the registry
 * holds on every assertion: on a file with two hundred assertions over
 * eighteen thousand components, a sixth of the run. */
struct RegistrationJournal final
{
  RegistrationJournal(const LraAtomRegistryState& state,
                      const PreregisteredFormula& formula)
      : generation(state.generation),
        next_symbol_serial(state.next_symbol_serial),
        next_row_serial(state.next_row_serial),
        next_component_serial(state.next_component_serial),
        next_equality_serial(state.next_equality_serial),
        metrics(state.metrics)
  {
    std::size_t terms = 0;
    for (const PredicateRegistration& occurrence : formula.predicates)
      terms += occurrence.payload.lhs_minus_rhs.terms.size();
    symbols.reserve(terms);
    frame_symbols.reserve(terms);
    rows.reserve(formula.predicates.size());
    frame_rows.reserve(formula.predicates.size());
    components.reserve(formula.predicates.size());
    frame_components.reserve(formula.predicates.size());
    sources_grown.reserve(formula.predicates.size());
    equalities.reserve(formula.equalities.size());
    frame_equalities.reserve(formula.equalities.size());
  }

  void undo(LraAtomRegistryState& state,
            LraAtomRegistryState::FrameRecord& frame) noexcept
  {
    if (formula_recorded)
      frame.registered_formulas.pop_back();
    for (LraComponentId id : sources_grown)
    {
      auto it = state.components.find(id);
      if (it != state.components.end() && !it->second.value.sources.empty())
        it->second.value.sources.pop_back();
    }
    for (LraEqualityGroupId id : frame_equalities)
      frame.equalities.erase(id);
    for (LraComponentId id : frame_components)
    {
      frame.components.erase(id);
      auto it = state.components.find(id);
      if (it != state.components.end())
        --it->second.frame_references;
    }
    for (LraCanonicalRowId id : frame_rows)
    {
      frame.rows.erase(id);
      auto it = state.rows.find(id);
      if (it != state.rows.end())
        --it->second.frame_references;
    }
    for (LraRegistrySymbolId id : frame_symbols)
    {
      frame.symbols.erase(id);
      auto it = state.symbols.find(id);
      if (it != state.symbols.end())
        --it->second.frame_references;
    }
    for (LraEqualityGroupId id : equalities)
      state.equalities.erase(id);
    for (LraComponentId id : components)
    {
      auto it = state.components.find(id);
      if (it == state.components.end())
        continue;
      state.active_component_by_key.erase(it->second.value.canonical_key);
      state.components.erase(it);
    }
    for (LraCanonicalRowId id : rows)
    {
      auto it = state.rows.find(id);
      if (it == state.rows.end())
        continue;
      state.active_row_by_key.erase(it->second.value.canonical_key);
      state.rows.erase(it);
    }
    for (LraRegistrySymbolId id : symbols)
    {
      auto it = state.symbols.find(id);
      if (it == state.symbols.end())
        continue;
      state.active_symbol_by_frontend.erase(it->second.value.frontend_id);
      state.symbols.erase(it);
    }
    state.generation = generation;
    state.next_symbol_serial = next_symbol_serial;
    state.next_row_serial = next_row_serial;
    state.next_component_serial = next_component_serial;
    state.next_equality_serial = next_equality_serial;
    state.metrics = metrics;
  }

  std::uint64_t generation;
  std::uint64_t next_symbol_serial;
  std::uint64_t next_row_serial;
  std::uint64_t next_component_serial;
  std::uint64_t next_equality_serial;
  LraRegistryMetrics metrics;
  std::vector<LraRegistrySymbolId> symbols;
  std::vector<LraCanonicalRowId> rows;
  std::vector<LraComponentId> components;
  std::vector<LraEqualityGroupId> equalities;
  std::vector<LraRegistrySymbolId> frame_symbols;
  std::vector<LraCanonicalRowId> frame_rows;
  std::vector<LraComponentId> frame_components;
  std::vector<LraEqualityGroupId> frame_equalities;
  std::vector<LraComponentId> sources_grown;
  bool formula_recorded = false;
};

void addFrameSymbol(LraAtomRegistryState& state,
                    LraAtomRegistryState::FrameRecord& frame,
                    LraRegistrySymbolId id, RegistrationJournal& journal)
{
  if (frame.symbols.insert(id).second)
  {
    ++requireSymbol(state, id).frame_references;
    journal.frame_symbols.push_back(id);
  }
}

void addFrameRow(LraAtomRegistryState& state,
                 LraAtomRegistryState::FrameRecord& frame,
                 LraCanonicalRowId id, RegistrationJournal& journal)
{
  if (frame.rows.insert(id).second)
  {
    ++requireRow(state, id).frame_references;
    journal.frame_rows.push_back(id);
  }
}

void addFrameComponent(LraAtomRegistryState& state,
                       LraAtomRegistryState::FrameRecord& frame,
                       LraComponentId id, RegistrationJournal& journal)
{
  if (frame.components.insert(id).second)
  {
    ++requireComponent(state, id).frame_references;
    journal.frame_components.push_back(id);
  }
}

void updateActiveMetrics(LraAtomRegistryState& state) noexcept
{
  state.metrics.active_frames = state.frames.size();
  state.metrics.active_symbols = state.symbols.size();
  state.metrics.active_rows = state.rows.size();
  state.metrics.active_components = state.components.size();
  state.metrics.active_equality_groups = state.equalities.size();
}

} // namespace

RegistryFailure::RegistryFailure(RegistryFailureKind kind, std::string detail)
    : std::runtime_error(std::move(detail)), kind_(kind)
{
}

LraAtomRegistry::LraAtomRegistry(STPMgr& manager) : manager_(manager)
{
  try
  {
    // Frontend construction is the only supported creation path for the
    // manager-owned exact-number state and preserves its frozen lifetime.
    Frontend frontend(manager_);
    (void)frontend;
    if (manager_.lra_ast_state->atom_registry == nullptr)
      manager_.lra_ast_state->atom_registry =
          new LraAtomRegistryState(allocateDomain());
  }
  catch (const RegistryFailure&)
  {
    throw;
  }
  catch (const std::bad_alloc&)
  {
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "allocation failure creating LRA atom registry");
  }
}

LraAtomRegistryState& LraAtomRegistry::state()
{
  if (manager_.lra_ast_state == nullptr ||
      manager_.lra_ast_state->atom_registry == nullptr)
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "manager has no live LRA atom registry");
  return *manager_.lra_ast_state->atom_registry;
}

const LraAtomRegistryState& LraAtomRegistry::state() const
{
  if (manager_.lra_ast_state == nullptr ||
      manager_.lra_ast_state->atom_registry == nullptr)
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "manager has no live LRA atom registry");
  return *manager_.lra_ast_state->atom_registry;
}

LraAssertionFrameId LraAtomRegistry::pushAssertionFrame()
{
  try
  {
    NumberOperationScope operation(manager_.lra_ast_state->number_budget);
    LraAtomRegistryState staged = state();
    const LraAssertionFrameId id{
        staged.domain,
        allocateSerial(staged.next_frame_serial, "assertion-frame")};
    staged.frames.emplace(
        id, LraAtomRegistryState::FrameRecord{id, {}, {}, {}, {}, {}});
    advanceGeneration(staged.generation);
    updateActiveMetrics(staged);
    state().swap(staged);
    return id;
  }
  catch (const NumberFailure& failure)
  {
    throw translateNumberFailure(failure);
  }
  catch (const std::bad_alloc&)
  {
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "allocation failure pushing LRA assertion frame");
  }
}

RegisteredLraFormula LraAtomRegistry::registerFormula(
    const PreregisteredFormula& formula, LraAssertionFrameId frame_id)
{
  try
  {
    PreparationPoller poll(manager_.preparation_control, PreparationStage::LraRegistry);
    Frontend frontend(manager_);
    if (!frontend.ownsNode(formula.boolean_formula))
      throw RegistryFailure(RegistryFailureKind::Invalid,
                            "registered formula belongs to another manager");
    if (formula.registry_generation == 0 ||
        formula.registry_generation != frontend.registryGeneration())
      throw RegistryFailure(RegistryFailureKind::Invalid,
                            "stale frontend preregistration generation");

    NumberOperationScope operation(manager_.lra_ast_state->number_budget);
    LraAtomRegistryState& staged = state();
    requireDomain(frame_id, staged.domain, "assertion-frame ID");
    auto frame_it = staged.frames.find(frame_id);
    if (frame_it == staged.frames.end())
      throw RegistryFailure(RegistryFailureKind::Invalid,
                            "unknown or popped assertion frame");
    LraAtomRegistryState::FrameRecord& frame = frame_it->second;
    RegistrationJournal journal(staged, formula);
    try
    {
    ASTNodeMap aliases;
    std::map<std::uint64_t, LraComponentId> component_by_opaque_node;
    std::map<std::uint64_t, LraEqualityGroupId> group_by_frontend_id;
    std::vector<LraComponentId> component_occurrences;
    component_occurrences.reserve(formula.predicates.size());

    for (const PredicateRegistration& occurrence : formula.predicates)
    {
      poll();
      if (occurrence.predicate_id == 0 ||
          !frontend.ownsNode(occurrence.opaque_atom))
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "malformed frontend predicate registration");
      Frontend::validateCanonical(occurrence.payload.lhs_minus_rhs);
      if (occurrence.payload.lhs_minus_rhs.terms.empty() ||
          occurrence.payload.relation == FrontendRelation::Equal)
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "non-ordinary component reached the atom registry");

      std::vector<RegistryMonomial> registry_terms;
      registry_terms.reserve(occurrence.payload.lhs_minus_rhs.terms.size());
      for (const LinearMonomial& term : occurrence.payload.lhs_minus_rhs.terms)
      {
        poll();
        auto active = staged.active_symbol_by_frontend.find(term.symbol);
        LraRegistrySymbolId symbol_id;
        if (active == staged.active_symbol_by_frontend.end())
        {
          symbol_id = LraRegistrySymbolId{
              staged.domain,
              allocateSerial(staged.next_symbol_serial, "registry-symbol")};
          RegistrySymbol symbol{symbol_id, term.symbol,
                                frontend.symbolNode(term.symbol)};
          staged.symbols.emplace(
              symbol_id,
              LraAtomRegistryState::StoredSymbol{std::move(symbol), 0});
          journal.symbols.push_back(symbol_id);
          staged.active_symbol_by_frontend.emplace(term.symbol, symbol_id);
        }
        else
        {
          symbol_id = active->second;
          RegistrySymbol& symbol = requireSymbol(staged, symbol_id).value;
          if (symbol.frontend_id != term.symbol ||
              symbol.symbol != frontend.symbolNode(term.symbol))
            throw RegistryFailure(RegistryFailureKind::Invalid,
                                  "registry symbol identity changed");
        }
        addFrameSymbol(staged, frame, symbol_id, journal);
        registry_terms.push_back(RegistryMonomial{symbol_id, term.coefficient});
      }

      const std::string row_key =
          frontend.exportCoefficientVector(occurrence.payload.lhs_minus_rhs);
      LraCanonicalRowId row_id;
      const auto existing_row = staged.active_row_by_key.find(row_key);
      if (existing_row == staged.active_row_by_key.end())
      {
        row_id = LraCanonicalRowId{
            staged.domain,
            allocateSerial(staged.next_row_serial, "canonical-row")};
        RegistryRow row{row_id, std::move(registry_terms), row_key};
        staged.rows.emplace(
            row_id, LraAtomRegistryState::StoredRow{std::move(row), 0});
        journal.rows.push_back(row_id);
        staged.active_row_by_key.emplace(row_key, row_id);
      }
      else
      {
        row_id = existing_row->second;
        RegistryRow& row = requireRow(staged, row_id).value;
        if (row.canonical_key != row_key ||
            row.terms.size() != registry_terms.size())
          throw RegistryFailure(RegistryFailureKind::Invalid,
                                "canonical row hash-cons collision");
        for (std::size_t i = 0; i < row.terms.size(); ++i)
        {
          poll();
          if (row.terms[i].symbol != registry_terms[i].symbol ||
              row.terms[i].coefficient != registry_terms[i].coefficient)
            throw RegistryFailure(RegistryFailureKind::Invalid,
                                  "canonical row hash-cons collision");
        }
        incrementSaturating(staged.metrics.row_deduplications);
      }
      addFrameRow(staged, frame, row_id, journal);

      ExactRational threshold = -occurrence.payload.lhs_minus_rhs.constant;
      const std::string predicate_key =
          componentKey(occurrence.payload.relation, row_key, threshold);
      LraComponentId component_id;
      ASTNode representative;
      const auto existing_component =
          staged.active_component_by_key.find(predicate_key);
      if (existing_component == staged.active_component_by_key.end())
      {
        component_id = LraComponentId{
            staged.domain,
            allocateSerial(staged.next_component_serial, "component")};
        RegistryComponent component{component_id,
                                    row_id,
                                    occurrence.payload.relation,
                                    std::move(threshold),
                                    occurrence.opaque_atom,
                                    predicate_key,
                                    {}};
        representative = component.opaque_atom;
        staged.components.emplace(
            component_id,
            LraAtomRegistryState::StoredComponent{std::move(component), 0});
        journal.components.push_back(component_id);
        staged.active_component_by_key.emplace(predicate_key, component_id);
      }
      else
      {
        component_id = existing_component->second;
        RegistryComponent& component =
            requireComponent(staged, component_id).value;
        if (component.row != row_id ||
            component.relation != occurrence.payload.relation ||
            component.threshold != threshold ||
            component.canonical_key != predicate_key)
          throw RegistryFailure(RegistryFailureKind::Invalid,
                                "component hash-cons collision");
        representative = component.opaque_atom;
        incrementSaturating(staged.metrics.component_deduplications);
      }
      addFrameComponent(staged, frame, component_id, journal);
      aliases.emplace(occurrence.opaque_atom, representative);
      if (!component_by_opaque_node
               .emplace(occurrence.opaque_atom.GetNodeNum(), component_id)
               .second)
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "duplicate frontend opaque predicate identity");
      component_occurrences.push_back(component_id);
    }

    std::vector<LraEqualityGroupId> equality_groups;
    equality_groups.reserve(formula.equalities.size());
    for (const EqualityRegistration& equality : formula.equalities)
    {
      poll();
      if (equality.equality_group_id == 0 ||
          !frontend.ownsNode(equality.source_equality) ||
          !frontend.ownsNode(equality.equality_atom) ||
          !frontend.ownsNode(equality.less_equal_atom) ||
          !frontend.ownsNode(equality.greater_equal_atom))
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "malformed frontend equality registration");
      const auto less =
          component_by_opaque_node.find(equality.less_equal_atom.GetNodeNum());
      const auto greater = component_by_opaque_node.find(
          equality.greater_equal_atom.GetNodeNum());
      if (less == component_by_opaque_node.end() ||
          greater == component_by_opaque_node.end() || less->second == greater->second)
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "incomplete equality component registration");
      if (requireComponent(staged, less->second).value.relation !=
              FrontendRelation::LessEqual ||
          requireComponent(staged, greater->second).value.relation !=
              FrontendRelation::GreaterEqual)
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "equality component relation mismatch");

      const LraEqualityGroupId group_id{
          staged.domain,
          allocateSerial(staged.next_equality_serial, "equality-group")};
      RegistryEqualityGroup group{group_id,
                                  frame_id,
                                  equality.source_equality,
                                  equality.equality_atom,
                                  less->second,
                                  greater->second};
      staged.equalities.emplace(
          group_id,
          LraAtomRegistryState::StoredEquality{std::move(group)});
      journal.equalities.push_back(group_id);
      if (frame.equalities.insert(group_id).second)
        journal.frame_equalities.push_back(group_id);
      if (!group_by_frontend_id
               .emplace(equality.equality_group_id, group_id)
               .second)
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "duplicate frontend equality-group identity");
      equality_groups.push_back(group_id);
    }

    // Source ownership is appended only after every equality group exists, so
    // an equality component can carry a checked registry group rather than a
    // transient frontend serial.
    for (const PredicateRegistration& occurrence : formula.predicates)
    {
      poll();
      const auto component =
          component_by_opaque_node.find(occurrence.opaque_atom.GetNodeNum());
      if (component == component_by_opaque_node.end())
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "predicate occurrence lost during registration");
      LraEqualityGroupId registry_group;
      if (occurrence.equality_group_id != 0)
      {
        const auto group =
            group_by_frontend_id.find(occurrence.equality_group_id);
        if (group == group_by_frontend_id.end())
          throw RegistryFailure(RegistryFailureKind::Invalid,
                                "component names an unknown equality group");
        registry_group = group->second;
      }
      else if (occurrence.equality_component == EqualityComponent::LessEqual ||
               occurrence.equality_component ==
                   EqualityComponent::GreaterEqual)
      {
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "equality component has no equality group");
      }
      requireComponent(staged, component->second)
          .value.sources.push_back(RegistrySourceOwnership{
              frame_id,
              occurrence.payload.source,
              registry_group,
              occurrence.equality_component});
      journal.sources_grown.push_back(component->second);
    }

    ASTNodeMap cache;
    ASTNode canonical_formula =
        rewriteAliases(manager_, formula.boolean_formula, aliases, cache);
    if (Frontend::containsRealSyntax(canonical_formula))
      throw RegistryFailure(RegistryFailureKind::Invalid,
                            "Real syntax remained after registry aliasing");
    poll.check();
    frame.registered_formulas.push_back(canonical_formula);
    journal.formula_recorded = true;
    incrementSaturating(staged.metrics.formulas_registered);
    advanceGeneration(staged.generation);
    updateActiveMetrics(staged);
    const LraRegistryTag new_tag{staged.domain, staged.generation};
    return RegisteredLraFormula{canonical_formula,
                                new_tag,
                                frame_id,
                                std::move(component_occurrences),
                                std::move(equality_groups)};
    }
    catch (...)
    {
      journal.undo(staged, frame);
      throw;
    }
  }
  catch (const RegistryFailure&)
  {
    throw;
  }
  catch (const FrontendFailure& failure)
  {
    throw translateFrontendFailure(failure);
  }
  catch (const NumberFailure& failure)
  {
    throw translateNumberFailure(failure);
  }
  catch (const std::bad_alloc&)
  {
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "allocation failure registering LRA formula");
  }
}

void LraAtomRegistry::popAssertionFrame(LraAssertionFrameId frame_id)
{
  try
  {
    NumberOperationScope operation(manager_.lra_ast_state->number_budget);
    LraAtomRegistryState staged = state();
    requireDomain(frame_id, staged.domain, "assertion-frame ID");
    auto frame_it = staged.frames.find(frame_id);
    if (frame_it == staged.frames.end())
      throw RegistryFailure(RegistryFailureKind::Invalid,
                            "unknown or already-popped assertion frame");
    const LraAtomRegistryState::FrameRecord frame = frame_it->second;

    for (LraEqualityGroupId id : frame.equalities)
    {
      const auto found = staged.equalities.find(id);
      if (found == staged.equalities.end() || found->second.value.frame != frame_id)
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "equality-group frame ownership is corrupt");
      staged.equalities.erase(found);
    }

    for (LraComponentId id : frame.components)
    {
      auto found = staged.components.find(id);
      if (found == staged.components.end() || found->second.frame_references == 0)
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "component reference accounting is corrupt");
      RegistryComponent& component = found->second.value;
      component.sources.erase(
          std::remove_if(component.sources.begin(), component.sources.end(),
                         [frame_id](const RegistrySourceOwnership& source) {
                           return source.frame == frame_id;
                         }),
          component.sources.end());
      if (--found->second.frame_references == 0)
      {
        if (!component.sources.empty())
          throw RegistryFailure(RegistryFailureKind::Invalid,
                                "unreachable component retained sources");
        staged.active_component_by_key.erase(component.canonical_key);
        staged.components.erase(found);
      }
    }

    for (LraCanonicalRowId id : frame.rows)
    {
      auto found = staged.rows.find(id);
      if (found == staged.rows.end() || found->second.frame_references == 0)
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "row reference accounting is corrupt");
      if (--found->second.frame_references == 0)
      {
        staged.active_row_by_key.erase(found->second.value.canonical_key);
        staged.rows.erase(found);
      }
    }

    for (LraRegistrySymbolId id : frame.symbols)
    {
      auto found = staged.symbols.find(id);
      if (found == staged.symbols.end() || found->second.frame_references == 0)
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "symbol reference accounting is corrupt");
      if (--found->second.frame_references == 0)
      {
        staged.active_symbol_by_frontend.erase(found->second.value.frontend_id);
        staged.symbols.erase(found);
      }
    }

    staged.frames.erase(frame_it);
    incrementSaturating(staged.metrics.frames_popped);
    advanceGeneration(staged.generation);
    updateActiveMetrics(staged);
    state().swap(staged);
  }
  catch (const RegistryFailure&)
  {
    throw;
  }
  catch (const NumberFailure& failure)
  {
    throw translateNumberFailure(failure);
  }
  catch (const std::bad_alloc&)
  {
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "allocation failure popping LRA assertion frame");
  }
}

LraRegistrySnapshot LraAtomRegistry::activeSnapshot(
    const PreparationControl* preparation) const
{
  try
  {
    PreparationPoller poll(preparation, PreparationStage::LraRegistry);
    NumberOperationScope operation(manager_.lra_ast_state->number_budget);
    const LraAtomRegistryState& current = state();
    LraRegistrySnapshot snapshot;
    snapshot.tag = {current.domain, current.generation};
    snapshot.symbols.reserve(current.symbols.size());
    snapshot.rows.reserve(current.rows.size());
    snapshot.components.reserve(current.components.size());
    snapshot.equalities.reserve(current.equalities.size());
    for (const auto& entry : current.symbols)
    {
      poll();
      snapshot.symbols.push_back(entry.second.value);
    }
    for (const auto& entry : current.rows)
    {
      poll();
      snapshot.rows.push_back(entry.second.value);
    }
    for (const auto& entry : current.components)
    {
      poll();
      snapshot.components.push_back(entry.second.value);
    }
    for (const auto& entry : current.equalities)
    {
      poll();
      snapshot.equalities.push_back(entry.second.value);
    }

    std::sort(snapshot.symbols.begin(), snapshot.symbols.end(),
              [&poll](const RegistrySymbol& lhs, const RegistrySymbol& rhs) {
                poll();
                return lhs.frontend_id < rhs.frontend_id;
              });
    poll.check();
    return snapshot;
  }
  catch (const RegistryFailure&)
  {
    throw;
  }
  catch (const NumberFailure& failure)
  {
    throw translateNumberFailure(failure);
  }
  catch (const std::bad_alloc&)
  {
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "allocation failure copying LRA registry snapshot");
  }
}

LraRegistrySnapshot
LraAtomRegistry::frameSnapshot(LraAssertionFrameId frame_id,
                               const PreparationControl* preparation) const
{
  try
  {
    PreparationPoller poll(preparation, PreparationStage::LraRegistry);
    NumberOperationScope operation(manager_.lra_ast_state->number_budget);
    const LraAtomRegistryState& current = state();
    requireDomain(frame_id, current.domain, "assertion-frame ID");
    const auto frame_it = current.frames.find(frame_id);
    if (frame_it == current.frames.end())
      throw RegistryFailure(RegistryFailureKind::Invalid,
                            "unknown or popped assertion frame");
    const LraAtomRegistryState::FrameRecord& frame = frame_it->second;

    LraRegistrySnapshot snapshot;
    snapshot.tag = {current.domain, current.generation};
    snapshot.symbols.reserve(frame.symbols.size());
    snapshot.rows.reserve(frame.rows.size());
    snapshot.components.reserve(frame.components.size());
    snapshot.equalities.reserve(frame.equalities.size());
    for (LraRegistrySymbolId id : frame.symbols)
    {
      poll();
      snapshot.symbols.push_back(current.symbols.at(id).value);
    }
    for (LraCanonicalRowId id : frame.rows)
    {
      poll();
      snapshot.rows.push_back(current.rows.at(id).value);
    }
    for (LraComponentId id : frame.components)
    {
      poll();
      RegistryComponent component = current.components.at(id).value;
      component.sources.erase(
          std::remove_if(component.sources.begin(), component.sources.end(),
                         [frame_id](const RegistrySourceOwnership& source) {
                           return source.frame != frame_id;
                         }),
          component.sources.end());
      if (component.sources.empty())
        throw RegistryFailure(RegistryFailureKind::Invalid,
                              "frame component has no frame-local source");
      snapshot.components.push_back(std::move(component));
    }
    for (LraEqualityGroupId id : frame.equalities)
    {
      poll();
      snapshot.equalities.push_back(current.equalities.at(id).value);
    }

    std::sort(snapshot.symbols.begin(), snapshot.symbols.end(),
              [&poll](const RegistrySymbol& lhs, const RegistrySymbol& rhs) {
                poll();
                return lhs.frontend_id < rhs.frontend_id;
              });
    poll.check();
    return snapshot;
  }
  catch (const RegistryFailure&)
  {
    throw;
  }
  catch (const NumberFailure& failure)
  {
    throw translateNumberFailure(failure);
  }
  catch (const std::bad_alloc&)
  {
    throw RegistryFailure(
        RegistryFailureKind::Invalid,
        "allocation failure copying frame-local LRA registry snapshot");
  }
  catch (const std::out_of_range&)
  {
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "registry frame closure is corrupt");
  }
}

bool LraAtomRegistry::validateSnapshotIdentity(
    const LraRegistrySnapshot& snapshot) const noexcept
{
  try
  {
    const LraAtomRegistryState& current = state();
    return snapshot.tag ==
               LraRegistryTag{current.domain, current.generation} &&
           snapshot.symbols.size() == current.symbols.size() &&
           snapshot.rows.size() == current.rows.size() &&
           snapshot.components.size() == current.components.size() &&
           snapshot.equalities.size() == current.equalities.size();
  }
  catch (...)
  {
    return false;
  }
}

bool LraAtomRegistry::validateFrameSnapshotIdentity(
    const LraRegistrySnapshot& snapshot,
    LraAssertionFrameId frame_id) const noexcept
{
  try
  {
    const LraAtomRegistryState& current = state();
    if (!frame_id.valid() || frame_id.domain != current.domain ||
        snapshot.tag != LraRegistryTag{current.domain, current.generation})
      return false;
    const auto frame_it = current.frames.find(frame_id);
    if (frame_it == current.frames.end())
      return false;
    const LraAtomRegistryState::FrameRecord& frame = frame_it->second;
    return snapshot.symbols.size() == frame.symbols.size() &&
           snapshot.rows.size() == frame.rows.size() &&
           snapshot.components.size() == frame.components.size() &&
           snapshot.equalities.size() == frame.equalities.size();
  }
  catch (...)
  {
    return false;
  }
}

bool LraAtomRegistry::validateSnapshot(
    const LraRegistrySnapshot& snapshot) const noexcept
{
  try
  {
    const LraAtomRegistryState& current = state();
    if (!validateSnapshotIdentity(snapshot))
      return false;
    for (const RegistrySymbol& symbol : snapshot.symbols)
    {
      const auto found = current.symbols.find(symbol.id);
      if (found == current.symbols.end() ||
          found->second.value.frontend_id != symbol.frontend_id ||
          found->second.value.symbol != symbol.symbol)
        return false;
    }
    for (const RegistryRow& row : snapshot.rows)
    {
      const auto found = current.rows.find(row.id);
      if (found == current.rows.end() ||
          found->second.value.canonical_key != row.canonical_key)
        return false;
    }
    for (const RegistryComponent& component : snapshot.components)
    {
      const auto found = current.components.find(component.id);
      if (found == current.components.end() ||
          found->second.value.canonical_key != component.canonical_key ||
          found->second.value.opaque_atom != component.opaque_atom)
        return false;
    }
    for (const RegistryEqualityGroup& equality : snapshot.equalities)
    {
      const auto found = current.equalities.find(equality.id);
      if (found == current.equalities.end() ||
          found->second.value.equality_atom != equality.equality_atom ||
          found->second.value.less_equal_component !=
              equality.less_equal_component ||
          found->second.value.greater_equal_component !=
              equality.greater_equal_component)
        return false;
    }
    return true;
  }
  catch (...)
  {
    return false;
  }
}

bool LraAtomRegistry::validateFrameSnapshot(
    const LraRegistrySnapshot& snapshot,
    LraAssertionFrameId frame_id) const noexcept
{
  try
  {
    const LraAtomRegistryState& current = state();
    if (!validateFrameSnapshotIdentity(snapshot, frame_id))
      return false;
    const auto frame_it = current.frames.find(frame_id);
    const LraAtomRegistryState::FrameRecord& frame = frame_it->second;
    for (const RegistrySymbol& symbol : snapshot.symbols)
    {
      const auto found = current.symbols.find(symbol.id);
      if (frame.symbols.count(symbol.id) != 1 ||
          found == current.symbols.end() ||
          found->second.value.frontend_id != symbol.frontend_id ||
          found->second.value.symbol != symbol.symbol)
        return false;
    }
    for (const RegistryRow& row : snapshot.rows)
    {
      const auto found = current.rows.find(row.id);
      if (frame.rows.count(row.id) != 1 || found == current.rows.end() ||
          found->second.value.canonical_key != row.canonical_key)
        return false;
    }
    for (const RegistryComponent& component : snapshot.components)
    {
      const auto found = current.components.find(component.id);
      if (frame.components.count(component.id) != 1 ||
          found == current.components.end() || component.sources.empty() ||
          found->second.value.canonical_key != component.canonical_key ||
          found->second.value.opaque_atom != component.opaque_atom)
        return false;
      for (const RegistrySourceOwnership& source : component.sources)
        if (source.frame != frame_id)
          return false;
    }
    for (const RegistryEqualityGroup& equality : snapshot.equalities)
    {
      const auto found = current.equalities.find(equality.id);
      if (frame.equalities.count(equality.id) != 1 ||
          found == current.equalities.end() || equality.frame != frame_id ||
          found->second.value.equality_atom != equality.equality_atom ||
          found->second.value.less_equal_component !=
              equality.less_equal_component ||
          found->second.value.greater_equal_component !=
              equality.greater_equal_component)
        return false;
    }
    return true;
  }
  catch (...)
  {
    return false;
  }
}

LraRegistryTag LraAtomRegistry::tag() const noexcept
{
  try
  {
    const LraAtomRegistryState& current = state();
    return {current.domain, current.generation};
  }
  catch (...)
  {
    return {};
  }
}

std::uint64_t LraAtomRegistry::allocateSolveEpoch()
{
  LraAtomRegistryState& current = state();
  const std::uint64_t epoch =
      allocateSerial(current.next_solve_epoch, "solve-epoch");
  incrementSaturating(current.metrics.solve_epochs_allocated);
  return epoch;
}

void LraAtomRegistry::destructiveReset()
{
  try
  {
    NumberOperationScope operation(manager_.lra_ast_state->number_budget);
    LraAtomRegistryState staged = state();
    staged.symbols.clear();
    staged.rows.clear();
    staged.components.clear();
    staged.equalities.clear();
    staged.frames.clear();
    staged.active_symbol_by_frontend.clear();
    staged.active_row_by_key.clear();
    staged.active_component_by_key.clear();
    incrementSaturating(staged.metrics.destructive_resets);
    advanceGeneration(staged.generation);
    updateActiveMetrics(staged);
    state().swap(staged);
  }
  catch (const RegistryFailure&)
  {
    throw;
  }
  catch (const NumberFailure& failure)
  {
    throw translateNumberFailure(failure);
  }
  catch (const std::bad_alloc&)
  {
    throw RegistryFailure(RegistryFailureKind::Invalid,
                          "allocation failure resetting LRA registry");
  }
}

LraRegistryMetrics LraAtomRegistry::metrics() const noexcept
{
  try
  {
    return state().metrics;
  }
  catch (...)
  {
    return {};
  }
}

#if defined(STP_LRA_TEST_FAULT_INJECTION)
void LraAtomRegistry::testSetNextSolveEpoch(std::uint64_t next)
{
  state().next_solve_epoch = next;
}

void LraAtomRegistry::testSetNextFrameSerial(std::uint64_t next)
{
  state().next_frame_serial = next;
}
#endif

void destroyLraAtomRegistryState(LraAtomRegistryState* state) noexcept
{
  delete state;
}

} // namespace stp::lra

namespace stp {
namespace {

lra::LraAssertionFrameId decodeAssertionFrame(
    const std::pair<std::uint64_t, std::uint64_t>& value) noexcept
{
  return {value.first, value.second};
}

std::pair<std::uint64_t, std::uint64_t> encodeAssertionFrame(
    lra::LraAssertionFrameId value) noexcept
{
  return {value.domain, value.serial};
}


} // namespace

void STPMgr::PushLraAssertionFrame()
{
  // Do not instantiate an LRA object for a manager that has only seen
  // non-Real input. Once frame tracking is active, mirror each public push.
  if (lra_ast_state == nullptr)
    return;
  const bool lra_active = lra_ast_state->atom_registry != nullptr &&
                          !lra_ast_state->assertion_frames.empty();
  const bool bridge_active = false;
  if (!lra_active && !bridge_active)
    return;

  bool lra_pushed = false;
  try
  {
    if (lra_active)
    {
      lra::LraAtomRegistry registry(*this);
      lra_ast_state->assertion_frames.push_back(
          encodeAssertionFrame(registry.pushAssertionFrame()));
      lra_pushed = true;
    }
  }
  catch (...)
  {
    if (lra_pushed)
    {
      lra::LraAtomRegistry registry(*this);
      registry.popAssertionFrame(
          decodeAssertionFrame(lra_ast_state->assertion_frames.back()));
      lra_ast_state->assertion_frames.pop_back();
    }
    throw;
  }
}

void STPMgr::PopLraAssertionFrame()
{
  if (lra_ast_state == nullptr)
    return;
  if (lra_ast_state->atom_registry != nullptr &&
      !lra_ast_state->assertion_frames.empty())
  {
    lra::LraAtomRegistry registry(*this);
    registry.popAssertionFrame(
        decodeAssertionFrame(lra_ast_state->assertion_frames.back()));
    lra_ast_state->assertion_frames.pop_back();
  }
}

void STPMgr::RegisterLraAssertion(const ASTNode& assertion)
{
  lra::Frontend frontend(*this);
  lra::LraAtomRegistry registry(*this);

  // Real use can begin below levels pushed while the feature was dormant.
  // Materialize all missing frames oldest-first before recording this source.
  while (lra_ast_state->assertion_frames.size() < _asserts.size())
    lra_ast_state->assertion_frames.push_back(
        encodeAssertionFrame(registry.pushAssertionFrame()));
  if (lra_ast_state->assertion_frames.size() != _asserts.size() ||
      lra_ast_state->assertion_frames.empty())
    throw lra::RegistryFailure(
        lra::RegistryFailureKind::Invalid,
        "LRA registry/public assertion-frame stack mismatch");

  const lra::PreregisteredFormula preregistered = frontend.preregister(assertion);
  (void)registry.registerFormula(
      preregistered,
      decodeAssertionFrame(lra_ast_state->assertion_frames.back()));
}

} // namespace stp
