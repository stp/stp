#include "LraPresolve.h"
#include "LraReconstruction.h"
#include "LraFrontend.h"
#include "stp/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolverFactory.h"

#include <iostream>
#include <limits>
#include <memory>
#include <sstream>
#include <stdexcept>

namespace
{
using namespace stp;
using namespace stp::lra;

void require(bool condition, const char* message)
{
  if (!condition)
    throw std::runtime_error(message);
}

void onlyMonotone(STPMgr& manager)
{
  auto& flags = manager.UserFlags;
  flags.lra_presolve_subst = false;
  flags.lra_presolve_propagate = false;
  flags.lra_presolve_rows = false;
  flags.lra_presolve_bounds = false;
  flags.lra_presolve_unconstrained = false;
  flags.lra_presolve_monotone = true;
  flags.lra_relu_bounds = UserDefinedFlags::OptionMode::OFF;
  flags.lra_relu_lp = UserDefinedFlags::OptionMode::OFF;
  flags.lra_model_reconstruction = UserDefinedFlags::OptionMode::OFF;
}

void monotone()
{
  STPMgr manager;
  SimplifyingNodeFactory factory(*manager.hashingNodeFactory, manager);
  manager.defaultNodeFactory = &factory;
  onlyMonotone(manager);
  const auto x = manager.CreateSourceSymbol("x", SourceSort::real());
  const auto y = manager.CreateSourceSymbol("y", SourceSort::real());
  const auto z = manager.CreateSourceSymbol("z", SourceSort::real());
  const auto one = manager.CreateRealConst("1");
  const auto two = manager.CreateRealConst("2");
  const auto atom = [&](Kind kind, const ASTNode& a, const ASTNode& b) {
    return manager.CreateRealPredicate(kind, a, b);
  };
  const auto add = [&](const ASTNode& a, const ASTNode& b) {
    return manager.CreateRealTerm(REAL_ADD, ASTVec{a, b});
  };
  const auto input = manager.CreateNode(AND, ASTVec{
      atom(REAL_GT, x, add(y, one)), atom(REAL_GE, x, add(z, two)),
      atom(EQ, y, manager.CreateRealConst("1/3")),
      atom(EQ, z, manager.CreateRealConst("2/3"))});
  LraReconstruction reconstruction;
  const auto result = presolveForSolve(manager, input, nullptr, &reconstruction);
  require(result != input && reconstruction.original == input &&
              reconstruction.definitions.size() == 1 &&
              reconstruction.definitions.front().symbol == x,
          "multiple lower bounds must eliminate only x");
  Frontend frontend(manager);
  RealModel model(frontend.numberLimits(), {{y, "1", "3"}, {z, "2", "3"}},
                  ASTVec{x, y, z});
  model.reconstruct(reconstruction.definitions);
  require(model.stringsFor(x).canonical_fraction == "11/3" &&
              acceptsRealFormula(input, [&](const ASTNode& p) {
                return model.predicateValue(p);
              }), "maximum witness must satisfy every original bound");

  // The first removal exposes a variable with opposing initial directions.
  // A local worklist reaches the fixed point without repeating all presolve.
  const auto chain = manager.CreateNode(AND, ASTVec{
      atom(REAL_LT, z, x), atom(REAL_LT, add(x, one), y),
      atom(REAL_LT, add(x, two), y)});
  LraReconstruction chained;
  require(presolveForSolve(manager, chain, nullptr, &chained) == manager.ASTTrue &&
              chained.definitions.size() == 2,
          "monotone incidence worklist must finish successive eliminations");
  RealModel chain_model(frontend.numberLimits(), {}, ASTVec{x, y, z});
  chain_model.reconstruct(chained.definitions);
  require(acceptsRealFormula(chain, [&](const ASTNode& p) {
            return chain_model.predicateValue(p);
          }), "reverse elimination order must reconstruct the chain");

  // A later affine elimination supplies dependencies of an earlier witness.
  manager.UserFlags.lra_model_reconstruction = UserDefinedFlags::OptionMode::ON;
  const auto affine = manager.CreateNode(AND, ASTVec{
      atom(REAL_GT, x, y), atom(REAL_GT, x, add(y, one)),
      atom(EQ, y, add(z, two)), atom(EQ, z, one)});
  LraReconstruction combined;
  require(presolveForSolve(manager, affine, nullptr, &combined) == manager.ASTTrue,
          "affine definitions may be removed after monotone bounds");
  RealModel combined_model(frontend.numberLimits(), {}, ASTVec{x, y, z});
  combined_model.reconstruct(combined.definitions);
  require(acceptsRealFormula(affine, [&](const ASTNode& p) {
            return combined_model.predicateValue(p);
          }), "affine and monotone records must share one dependency order");
  const auto cancelled = manager.CreateNode(AND, ASTVec{
      atom(REAL_GT, x, y), atom(EQ, y,
          manager.CreateRealTerm(REAL_SUB, ASTVec{x, x}))});
  LraReconstruction cancellation;
  require(presolveForSolve(manager, cancelled, nullptr, &cancellation) == manager.ASTTrue,
          "cancelled occurrences must not retain eliminated symbols");
  RealModel cancellation_model(frontend.numberLimits(), {}, ASTVec{x, y});
  cancellation_model.reconstruct(cancellation.definitions);
  require(acceptsRealFormula(cancelled, [&](const ASTNode& p) {
            return cancellation_model.predicateValue(p);
          }), "cancelled occurrences must not introduce a reconstruction cycle");
  manager.UserFlags.lra_model_reconstruction = UserDefinedFlags::OptionMode::OFF;

  // Work refusal cannot publish a partial formula or a partial witness list.
  for (const std::uint64_t cap : {0U, 1U, 30U, 80U})
  {
    manager.UserFlags.lra_presolve_monotone_work = cap;
    LraReconstruction limited;
    const auto reduced = presolveForSolve(manager, input, nullptr, &limited);
    require((reduced == input && limited.definitions.empty()) ||
                (reduced == result && limited.definitions.size() == 1),
            "bounded elimination must be transactional");
  }
  manager.UserFlags.lra_presolve_monotone_work = 1000000;
  require(presolveForSolve(manager, input) == input,
          "elimination requires a reconstruction destination");
  manager.noteIntroducedSymbol(x);
  LraReconstruction protected_symbol;
  require(presolveForSolve(manager, input, nullptr, &protected_symbol) == input &&
              protected_symbol.definitions.empty(),
          "introduced symbols cannot be chosen as free witnesses");
  std::unique_ptr<SATSolver> solver(createSATSolver(manager.UserFlags));
  solver->setDeadline(std::chrono::steady_clock::time_point::min());
  LraReconstruction expired;
  require(presolveForSolve(manager, input, solver.get(), &expired) == input &&
              expired.definitions.empty() && manager.soft_timeout_expired,
          "expired presolve must leave no reconstruction");
}

void definitionsBeforeMonotone()
{
  STPMgr manager;
  SimplifyingNodeFactory factory(*manager.hashingNodeFactory, manager);
  manager.defaultNodeFactory = &factory;
  onlyMonotone(manager);
  const auto x = manager.CreateSourceSymbol("definition_x", SourceSort::real());
  const auto y = manager.CreateSourceSymbol("definition_y", SourceSort::real());
  const auto z = manager.CreateSourceSymbol("definition_z", SourceSort::real());
  const auto one = manager.CreateRealConst("1");
  const auto two = manager.CreateRealConst("2");
  const auto add = [&](const ASTNode& a, const ASTNode& b) {
    return manager.CreateRealTerm(REAL_ADD, ASTVec{a, b});
  };
  const auto definition = manager.CreateRealPredicate(EQ, y, add(x, one));
  const auto bounds = manager.CreateNode(AND, ASTVec{
      manager.CreateRealPredicate(REAL_GT, x, one),
      manager.CreateRealPredicate(REAL_GT, x, two)});
  const auto input = manager.CreateNode(AND, ASTVec{
      definition, manager.CreateRealPredicate(EQ, z, add(y, two)), bounds});
  Frontend frontend(manager);
  for (bool substitute : {false, true})
    for (auto replay : {UserDefinedFlags::OptionMode::OFF,
                        UserDefinedFlags::OptionMode::ON})
      for (unsigned rounds : {1U, 3U})
      {
        manager.UserFlags.lra_presolve_subst = substitute;
        manager.UserFlags.lra_model_reconstruction = replay;
        manager.UserFlags.lra_presolve_rounds = rounds;
        LraReconstruction reconstruction;
        require(presolveForSolve(manager, input, nullptr, &reconstruction) ==
                    manager.ASTTrue && reconstruction.definitions.size() == 3,
                "dead definition chains must expose monotone variables in the first round");
        RealModel model(frontend.numberLimits(), {}, ASTVec{x, y, z});
        model.reconstruct(reconstruction.definitions);
        require(acceptsRealFormula(input, [&](const ASTNode& atom) {
                  return model.predicateValue(atom);
                }), "monotone values must replay before the affine definitions using them");
      }

  onlyMonotone(manager);
  manager.UserFlags.lra_presolve_rounds = 1;
  const auto cycle = manager.CreateNode(AND, ASTVec{
      definition, manager.CreateRealPredicate(EQ, x, add(y, one)), bounds});
  LraReconstruction cyclic;
  require(presolveForSolve(manager, cycle, nullptr, &cyclic) == cycle &&
              cyclic.definitions.empty(), "cyclic definitions cannot be erased");

  const auto protected_input = manager.CreateNode(AND, definition, bounds);
  manager.noteIntroducedSymbol(y);
  LraReconstruction protected_result;
  require(presolveForSolve(manager, protected_input, nullptr, &protected_result) ==
              protected_input && protected_result.definitions.empty(),
          "early reconstruction must retain introduced targets");

  // Interrupt every work boundary of a successful dead-definition removal,
  // including the last boundary after the result formula has been rebuilt.
  std::size_t visits = 0;
  LraReconstruction complete;
  (void)removeDeadRealDefinitions(manager, input, complete, [&]() { ++visits; });
  require(!complete.definitions.empty(), "the cancellation probe must eliminate a definition");
  for (std::size_t cutoff = 1; cutoff <= visits; ++cutoff)
  {
    std::size_t count = 0;
    LraReconstruction cancelled;
    bool stopped = false;
    try
    {
      (void)removeDeadRealDefinitions(manager, input, cancelled, [&]() {
        if (++count == cutoff)
          throw PreparationInterrupted(PreparationStage::LraPresolve,
                                       std::chrono::steady_clock::now());
      });
    }
    catch (const PreparationInterrupted&) { stopped = true; }
    require(stopped && cancelled.definitions.empty(),
            "cancelled definition extraction must not publish partial witnesses");
  }
}

void localMonotoneRefusal()
{
  STPMgr manager;
  SimplifyingNodeFactory factory(*manager.hashingNodeFactory, manager);
  manager.defaultNodeFactory = &factory;
  onlyMonotone(manager);
  const auto x = manager.CreateSourceSymbol("opaque_x", SourceSort::real());
  const auto y = manager.CreateSourceSymbol("opaque_y", SourceSort::real());
  const auto z = manager.CreateSourceSymbol("opaque_z", SourceSort::real());
  const auto b = manager.CreateSourceSymbol("opaque_b", SourceSort::boolean());
  const auto one = manager.CreateRealConst("1");
  const auto two = manager.CreateRealConst("2");
  const auto ten = manager.CreateRealConst("10");
  const auto bounds = manager.CreateNode(AND, ASTVec{
      manager.CreateRealPredicate(REAL_GT, x, one),
      manager.CreateRealPredicate(REAL_GT, x, two)});
  const auto ite = manager.CreateRealTerm(ITE, ASTVec{b, y, z});
  auto shared = ite;
  for (unsigned i = 0; i < 40; ++i)
    shared = manager.CreateRealTerm(REAL_ADD, ASTVec{shared, shared});
  const auto opaque = manager.CreateRealPredicate(REAL_LE, shared, ten);
  const auto input = manager.CreateNode(AND, bounds, opaque);
  manager.UserFlags.lra_presolve_monotone_work = 5000;
  LraReconstruction independent;
  require(presolveForSolve(manager, input, nullptr, &independent) == opaque &&
              independent.definitions.size() == 1 &&
              independent.definitions.front().symbol == x,
          "shared opaque DAGs must only block the variables occurring in them");
  Frontend frontend(manager);
  RealModel model(frontend.numberLimits(), {}, ASTVec{x, y, z});
  model.reconstruct(independent.definitions);
  require(acceptsRealFormula(bounds, [&](const ASTNode& atom) {
            return model.predicateValue(atom);
          }), "independent monotone reconstruction must satisfy the removed bounds");

  for (const auto& term : {manager.CreateRealTerm(ITE, ASTVec{b, x, y}),
                          manager.CreateRealTerm(REAL_ADD, ASTVec{x, ite})})
  {
    const auto pinned = manager.CreateNode(AND, bounds,
        manager.CreateRealPredicate(REAL_LE, term, ten));
    LraReconstruction refused;
    require(presolveForSolve(manager, pinned, nullptr, &refused) == pinned &&
                refused.definitions.empty(),
            "every variable of an unsupported atom must be blocked permanently");
  }
  manager.UserFlags.lra_presolve_monotone_work = 20;
  LraReconstruction limited;
  require(presolveForSolve(manager, input, nullptr, &limited) == input &&
              limited.definitions.empty(), "opaque scans must obey the shared work budget");
}

void repeatedPresolve()
{
  STPMgr manager;
  SimplifyingNodeFactory factory(*manager.hashingNodeFactory, manager);
  manager.defaultNodeFactory = &factory;
  onlyMonotone(manager);
  auto& flags = manager.UserFlags;
  flags.lra_presolve_monotone = false;
  flags.lra_presolve_unconstrained = true;
  flags.lra_presolve_rows = true;
  const auto x = manager.CreateSourceSymbol("repeat_x", SourceSort::real());
  const auto first = manager.CreateRealPredicate(REAL_LT, x, manager.CreateRealConst("1"));
  const auto second = manager.CreateRealPredicate(REAL_LT, x, manager.CreateRealConst("2"));
  const auto input = manager.CreateNode(AND, ASTVec{first, second});
  LraReconstruction baseline;
  require(presolveForSolve(manager, input, nullptr, &baseline) == first,
          "one round drops the weaker row after the single-use pass");
  flags.lra_presolve_rounds = 2;
  LraReconstruction repeated;
  const auto result = presolveForSolve(manager, input, nullptr, &repeated);
  require(result.GetKind() == EQ && repeated.original == input &&
              repeated.definitions.empty(),
          "the second round must witness the newly single-use variable");
  Frontend frontend(manager);
  RealModel model(frontend.numberLimits(), {{x, "0", "1"}}, ASTVec{x});
  require(model.predicateValue(result) && acceptsRealFormula(input,
              [&](const ASTNode& atom) { return model.predicateValue(atom); }),
          "the repeated presolve witness must satisfy the original input");

  struct Capture
  {
    std::ostringstream output;
    std::streambuf* saved = std::cerr.rdbuf(output.rdbuf());
    ~Capture() { std::cerr.rdbuf(saved); }
  } capture;
  flags.stats_flag = true;
  flags.lra_presolve_rounds = 8;
  LraReconstruction stable;
  require(presolveForSolve(manager, input, nullptr, &stable) == result,
          "extra rounds must stabilize");
  const auto log = capture.output.str();
  require(log.find("index=3, changed=0") != std::string::npos &&
              log.find("index=4") == std::string::npos &&
              log.find("1 rows dropped") != std::string::npos &&
              log.find("index=2, changed=1, definitions=0, fixed=0, rows=0") !=
                  std::string::npos,
          "fixed-point stopping and per-call counters must survive repetition");

  // Observe the completed first-round report, then interrupt at the next
  // preparation boundary. This tests cancellation between rounds without
  // timing races or hard-coding the number of within-round checks.
  capture.output.str("");
  const auto stop = [](void* opaque, PreparationStage stage) {
    return stage == PreparationStage::LraPresolve &&
        static_cast<std::ostringstream*>(opaque)->str().find("index=1") !=
            std::string::npos;
  };
  const PreparationControl control(PreparationControl::Clock::time_point::max(),
                                   nullptr, stop, &capture.output);
  LraReconstruction interrupted;
  bool stopped = false;
  {
    PreparationScope scope(manager.preparation_control, control);
    try { (void)presolveForSolve(manager, input, nullptr, &interrupted); }
    catch (const PreparationInterrupted& failure)
    {
      stopped = failure.stage == PreparationStage::LraPresolve;
    }
  }
  require(stopped && !manager.HasRealModel() &&
              capture.output.str().find("index=2") == std::string::npos,
          "cancellation between rounds must not proceed to the next round");
  flags.stats_flag = false;
  LraReconstruction recovered;
  require(presolveForSolve(manager, input, nullptr, &recovered) == result,
          "a fresh query must recover after cancellation");
}

void substitutionGuards()
{
  STPMgr manager;
  SimplifyingNodeFactory factory(*manager.hashingNodeFactory, manager);
  manager.defaultNodeFactory = &factory;
  onlyMonotone(manager);
  auto& flags = manager.UserFlags;
  flags.lra_presolve_monotone = false;
  flags.lra_presolve_subst = true;
  flags.stats_flag = true;
  const auto x = manager.CreateSourceSymbol("growth_x", SourceSort::real());
  const auto y = manager.CreateSourceSymbol("growth_y", SourceSort::real());
  const auto z = manager.CreateSourceSymbol("growth_z", SourceSort::real());
  const auto one = manager.CreateRealConst("1");
  const auto two = manager.CreateRealConst("2");
  const auto three = manager.CreateRealConst("3");
  const auto add = [&](const ASTNode& a, const ASTNode& b) {
    return manager.CreateRealTerm(REAL_ADD, ASTVec{a, b});
  };
  const auto mul = [&](const ASTNode& a, const ASTNode& b) {
    return manager.CreateRealTerm(REAL_MUL, ASTVec{a, b});
  };
  const auto atom = [&](Kind kind, const ASTNode& a, const ASTNode& b) {
    return manager.CreateRealPredicate(kind, a, b);
  };
  const auto input = manager.CreateNode(AND, ASTVec{
      atom(EQ, x, add(y, one)), atom(REAL_GT, x, z),
      atom(REAL_LT, x, add(z, three))});
  const auto run = [&](const ASTNode& formula) {
    struct Capture
    {
      std::ostringstream output;
      std::streambuf* saved = std::cerr.rdbuf(output.rdbuf());
      ~Capture() { std::cerr.rdbuf(saved); }
    } capture;
    LraReconstruction reconstruction;
    const auto result = presolveForSolve(manager, formula, nullptr, &reconstruction);
    require(reconstruction.definitions.empty(),
            "substitution must retain its equations instead of publishing witnesses");
    return std::make_pair(result, capture.output.str());
  };
  const auto counter = [](const std::string& log, const std::string& field) {
    const auto pos = log.find(field + "=");
    require(pos != std::string::npos, "missing substitution counter");
    return std::stoull(log.substr(pos + field.size() + 1));
  };

  flags.lra_presolve_subst_work = 0;
  const auto baseline = run(input);
  require(baseline.first != input &&
              baseline.second.find("LRA substitution round:") == std::string::npos,
          "zero growth must preserve the unguarded substitution path");
  flags.lra_presolve_subst_growth = 1000;
  require(run(input).first == input, "zero work must retain every input equation");
  flags.lra_presolve_subst_work = 10000;
  const auto complete = run(input);
  require(complete.first == baseline.first &&
              complete.second.find("stop=none") != std::string::npos,
          "sufficient allowance must preserve the full substitution result");
  const auto work = counter(complete.second, "work");
  const auto growth = counter(complete.second, "growth");
  require(work > 0 && work < 1000 && growth > 0 && growth < 1000,
          "the guard probe must exercise bounded work and growth");

  // Every refusal boundary, including the final output measurement, returns
  // the original formula. No prefix of the rewrite may escape.
  for (std::uint64_t cap = 0; cap < work; ++cap)
  {
    flags.lra_presolve_subst_work = cap;
    const auto limited = run(input);
    require(limited.first == input && counter(limited.second, "work") == cap &&
                limited.second.find("refusals=1, stop=work") != std::string::npos,
            "work refusal must be transactional at every boundary");
  }
  flags.lra_presolve_subst_work = 10000;
  for (std::uint64_t cap = 1; cap < growth; ++cap)
  {
    flags.lra_presolve_subst_growth = cap;
    const auto limited = run(input);
    require(limited.first == input && counter(limited.second, "growth") <= cap &&
                limited.second.find("refusals=1, stop=growth") != std::string::npos,
            "growth refusal must retain defining equations and unrewritten uses");
  }
  flags.lra_presolve_subst_growth = growth;
  flags.lra_presolve_subst_work = work;
  require(run(input).first == baseline.first, "exact budget endpoints must be usable");
  flags.lra_presolve_rounds = 3;
  const auto repeated = run(input);
  require(repeated.first == baseline.first &&
              repeated.second.find("index=2, work=" + std::to_string(work)) !=
                  std::string::npos &&
              repeated.second.find("refusals=1, stop=work") != std::string::npos,
          "later rounds must not replenish the substitution allowance");

  flags.lra_presolve_rounds = 1;
  flags.lra_presolve_subst_growth = 1000;
  flags.lra_presolve_subst_work = 10000;
  const auto chain = manager.CreateNode(AND, ASTVec{
      atom(EQ, x, add(y, one)), atom(EQ, y, add(z, one)),
      atom(REAL_GT, x, three)});
  const auto first_round = run(chain);
  flags.lra_presolve_rounds = 3;
  const auto all_rounds = run(chain);
  require(all_rounds.first != first_round.first,
          "the chain probe must expose a substitution in a later round");
  flags.lra_presolve_subst_growth = counter(first_round.second, "growth");
  const auto shared_growth = run(chain);
  require(shared_growth.first == first_round.first &&
              shared_growth.second.find("refusals=1, stop=growth") != std::string::npos,
          "later rounds must not replenish the growth allowance either");

  // Gaussian elimination has no syntactic x=t candidate. Its normalization
  // and generated solved form must obey the same limits.
  flags.lra_presolve_rounds = 1;
  flags.lra_presolve_subst_growth = std::numeric_limits<std::uint64_t>::max();
  flags.lra_presolve_subst_work = std::numeric_limits<std::uint64_t>::max();
  const auto gaussian = manager.CreateNode(AND, ASTVec{
      atom(EQ, add(mul(two, x), mul(three, y)), add(z, one)),
      atom(REAL_GT, x, z)});
  const auto solved = run(gaussian);
  require(solved.first != gaussian && counter(solved.second, "growth") > 0,
          "Gaussian rewriting must work with overflow-safe maximum allowances");
  Frontend frontend(manager);
  for (int xv = -2; xv <= 2; ++xv)
    for (int yv = -2; yv <= 2; ++yv)
      for (int zv = -2; zv <= 2; ++zv)
      {
        RealModel model(frontend.numberLimits(),
            {{x, std::to_string(xv), "1"}, {y, std::to_string(yv), "1"},
             {z, std::to_string(zv), "1"}}, ASTVec{x, y, z});
        const auto value = [&](const ASTNode& formula) {
          return acceptsRealFormula(formula, [&](const ASTNode& predicate) {
            return model.predicateValue(predicate);
          });
        };
        require(value(gaussian) == value(solved.first) &&
                    value(input) == value(baseline.first),
                "substitution must preserve the original assignments exactly");
      }
  const auto gaussian_work = counter(solved.second, "work");
  for (std::uint64_t cap = 0; cap < gaussian_work; ++cap)
  {
    flags.lra_presolve_subst_work = cap;
    require(run(gaussian).first == gaussian,
            "Gaussian normalization must share the transactional work guard");
  }

  // Exponentially many paths, but only forty distinct addition nodes. Both
  // sizing and rewriting must respect sharing, including conjunctions.
  flags.lra_presolve_subst_growth = 1000;
  flags.lra_presolve_subst_work = 10000;
  auto shared = x;
  for (unsigned i = 0; i < 40; ++i)
    shared = add(shared, shared);
  auto conjunction = atom(REAL_GT, shared, z);
  for (unsigned i = 0; i < 40; ++i)
    conjunction = manager.hashingNodeFactory->CreateNode(AND, ASTVec{conjunction, conjunction});
  const auto dag = manager.hashingNodeFactory->CreateNode(
      AND, ASTVec{atom(EQ, x, add(y, one)), conjunction});
  const auto shared_result = run(dag);
  require(shared_result.first != dag &&
              shared_result.second.find("stop=none") != std::string::npos &&
              counter(shared_result.second, "added_nodes") < 100,
          "growth and traversal accounting must count shared DAG nodes once");

  // Stop at every preparation poll observed on a successful guarded rewrite.
  // A cancellation is not a heuristic refusal and must propagate to its owner.
  struct Stop
  {
    std::size_t calls = 0, limit = std::numeric_limits<std::size_t>::max();
    static bool observe(void* opaque, PreparationStage stage)
    {
      auto& self = *static_cast<Stop*>(opaque);
      return stage == PreparationStage::LraPresolve && ++self.calls == self.limit;
    }
  } stop;
  const PreparationControl observed(PreparationControl::Clock::time_point::max(),
                                    nullptr, Stop::observe, &stop);
  {
    PreparationScope scope(manager.preparation_control, observed);
    (void)run(dag);
  }
  const auto polls = stop.calls;
  for (std::size_t cutoff = 1; cutoff <= polls; ++cutoff)
  {
    stop.calls = 0;
    stop.limit = cutoff;
    const PreparationControl control(PreparationControl::Clock::time_point::max(),
                                     nullptr, Stop::observe, &stop);
    PreparationScope scope(manager.preparation_control, control);
    bool interrupted = false;
    try { (void)run(dag); }
    catch (const PreparationInterrupted&) { interrupted = true; }
    require(interrupted && !manager.HasRealModel(),
            "guarded substitution must not swallow query cancellation");
  }
  require(run(dag).first == shared_result.first,
          "fresh queries must recover their substitution allowance after cancellation");
}
} // namespace

int main()
{
  try
  {
    monotone();
    definitionsBeforeMonotone();
    localMonotoneRefusal();
    repeatedPresolve();
    substitutionGuards();
    std::cout << "PASS monotone and repeated presolve, reconstruction and substitution guards\n";
    return 0;
  }
  catch (const std::exception& error)
  {
    std::cerr << error.what() << '\n';
    return 1;
  }
}
