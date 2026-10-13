// In-memory adapter for Satsuma 1.4 and STP's SAT backends.
#include "stp/Sat/Satsuma.h"
#include "stp/AIG/CNF.h"
#include "stp/Sat/SATSolver.h"
#include "stp/STPManager/STPManager.h"
#include "satsuma.h"

#include <chrono>
#include <climits>
#include <limits>
#include <stdexcept>

namespace stp
{
namespace
{
class SolverOutput final : public satsuma::cnf_output
{
  SATSolver& solver;
  PreparationPoller poll;
  const uint32_t originalVariables;
  SATSolver::vec_literals clauseBuffer;

public:
  uint64_t variables = 0, clauses = 0, literals = 0;

  SolverOutput(STPMgr& manager, SATSolver& solver, uint32_t originalVariables)
      : solver(solver),
        poll(manager.preparation_control, PreparationStage::ClauseLoading),
        originalVariables(originalVariables)
  {
  }

  void begin(int variableCount, int clauseCount) override
  {
    if (variableCount < 0 || variableCount == INT_MAX || clauseCount < 0)
      throw std::runtime_error("Satsuma returned an invalid CNF size");
    variables = variableCount;
    clauses = clauseCount;
    // CNF uses 1..n. Keep STP's unused variable 0 and allocate the whole
    // output domain, just as ordinary STP clause loading does. Keeping
    // the original domain also makes unconstrained input bits modelable.
    const uint32_t count = std::max(originalVariables,
                                   static_cast<uint32_t>(variableCount) + 1);
    while (solver.nVars() < count)
    {
      poll();
      solver.newVar();
    }
  }

  void clause(const int* input, size_t count) override
  {
    poll();
    // Even if the backend has found UNSAT, count the whole output formula.
    literals += count;
    if (!solver.okay())
      return;
    clauseBuffer.clear();
    for (size_t i = 0; i < count; ++i)
    {
      poll();
      const int literal = input[i];
      if (literal == 0 || literal == INT_MIN)
        throw std::runtime_error("Satsuma returned an invalid literal");
      const uint32_t variable = static_cast<uint32_t>(std::abs(literal));
      if (variable > variables)
        throw std::runtime_error("Satsuma literal exceeds the output variable count");
      clauseBuffer.push(SATSolver::mkLit(variable, literal < 0));
    }
    solver.addClause(clauseBuffer);
  }

  void end() override { poll.check(); }
};
}

bool addSatsumaCnfToSolver(STPMgr& manager, SATSolver& solver, const CNF& cnf,
                         const std::vector<std::vector<int>>& extraClauses)
{
  // Match the wrapper's variable guard; Satsuma's clause arena uses int
  // offsets, and its graph carries two literal vertices per variable.
  if (cnf.varCount() - 1 >= 5000000 ||
      cnf.clauseCount() + extraClauses.size() > INT_MAX / 4 ||
      cnf.literalCount() > INT_MAX / 2)
    return false;

  // Check this before constructing Satsuma's duplicate clause and graph
  // structures. A declined request leaves the original CNF for the ordinary
  // clause loader and does not submit anything to the backend.
  const bool quick = manager.UserFlags.satsuma_profile == "quick";
  const int inputLimit = manager.UserFlags.satsuma_input_limit >= 0
      ? manager.UserFlags.satsuma_input_limit : quick ? 1000000 : -1;
  if (inputLimit >= 0)
  {
    uint64_t inputSize = cnf.varCount() - 1 + cnf.literalCount();
    for (const auto& extra : extraClauses)
      inputSize += extra.size();
    if (inputSize > static_cast<uint64_t>(inputLimit))
      return false;
  }

  const auto start = std::chrono::steady_clock::now();
  PreparationPoller poll(manager.preparation_control, PreparationStage::ClauseLoading);
  cnf2wl formula;
  formula.reserve(static_cast<int>(cnf.varCount() - 1),
                  static_cast<int>(cnf.clauseCount() + extraClauses.size()));
  std::vector<int> clause;
  const auto addLiteral = [&](int packed) {
    poll();
    const int variable = packed >> 1;
    if (variable <= 0 || static_cast<uint32_t>(variable) >= cnf.varCount())
      throw std::runtime_error("STP CNF literal outside its variable domain");
    clause.push_back((packed & 1) ? -variable : variable);
  };
  for (CNF::ClauseCursor c = cnf.clauses(); c.next();)
  {
    poll();
    clause.clear();
    for (const int* lit = c.begin(); lit != c.end(); ++lit)
      addLiteral(*lit);
    formula.add_clause(clause);
  }
  uint64_t extraLiterals = 0;
  for (const auto& extra : extraClauses)
  {
    clause.clear();
    bool valid = true;
    for (const int literal : extra)
      if (static_cast<uint32_t>(literal >> 1) >= cnf.varCount())
        valid = false;
    if (!valid)
      continue;
    for (const int literal : extra)
      addLiteral(literal);
    extraLiterals += clause.size();
    formula.add_clause(clause);
  }

  SolverOutput output(manager, solver, cnf.varCount());
  empty_stream silent;
  satsuma::tracker tracker;
  tracker.h_silent = true;
  satsuma::preprocessor preprocessor;
  preprocessor.set_tracker(&tracker);
  preprocessor.set_log_output(&silent);
  preprocessor.set_cnf_output(&output);
  preprocessor.set_add_reduced_as_unit(true);
  preprocessor.set_preprocess_cnf_unit(true);
  if (quick)
    preprocessor.set_total_cost_limit(20000000);
  const bool competition = manager.UserFlags.satsuma_profile == "competition";
  const int componentLimit = manager.UserFlags.satsuma_component_limit >= 0
      ? manager.UserFlags.satsuma_component_limit : competition ? 5000000 : 500000;
  const int iterationLimit = manager.UserFlags.satsuma_iteration_limit >= 0
      ? manager.UserFlags.satsuma_iteration_limit : quick ? 0 : -1;
  preprocessor.set_proof_dense_crossover(competition ? 64 : 60);
  preprocessor.set_component_size_limit(componentLimit);
  preprocessor.set_order_model_budget(competition
      ? std::numeric_limits<uint64_t>::max() : 750000);
  preprocessor.set_dense_model_budget(competition
      ? std::numeric_limits<uint64_t>::max() : 20000000);
  if (competition)
    preprocessor.set_full_skip_limit(100000000);
  std::string ordering = manager.UserFlags.satsuma_ordering;
  if (ordering == "auto")
    ordering = competition && manager.UserFlags.satsuma_mode == "fix" ? "clique" : "off";
#if !CLIQUES
  if (ordering != "off")
    throw std::runtime_error("Satsuma column ordering requires USE_SATSUMA_CLIQUER=ON");
#endif
  if (manager.UserFlags.satsuma_mode == "fix")
  {
    preprocessor.set_orbitopal_fixing(true);
    preprocessor.set_orbitopal_fixing_only(true);
    preprocessor.set_schreier_fixing(true);
    preprocessor.set_negation_fixing(true);
    preprocessor.set_reorder(ordering != "off");
    preprocessor.set_reorder_cliquer(ordering == "clique");
    preprocessor.set_iterate(iterationLimit != 0);
    if (iterationLimit > 0)
      preprocessor.set_iteration_limit(iterationLimit);
    preprocessor.set_preprocess_cnf_pure(true);
  }
  poll.check();
  preprocessor.preprocess(formula);
  poll.check();
  if (manager.UserFlags.stats_flag)
  {
    const double seconds = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - start).count();
    std::cerr << "satsuma: mode=" << manager.UserFlags.satsuma_mode
              << " profile=" << manager.UserFlags.satsuma_profile
              << " ordering=" << ordering << " component_limit=" << componentLimit
              << " input_limit=" << inputLimit << " iteration_limit=" << iterationLimit
              << " seconds=" << seconds
              << " input_vars=" << cnf.varCount() - 1
              << " input_clauses=" << cnf.clauseCount() + extraClauses.size()
              << " input_literals=" << cnf.literalCount() + extraLiterals
              << " output_vars=" << output.variables
              << " output_clauses=" << output.clauses
              << " output_literals=" << output.literals << '\n';
  }
  return true;
}
}
