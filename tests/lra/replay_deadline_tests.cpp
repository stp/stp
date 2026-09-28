#include "LraReconstruction.h"
#include "LraRelu.h"
#include "stp/STPManager/STPManager.h"
#include <iostream>
#include <stdexcept>

namespace
{
using namespace stp;
using namespace stp::lra;

void require(bool condition, const char* detail)
{
  if (!condition)
    throw std::runtime_error(detail);
}

void reconstructionDeadline()
{
  STPMgr manager;
  const auto x = manager.CreateSourceSymbol("deadline_x", SourceSort::real());
  const auto atom = manager.CreateRealPredicate(EQ, x, manager.CreateRealConst("0"));
  unsigned evaluations = 0;
  const auto predicate = [&](const ASTNode&) { ++evaluations; return true; };
  const auto expired = std::chrono::steady_clock::time_point::min();
  require(!acceptsRealFormula(atom, predicate, expired) && evaluations == 0,
          "expired checking must decline before evaluating predicates");
  require(acceptsRealFormula(atom, predicate) && evaluations == 1,
          "unlimited exact checking must still evaluate predicates");

  ReluProblem problem(manager, manager.ASTTrue);
  LraReconstruction reconstruction;
  reconstruction.original = manager.ASTTrue;
  problem.reconstruction = &reconstruction;
  require(!tryReluWitness(problem, {}, expired) && !problem.satisfied &&
              !reconstruction.witness && reconstruction.definitions.empty() &&
              reconstruction.replay_attempts == 0,
          "expired replay must not publish or consume an attempt");
  require(tryReluWitness(problem, {}) && problem.satisfied &&
              reconstruction.witness,
          "a declined deadline must leave a later replay usable");
}

} // namespace

int main()
{
  try
  {
    reconstructionDeadline();
    std::cout << "PASS exact replay deadline and recovery\n";
    return 0;
  }
  catch (const std::exception& error)
  {
    std::cerr << error.what() << '\n';
    return 1;
  }
}
