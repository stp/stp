#include "stp/cpp_interface.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Util/RunTimes.h"

#include <iostream>
#include <sstream>
#include <stdexcept>

int main()
{
  try
  {
    stp::STPMgr manager;
    stp::STP engine(&manager);
    stp::GlobalSTP = &engine;
    stp::Cpp_interface api(manager);
    const stp::ASTNode x =
        api.CreateSourceSymbol("x", stp::SourceSort::real());
    const stp::ASTNode coefficient = api.CreateRealConst("-1.2500");
    const stp::ASTNode product = api.CreateRealTerm(
        stp::REAL_MUL, stp::ASTVec{coefficient, x});
    const stp::ASTNode bound = api.CreateRealConst("-5/4");
    const stp::ASTNode predicate =
        api.CreateRealPredicate(stp::REAL_GE, product, bound);
    // Successful checked construction of product/predicate proves that x's
    // C++ source-sort conversion is Real.  Restrict the shared-library smoke
    // to deliberately exported LRA methods; baseline AST debug/carrier helpers
    // are not part of hidden-symbol libstp's installed ABI.
    if (coefficient.GetRealCanonical() != "-5/4" ||
        coefficient.GetRealNumerator() != "-5" ||
        coefficient.GetRealDenominator() != "4" || coefficient != bound ||
        product.GetKind() != stp::REAL_MUL ||
        predicate.GetKind() != stp::REAL_GE)
      throw std::runtime_error("C++ exact Real construction mismatch");

    const stp::ASTNode one = api.CreateRealConst("1");
    api.AddAssert(api.CreateRealPredicate(stp::REAL_GE, x, one));
    api.AddAssert(api.CreateRealPredicate(stp::REAL_LE, x, one));
    manager.GetRunTimes()->start(RunTimes::Parsing);
    api.checkSat(api.getAssertVector());
    if (!manager.HasRealModel() || !manager.HasRealModelValue(x) ||
        manager.GetRealModelValue(x) != "1" ||
        manager.GetRealModelNumerator(x) != "1" ||
        manager.GetRealModelDenominator(x) != "1" ||
        manager.GetRealModelSMTLIB(x) != "1")
      throw std::runtime_error("C++ exact Real model mismatch");

    std::ostringstream model;
    manager.PrintRealModelSMTLIB2(model, stp::ASTVec{x});
    if (model.str().find("(define-fun |x| () Real 1)") ==
        std::string::npos)
      throw std::runtime_error("C++ legal SMT-LIB model mismatch");

    api.push();
    if (manager.HasRealModel())
      throw std::runtime_error("C++ push retained a stale Real model");
    api.AddAssert(api.CreateRealPredicate(
        stp::REAL_GT, x, api.CreateRealConst("2")));
    api.checkSat(api.getAssertVector());
    if (manager.HasRealModel())
      throw std::runtime_error("UNSAT published a Real model");
    api.pop();
    api.checkSat(api.getAssertVector());
    if (!manager.HasRealModel() || manager.GetRealModelValue(x) != "1")
      throw std::runtime_error("repeated post-pop Real check mismatch");

    api.checkSatAssuming(stp::ASTVec{api.CreateRealPredicate(
        stp::REAL_GT, x, api.CreateRealConst("3"))});
    if (manager.HasRealModel())
      throw std::runtime_error("UNSAT assumption published a Real model");
    api.checkSat(api.getAssertVector());
    if (!manager.HasRealModel() || manager.GetRealModelValue(x) != "1")
      throw std::runtime_error("assumption did not expire after one call");

    api.resetAssertions();
    if (manager.HasRealModel())
      throw std::runtime_error("resetAssertions retained an exact Real model");
    api.reset();
    if (manager.HasRealModel())
      throw std::runtime_error("full reset retained an exact Real model");
    const stp::ASTNode unconstrained =
        api.CreateSourceSymbol("unconstrained", stp::SourceSort::real());
    manager.GetRunTimes()->start(RunTimes::Parsing);
    api.checkSat(api.getAssertVector());
    if (!manager.HasRealModel() ||
        manager.GetRealModelValue(unconstrained) != "0")
      throw std::runtime_error(
          "unconstrained C++ Real check bypassed exact certification");
    stp::GlobalSTP = nullptr;
    std::cout << "PASS real-cpp-api-smoke\n";
    return 0;
  }
  catch (const std::exception& failure)
  {
    std::cerr << "FAIL " << failure.what() << '\n';
    return 1;
  }
}
