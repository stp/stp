// Standalone public-API smoke test. Uses the same in-process adapter as the CLI.
#include <stp/stp.hpp>
#include <iostream>
#include <stdexcept>

int main(int argc, char** argv)
{
  for (const char* mode : {"off", "lex", "fix"})
  {
    stp::Options options;
    options.set("sat-backend", argc > 1 ? argv[1] : "cadical");
    options.set("satsuma", mode);
    options.set("incremental", "off");
    options.set_bool("check-sanity", true);
    stp::TermManager manager;
    stp::Solver solver(manager, options);
    solver.parse(R"((set-logic QF_BV)
      (declare-fun x () (_ BitVec 8))
      (declare-fun y () (_ BitVec 8))
      (assert (and (= (bvmul x y) #x06)
                   (bvult x #x10) (bvult y #x10))))", stp::Format::SMTLIB2);
    if (!solver.check_sat().is_sat())
      throw std::runtime_error("expected SAT in public API");
    solver.parse("(assert (bvugt x #x80))", stp::Format::SMTLIB2);
    if (!solver.check_sat().is_unsat())
      throw std::runtime_error("expected UNSAT after adding a batch constraint");
  }
  std::cout << "Public C++ API passed in off, lex and fix modes\n";
}
