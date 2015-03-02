/**********
Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*************/

// Parses, runs constant bit propagation, then outputs the result.

#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/AST/AST.h"
#include "stp/Printer/printers.h"

#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/AIG/ToSATAIG.h"
#include "stp/Sat/MinisatCore.h"
#include "stp/STPManager/STP.h"
#include "stp/cpp_interface.h"

using namespace simplifier::constantBitP;
using namespace stp;

int main(int argc, char** argv)
{
  extern int smt2parse();
  extern int smt2lex_destroy(void);
  extern FILE* smt2in;

  STPMgr stp;
  STPMgr* mgr = &stp;

  Cpp_interface interface(*mgr, mgr->defaultNodeFactory);
  interface.startup();
  interface.ignoreCheckSat();
  stp::GlobalParserInterface = &interface;

  Simplifier* simp = new Simplifier(mgr);
  ArrayTransformer* at = new ArrayTransformer(mgr, simp);
  AbsRefine_CounterExample* abs = new AbsRefine_CounterExample(mgr, simp, at);
  ToSATAIG* tosat = new ToSATAIG(mgr, at);

  GlobalSTP = new STP(mgr, simp, at, tosat, abs);

  srand(time(NULL));
  stp::GlobalParserBM = &stp;

  stp.UserFlags.disableSimplifications();
  stp.UserFlags.bitConstantProp_flag = true;

  // Parse SMTLIB2-----------------------------------------
  mgr->GetRunTimes()->start(RunTimes::Parsing);
  if (argc > 1)
  {
    smt2in = fopen(argv[1], "r");
    smt2parse();
  }
  else
  {
    smt2in = NULL; // from stdin.
    smt2parse();
  }
  smt2lex_destroy();
  //-----------------------------------------------------

  ASTNode n;

  ASTVec v = interface.GetAsserts();
  if (v.size() > 1)
    n = interface.CreateNode(AND, v);
  else
    n = v[0];

  // Apply cbitp ----------------------------------------
  simplifier::constantBitP::ConstantBitPropagation cb(
      simp, mgr->defaultNodeFactory, n);
  if (cb.isUnsatisfiable())
    n = mgr->ASTFalse;
  else
    n = cb.topLevelBothWays(n, true, true);

  if (simp->hasUnappliedSubstitutions())
  {
    n = simp->applySubstitutionMap(n);
    simp->haveAppliedSubstitutionMap();
  }

  // Print back out.
  printer::SMTLIB2_PrintBack(cout, n);
  cout << "(check-sat)\n";
  cout << "(exit)\n";
  return 0;
}
