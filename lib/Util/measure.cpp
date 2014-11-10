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

// Measures how precise the AIG encodings are compared with the propagators.

#include "stp/cpp_interface.h"
#include "stp/Util/Relations.h"
#include "stp/Sat/MinisatCore.h"
#include "stp/Sat/core/Solver.h"
#include "stp/ToSat/AIG/ToSATAIG.h"
#include "stp/Util/Functions.h"
#include "stp/Printer/printers.h"
#include "stp/Util/StopWatch.h"
#include "stp/Util/BBAsProp.h"

using namespace BEEV;

int bits = 64;
int iterations = 100000;
ostream& out = cout;
STPMgr* mgr = new STPMgr;

void print(MinisatCore<Minisat::Solver>* ss, ASTNode i0,
           ToSAT::ASTNodeToSATVar& m)
{
  const int bits = std::max(1U, i0.GetValueWidth());
  out << "<";
  for (int i = bits - 1; i >= 0; i--)
  {
    if (ss->value(m.find(i0)->second[i]) == ss->true_literal())
    {
      out << "1";
    }
    else if (ss->value(m.find(i0)->second[i]) == ss->false_literal())
    {
      out << "0";
    }
    else
      out << "-";
  }
  out << ">";
}

void go(Kind k, Result (*t_fn)(vector<FixedBits*>&, FixedBits&), int prob)
{

  BBAsProp bbP(k, mgr, bits);
  bbP.numberClauses();

  Relations relations(iterations, bits, k, mgr, prob);

  int initial = 0;
  int transfer = 0;
  int clause = 0;

  Stopwatch2 bb;
  Stopwatch2 prop;

  list<Relations::Relation>::iterator it = relations.relations.begin();
  while (it != relations.relations.end())
  {
    FixedBits& a = it->a;
    FixedBits& b = it->b;
    FixedBits& output = it->output;

    bbP.toAssumptions(a, b, output);

    // Initial.
    // cerr << rel.a << _kind_names[k] << rel.b << rel.output << endl;

    const int initialCount =
        a.countFixed() + b.countFixed() + output.countFixed();
    initial += initialCount;

    // simplify does propagate.
    bb.start();
    bool ok = bbP.unitPropagate();
    bb.stop();
    assert(ok);

    // After unit propagation.
    int clauseCount = 0;
    clauseCount = bbP.fixedCount();

    clause += clauseCount;

    // After unit propagation.
    /*
     print(ss, i0, a.SATVar_to_SymbolIndexMap());
     cerr <<  _kind_names[k];
     print(ss, i1, a.SATVar_to_SymbolIndexMap());
     print(ss, r, a.SATVar_to_SymbolIndexMap());
     cerr << "\n";
     */

    // After transfer functions.
    vector<FixedBits*> ch;
    ch.push_back(&a);
    ch.push_back(&b);
    prop.start();
    Result rr = t_fn(ch, output);
    prop.stop();

    assert(rr != CONFLICT);
    // cerr << rel.a << _kind_names[k] << rel.b << rel.output << endl;
    int transferCount = a.countFixed() + b.countFixed() + output.countFixed();
    transfer += transferCount;

    // cerr << initialCount << endl;
    // cerr << clauseCount << endl;
    assert(initialCount <= clauseCount);
    assert(initialCount <= transferCount);

    // delete ss;
    it++;
  }

  int percent =
      100 * ((float)(clause - initial)) / ((float)(transfer - initial));
  if (transfer - initial == 0)
    percent = 100;

  cerr.setf(ios::fixed);
  cerr << "&" << setprecision(2) << (float(bb.elapsed) / CLOCKS_PER_SEC) << "s";

  cerr.setf(ios::fixed);
  cerr << "&" << setprecision(2) << (float(prop.elapsed) / CLOCKS_PER_SEC)
       << "s";

  cerr << "&" << (clause - initial) << "&" << (transfer - initial) << "&"
       << percent << "\\%\\\\%prob:" << prob << endl;
}

void work(int p)
{
  out << "\\begin{table}[t]" << endl;
  out << "\\begin{center}" << endl;
  out << "\\begin{tabular}{|l| r|r|r|r|r|r|r| }" << endl;
  out << "\\hline" << endl;
  out << "\\multicolumn{1}{|c|}{Operation} &" << endl;
  out << "\\multicolumn{5}{c|}{" << p << "\\%} \\\\" << endl;
  out << "& UP time & prop. time &  UP bits & prop. bits &  \\% \\\\" << endl;
  out << "\\hline" << endl;

  Functions f;
  std::list<Functions::Function>::iterator it = f.l.begin();
  while (it != f.l.end())
  {
    Functions::Function& f = *it;
    out << f.name << endl;
    go(f.k, f.fn, p);
    it++;
  }

  out << "\\hline" << endl;
  out << "\\end{tabular}" << endl;
  out << "\\caption{Comparison of unit propagation and bit-blasting at " << p
      << "\\%. ";
  out << iterations << " iterations at " << bits << " bits. \\label{tbl:p" << p
      << "}}}" << endl;
  out << "\\end{center}" << endl;
  out << "\\end{table}" << endl;
}

int main()
{
  mgr = new STPMgr;
  Cpp_interface interface(*mgr);
  mgr->UserFlags.division_by_zero_returns_one_flag = true;
  // mgr->UserFlags.set("simple-cnf","1");

  out << "\\begin{subtables}" << endl;
  // work(1);
  // work(5);
  work(50);
  // work(95);
  out << "\\end{subtables}" << endl;

  out << "% Iterations:" << iterations << " bit-width:" << bits << endl;
}
