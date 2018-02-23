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
// Runs unit propagation on the AIG encoding and measures how many bits
// unit propagation deduces.

#define __STDC_FORMAT_MACROS
#include "minisat/core/Solver.h"
#include "stp/Printer/printers.h"
#include "stp/Sat/MinisatCore.h"
#include "stp/ToSat/AIG/ToSATAIG.h"
#include "stp/Util/BBAsProp.h"
#include "stp/Util/Functions.h"
#include "stp/Util/Relations.h"
#include "stp/Util/StopWatch.h"
#include "stp/cpp_interface.h"
#include <cstdint>

#include <iostream>

using namespace stp;

int bits = 65;
int iterations = 100000;
ostream& out = cout;
STPMgr* mgr = new STPMgr;


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

    bbP.fill_assumps_with(a, b, output);

    const int initialCount =
        a.countFixed() + b.countFixed() + output.countFixed();
    initial += initialCount;

    // Initial.
    cerr << a << _kind_names[k] << b << output << endl;
    cerr << "Initial Fixed:" << initialCount << endl;

    bb.start();
    bool ok = bbP.unit_prop_with_assumps();
    assert(ok); // should never conflict.
    bb.stop();

    // After unit propagation.
    int unitPCount = bbP.fixedCount();
    cerr << "Unit Propagation Fixed:" << unitPCount - initialCount << endl;
    clause += unitPCount;

    // After transfer functions.
    vector<FixedBits*> ch;
    ch.push_back(&a);
    ch.push_back(&b);
    prop.start();
    Result rr = t_fn(ch, output);
    assert(rr != CONFLICT);
    prop.stop();

    int transferCount = a.countFixed() + b.countFixed() + output.countFixed();
    transfer += transferCount;

    // Result from cbitp.
    cerr << a << _kind_names[k] << b << output << endl;
    cerr << "CBitP Fixed:" << transferCount - initialCount << endl;

    assert(initialCount <= unitPCount);
    assert(initialCount <= transferCount);

    // delete ss;
    it++;
  }

  int percent =
      100 * ((float)(clause - initial)) / ((float)(transfer - initial));
  if (transfer - initial == 0)
    percent = 100;

  cerr.setf(std::ios::fixed);
  cerr << "&" << std::setprecision(2) << (float(bb.elapsed) / CLOCKS_PER_SEC)
       << "s";

  cerr.setf(std::ios::fixed);
  cerr << "&" << std::setprecision(2) << (float(prop.elapsed) / CLOCKS_PER_SEC)
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
  // mgr->UserFlags.set("simple-cnf","1");

  out << "\\begin{subtables}" << endl;
  //work(1);
  //work(5);
  work(50);
  //work(95);
  out << "\\end{subtables}" << endl;

  out << "% Iterations:" << iterations << " bit-width:" << bits << endl;
}
