/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Dan Liew, Mate Soos
 *
 * BEGIN DATE: November, 2005
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "stp/ToSat/ToSATBase.h"

namespace stp
{
using std::cerr;
using std::cout;
using std::endl;

// This function prints the output of the STP solver
void ToSATBase::PrintOutput(SOLVER_RETURN_TYPE ret)
{
  if (ret == SOLVER_TIMEOUT || ret == SOLVER_UNDECIDED)
  {
    cout << "Timed Out." << endl;
    return;
  }

  bool true_iff_valid = (SOLVER_VALID == ret);

  if (bm->UserFlags.print_output_flag)
  {
    if (bm->UserFlags.smtlib1_parser_flag || bm->UserFlags.smtlib2_parser_flag)
    {
      if (true_iff_valid && (input_status == TO_BE_SATISFIABLE))
      {
        cerr << "Warning. Expected satisfiable,"
                " FOUND unsatisfiable"
             << endl;
      }
      else if (!true_iff_valid && (input_status == TO_BE_UNSATISFIABLE))
      {
        cerr << "Warning. Expected unsatisfiable,"
                " FOUND satisfiable"
             << endl;
      }
    }
  }

  if (true_iff_valid)
  {
    bm->ValidFlag = true;
    if (bm->UserFlags.print_output_flag)
    {
      if (bm->UserFlags.smtlib1_parser_flag ||
          bm->UserFlags.smtlib2_parser_flag)
        cout << "unsat\n";
      else
        cout << "Valid.\n";
    }
  }
  else
  {
    bm->ValidFlag = false;
    if (bm->UserFlags.print_output_flag)
    {
      if (bm->UserFlags.smtlib1_parser_flag ||
          bm->UserFlags.smtlib2_parser_flag)
        cout << "sat\n";
      else
        cout << "Invalid.\n";
    }
  }

  flush(cout);
}
}
