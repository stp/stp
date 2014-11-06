/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
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
// -*- c++ -*-

#include "stp/AST/UsefulDefs.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Globals/Globals.h"
namespace BEEV
{
  using std::cout;
  using std::endl;

  ostream &operator<<(ostream &os, const Spacer &sp)
  {
    // Instead of wrapping lines with hundreds of spaces, prints
    // a "+" at the beginning of the line for each wrap-around.
    // so lines print like: +14+                (XOR ...
    int blanks = sp._spaces % 60;
    int wraps = sp._spaces / 60;
    if (wraps > 0)
      {
        os << "+" << wraps;
      }
    for (int i = 0; i < blanks; i++)
      os << " ";
    return os;
  }

  //this function accepts the name of a function (as a char *), and
  //records some stats about it. if the input is "print_func_stats",
  //the function will then print the stats that it has collected.
  void CountersAndStats(const char * functionname, STPMgr * bm)
  {
    static function_counters s;
    if (bm->UserFlags.stats_flag)
      {

        if (!strcmp(functionname, "print_func_stats"))
          {
            cout << endl;
            for (function_counters::iterator 
                   it = s.begin(), itend = s.end(); 
                 it != itend; it++)
              cout << "Number of times the function: " 
                   << it->first 
                   << ": is called: " 
                   << it->second << endl;
            return;
          }
        s[functionname] += 1;

      }
  }
} // end of namespace
