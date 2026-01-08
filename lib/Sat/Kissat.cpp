/********************************************************************
 * AUTHORS: Kotaro Matsuoka
 *
 * BEGIN DATE: Oct, 2024
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

#include "stp/Sat/Kissat.h"
#include <unordered_set>
#include <algorithm>

namespace stp
{

Kissat::Kissat()
{
  s = kissat_init();
  kissat_set_option(s, "quiet", 1);
}

Kissat::~Kissat()
{
  kissat_release(s);
}

void Kissat::setMaxConflicts(int64_t _max_confl)
{
  if(_max_confl > 0)
    kissat_set_conflict_limit(s,_max_confl);
}

// void Kissat::setMaxTime(int64_t _max_time)
// {
//   max_time = _max_time;
// }

bool Kissat::addClause(
    const vec_literals& ps) // Add a clause to the solver.
{

  for (int i = 0; i < ps.size(); i++)
    // kissat_add(s,ps[i].x);
    kissat_add(s,ps[i].x&1?-(ps[i].x>>1):(ps[i].x>>1));
  kissat_add(s,0);
  return true;
}

bool Kissat::okay()
    const // FALSE means solver is in a conflicting state
{
  return kissat_okay(s);
}

bool Kissat::solve(bool& timeout_expired) // Search without assumptions.
{

  int32_t res = kissat_solve(s);
  if (res == 10)
  {
    return true;
  }
  else if (res == 20)
  {
    return false;
  }
  else
  {
    timeout_expired = true;
    return false;
  }
}

uint8_t Kissat::modelValue(uint32_t x) const
{
  int32_t val = kissat_value(s,x);
  if (val > 0) return 1;
  else if (val < 0) return -1;
  else return 0;
}

uint32_t Kissat::newVar()
{
  return kissat_new_var(s);
}

void Kissat::setVerbosity(int v)
{
  kissat_set_option(s, "verbose", v);
}

unsigned long Kissat::nVars() const
{
  return kissat_nvars(s);
}

void Kissat::printStats() const
{
  kissat_print_statistics(s);
}

} //end namespace stp
