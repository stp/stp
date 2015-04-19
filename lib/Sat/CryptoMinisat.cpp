/********************************************************************
 * AUTHORS: Vijay Ganesh, Mate Soos
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

#include "stp/Sat/CryptoMinisat.h"
//#include "utils/System.h"

#undef var_Undef
#undef l_True
#undef l_False
#undef l_Undef

#include "cryptominisat2/Solver.h"
#include "cryptominisat2/SolverTypes.h"

namespace stp
{

CryptoMinisat::CryptoMinisat()
{
  s = new CMSat2::Solver();
}

CryptoMinisat::~CryptoMinisat()
{
  delete s;
}

bool
CryptoMinisat::addClause(const vec_literals& ps) // Add a clause to the solver.
{
  // Cryptominisat uses a slightly different vec class.
  // Cryptominisat uses a slightly different Lit class too.

  // VERY SLOW>
  CMSat2::vec<CMSat2::Lit> v;
  for (int i = 0; i < ps.size(); i++)
    v.push(CMSat2::Lit(var(ps[i]), sign(ps[i])));

  return s->addClause(v);
}

bool CryptoMinisat::okay() const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

bool CryptoMinisat::solve(bool& timeout_expired) // Search without assumptions.
{
  CMSat2::lbool ret = s->solve();
  if (ret == CMSat2::l_Undef) {
    timeout_expired = true;
  }
  return ret == CMSat2::l_True;
}

uint8_t CryptoMinisat::modelValue(uint32_t x) const
{
  return s->model[x].getchar();
}

uint32_t CryptoMinisat::newVar()
{
  return s->newVar();
}

void CryptoMinisat::setVerbosity(int v)
{
  s->verbosity = v;
}

unsigned long CryptoMinisat::nVars() const
{
  return s->nVars();
}

void CryptoMinisat::printStats()
{
  s->printStats();
}
}
