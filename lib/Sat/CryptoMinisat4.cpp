/********************************************************************
 * AUTHORS: Mate Soos
 *
 * BEGIN DATE: November, 2013
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

#include "stp/Sat/CryptoMinisat4.h"

#undef var_Undef
#undef l_True
#undef l_False
#undef l_Undef

#include "cryptominisat4/cryptominisat.h"
#include <vector>
using std::vector;

namespace stp
{

CryptoMinisat4::CryptoMinisat4()
{
  s = new CMSat::SATSolver;
  // s->log_to_file("stp.cnf");
  // s->set_num_threads(3);
  temp_cl = (void*)new std::vector<CMSat::Lit>;
}

CryptoMinisat4::~CryptoMinisat4()
{
  delete s;
  vector<CMSat::Lit>* real_temp_cl = (vector<CMSat::Lit>*)temp_cl;
  delete real_temp_cl;
}

void CryptoMinisat4::setMaxConflicts(int64_t max_confl)
{
  if (max_confl> 0)
    s->set_max_confl(max_confl);
}

bool
CryptoMinisat4::addClause(const vec_literals& ps) // Add a clause to the solver.
{
  // Cryptominisat uses a slightly different vec class.
  // Cryptominisat uses a slightly different Lit class too.

  vector<CMSat::Lit>& real_temp_cl = *(vector<CMSat::Lit>*)temp_cl;
  real_temp_cl.clear();
  for (int i = 0; i < ps.size(); i++)
  {
    real_temp_cl.push_back(CMSat::Lit(var(ps[i]), sign(ps[i])));
  }

  return s->add_clause(real_temp_cl);
}

bool
CryptoMinisat4::okay() const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

bool CryptoMinisat4::solve(bool& timeout_expired) // Search without assumptions.
{
  CMSat::lbool ret = s->solve();
  if (ret == CMSat::l_Undef) {
    timeout_expired = true;
  }
  return ret == CMSat::l_True;
}

uint8_t CryptoMinisat4::modelValue(uint32_t x) const
{
  return (s->get_model().at(x) == CMSat::l_True);
}

uint32_t CryptoMinisat4::newVar()
{
  s->new_var();
  return s->nVars() - 1;
}

void CryptoMinisat4::setVerbosity(int v)
{
  // s->conf.verbosity = v;
}

unsigned long CryptoMinisat4::nVars() const
{
  return s->nVars();
}

void CryptoMinisat4::printStats() const
{
  // s->printStats();
}

} //end namespace stp
