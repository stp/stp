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

#include "stp/Sat/CryptoMinisat5.h"
#include "cryptominisat5/cryptominisat.h"
#include <vector>
using std::vector;

namespace stp
{

void CryptoMiniSat5::enableRefinement(const bool enable)
{
  // might break if we simplify with refinement enabled..
  if (enable)
  {
    s->set_no_simplify_at_startup();
  }
}

CryptoMiniSat5::CryptoMiniSat5(int num_threads)
{
  s = new CMSat::SATSolver;
  // s->log_to_file("stp.cnf");
  s->set_num_threads(num_threads);
  s->set_default_polarity(false);
  //s->set_allow_otf_gauss();
  temp_cl = (void*)new vector<CMSat::Lit>;
}

CryptoMiniSat5::~CryptoMiniSat5()
{
  delete s;
  vector<CMSat::Lit>* real_temp_cl = (vector<CMSat::Lit>*)temp_cl;
  delete real_temp_cl;
}

void CryptoMiniSat5::setMaxConflicts(int64_t max_confl)
{
  if (max_confl > 0)
    s->set_max_confl(max_confl);
}

bool CryptoMiniSat5::addClause(
    const vec_literals& ps) // Add a clause to the solver.
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

bool CryptoMiniSat5::okay()
    const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

bool CryptoMiniSat5::solve(bool& timeout_expired) // Search without assumptions.
{
  CMSat::lbool ret = s->solve();
  if (ret == CMSat::l_Undef)
  {
    timeout_expired = true;
  }
  return ret == CMSat::l_True;
}

uint8_t CryptoMiniSat5::modelValue(uint32_t x) const
{
  return (s->get_model().at(x) == CMSat::l_True);
}

uint32_t CryptoMiniSat5::newVar()
{
  s->new_var();
  return s->nVars() - 1;
}

void CryptoMiniSat5::setVerbosity(int v)
{
  s->set_verbosity(v);
}

unsigned long CryptoMiniSat5::nVars() const
{
  return s->nVars();
}

void CryptoMiniSat5::printStats() const
{
  // s->printStats();
}

} //end namespace stp
