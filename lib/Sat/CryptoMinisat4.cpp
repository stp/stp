// -*- c++ -*-
/********************************************************************
 * AUTHORS: Mate Soos
 *
 * BEGIN DATE: November, 2013
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "stp/Sat/CryptoMinisat4.h"

#undef var_Undef
#undef l_True
#undef l_False
#undef l_Undef

#include "cryptominisat4/cryptominisat.h"
#include <vector>
using std::vector;

namespace BEEV
{

  CryptoMinisat4::CryptoMinisat4()
  {
     CMSat::SolverConf conf;
     //conf.verbosity = 2;
     conf.doSQL = false;
     s = new CMSat::SATSolver(conf);
     //s->log_to_file("stp.cnf");
     //s->set_num_threads(3);
     temp_cl = (void*)new std::vector<CMSat::Lit>;
  }

  CryptoMinisat4::~CryptoMinisat4()
  {
    delete s;
    vector<CMSat::Lit>* real_temp_cl = (vector<CMSat::Lit>*)temp_cl;
    delete real_temp_cl;
  }

  bool
  CryptoMinisat4::addClause(const vec_literals& ps) // Add a clause to the solver.
  {
    // Cryptominisat uses a slightly different vec class.
    // Cryptominisat uses a slightly different Lit class too.

    vector<CMSat::Lit>& real_temp_cl = *(vector<CMSat::Lit>*)temp_cl;
    real_temp_cl.clear();
    for (int i = 0; i < ps.size(); i++) {
      real_temp_cl.push_back(CMSat::Lit(var(ps[i]), sign(ps[i])));
    }

    return s->add_clause(real_temp_cl);
  }

  bool
  CryptoMinisat4::okay() const // FALSE means solver is in a conflicting state
  {
    return s->okay();
  }

  bool
  CryptoMinisat4::solve() // Search without assumptions.
  {
    CMSat::lbool ret = s->solve();
    return (ret == CMSat::l_True);
  }

  uint8_t
  CryptoMinisat4::modelValue(uint32_t x) const
  {
    return (s->get_model().at(x) == CMSat::l_True);
  }

  uint32_t
  CryptoMinisat4::newVar()
  {
    s->new_var();
    return s->nVars()-1;
  }

  void CryptoMinisat4::setVerbosity(int v)
  {
    //s->conf.verbosity = v;
  }

  unsigned long CryptoMinisat4::nVars()
  {return s->nVars();}

  void CryptoMinisat4::printStats()
  {
        //s->printStats();
  }
};
