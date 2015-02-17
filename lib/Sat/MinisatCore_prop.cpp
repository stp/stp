/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Aug, 2010
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

#include "minisat/core_prop/Solver_prop.h"
#include "stp/Sat/MinisatCore_prop.h"
//#include "utils/System.h"

namespace stp
{

template <class T> MinisatCore_prop<T>::MinisatCore_prop(volatile bool& timeout)
{
  s = new T(timeout);
}

template <class T> MinisatCore_prop<T>::~MinisatCore_prop()
{
  delete s;
}

template <class T>
bool MinisatCore_prop<T>::addArray(int array_id,
                                   const SATSolver::vec_literals& i,
                                   const SATSolver::vec_literals& v,
                                   const Minisat::vec<Minisat::lbool>& ki,
                                   const Minisat::vec<Minisat::lbool>& kv)
{
  s->addArray(array_id, i, v, ki, kv);
  return true;
}

template <class T>
bool MinisatCore_prop<T>::addClause(
    const SATSolver::vec_literals& ps) // Add a clause to the solver.
{
  return s->addClause(ps);
}

template <class T>
bool MinisatCore_prop<T>::okay()
    const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

template <class T>
bool MinisatCore_prop<T>::solve() // Search without assumptions.
{
  if (!s->simplify())
    return false;

  return s->solve();
}

template <class T> uint8_t MinisatCore_prop<T>::modelValue(uint32_t x) const
{
  return Minisat::toInt(s->modelValue(x));
}

template <class T> uint32_t MinisatCore_prop<T>::newVar()
{
  return s->newVar();
}

template <class T> void MinisatCore_prop<T>::setVerbosity(int v)
{
  s->verbosity = v;
}

template <class T> unsigned long MinisatCore_prop<T>::nVars()
{
  return s->nVars();
}

template <class T> void MinisatCore_prop<T>::printStats()
{
  s->printStats();
}

template <class T> void MinisatCore_prop<T>::setSeed(int i)
{
  s->random_seed = i;
}

template class MinisatCore_prop<Minisat::Solver_prop>;
}
