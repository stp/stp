/********************************************************************
 * AUTHORS: Unknown
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

#include "minisat/core/Solver.h"
#include "stp/Sat/MinisatCore.h"
//#include "utils/System.h"
//#include "simp/SimpSolver.h"

namespace stp
{

template <class T>
bool MinisatCore<T>::unitPropagate(const vec_literals& ps) {
  return s->unitPropagate(ps);
}

template <class T>
uint8_t MinisatCore<T>::value(uint32_t x) const {
  return Minisat::toInt(s->value(x));
}

template <class T> MinisatCore<T>::MinisatCore(volatile bool& interrupt)
{
  s = new T(interrupt);
}

template <class T> MinisatCore<T>::~MinisatCore()
{
  delete s;
}

template <class T>
bool MinisatCore<T>::addClause(
    const SATSolver::vec_literals& ps) // Add a clause to the solver.
{
  return s->addClause(ps);
}

template <class T>
bool
MinisatCore<T>::okay() const // FALSE means solver is in a conflicting state
{
  return s->okay();
}

template <class T> bool MinisatCore<T>::solve() // Search without assumptions.
{
  if (!s->simplify())
    return false;

  return s->solve();
}

template <class T> uint8_t MinisatCore<T>::modelValue(uint32_t x) const
{
  return Minisat::toInt(s->modelValue(x));
}

template <class T> uint32_t MinisatCore<T>::newVar()
{
  return s->newVar();
}

template <class T> void MinisatCore<T>::setVerbosity(int v)
{
  s->verbosity = v;
}

template <class T> void MinisatCore<T>::setSeed(int i)
{
  s->random_seed = i;
}

template <class T> unsigned long MinisatCore<T>::nVars()
{
  return s->nVars();
}

template <class T> void MinisatCore<T>::printStats()
{
  s->printStats();
}

template <class T> int MinisatCore<T>::nClauses()
{
  return s->nClauses();
}

template <class T> bool MinisatCore<T>::simplify()
{
  return s->simplify();
}

// I was going to make SimpSolver and Solver instances of this template.
// But I'm not so sure now because I don't understand what eliminate() does in
// the simp solver.
template class MinisatCore<Minisat::Solver>;
// template class MinisatCore<Minisat::SimpSolver>;
}
