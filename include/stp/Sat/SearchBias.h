/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2026
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

#ifndef SEARCHBIAS_H_
#define SEARCHBIAS_H_

namespace stp
{

// Which answer to tune the SAT search towards.
//
// Modern CDCL solvers alternate between a mode that is good at finding models
// and one that is good at closing off the search space, and several of them
// let a caller pin one of the two. On a workload that is known to lean one way
// -- verification conditions are usually unsatisfiable -- the time spent in the
// other mode is wasted.
//
// This selects heuristics only. A correct SAT solver returns the same verdict
// whatever bias it is given, so getting the bias wrong costs time, not
// soundness. Each backend maps this onto whatever it happens to offer, and
// backends with nothing to offer ignore it.
enum class SearchBias
{
  NONE = 0, // leave the solver at its own defaults
  SAT,      // tune for finding a model
  UNSAT     // tune for proving that there isn't one
};

inline const char* searchBiasName(SearchBias bias)
{
  switch (bias)
  {
    case SearchBias::SAT:
      return "sat";
    case SearchBias::UNSAT:
      return "unsat";
    default:
      return "none";
  }
}
}

#endif
