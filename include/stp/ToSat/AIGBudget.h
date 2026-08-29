/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: August, 2026
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

#ifndef AIGBUDGET_H
#define AIGBUDGET_H

#include <stdexcept>

namespace stp
{

// Thrown by a node manager's checkBudget() when the AND-gate count passes its
// nodeBudget. Whoever set the budget owns the abandonment policy, so this
// escapes CreateNode() and every BitBlaster frame above it; only a caller
// that set a budget can see it.
//
// In its own header because both node managers throw it and the callers catch
// one type, while only one of the two managers knows what ABC is.
struct AIGBudgetExhausted : public std::runtime_error
{
  // The AND-gate count reached, always strictly greater than the budget.
  int nodeCount;

  explicit AIGBudgetExhausted(int n)
      : std::runtime_error("AIG node budget exhausted"), nodeCount(n) {}
};

} // namespace stp

#endif
