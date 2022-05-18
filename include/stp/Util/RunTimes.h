/********************************************************************
 * AUTHORS: Trevor Hansen
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

#ifndef RUNTIMES_H
#define RUNTIMES_H

#include "stp/Util/Attributes.h"
#include <iomanip>
#include <iostream>
#include <map>
#include <sstream>
#include <stack>
#include <string>
#include <vector>

class RunTimes // not copyable
{
public:
  enum Category
  {
    Transforming = 0,
    SimplifyTopLevel,
    Parsing,
    CNFConversion,
    BitBlasting,
    Solving,
    BVSolver,
    PropagateEqualities,
    SendingToSAT,
    CounterExampleGeneration,
    SATSimplifying,
    ConstantBitPropagation,
    ArrayReadRefinement,
    ApplyingSubstitutions,
    RemoveUnconstrained,
    PureLiterals,
    UseITEContext,
    AIGSimplifyCore,
    IntervalPropagation,
    AlwaysTrue,
    Flatten,
    NodeDomainAnalysis,
    StrengthReduction
  };

  std::vector<std::string> CategoryNames = {"Transforming",
                                            "Simplifying",
                                            "Parsing",
                                            "CNF Conversion",
                                            "Bit Blasting",
                                            "SAT Solving",
                                            "Bitvector Solving",
                                            "Variable Elimination",
                                            "Sending to SAT Solver",
                                            "Counter Example Generation",
                                            "SAT Simplification",
                                            "Constant Bit Propagation",
                                            "Array Read Refinement",
                                            "Applying Substitutions",
                                            "Removing Unconstrained",
                                            "Pure Literals",
                                            "ITE Contexts",
                                            "AIG core simplification",
                                            "Interval Propagation",
                                            "Always True",
                                            "Sharing-aware Flattening",
                                            "Node Domain Analysis",
                                            "Strength Reduction"};

  typedef std::pair<Category, long> Element;

private:
  RunTimes& operator=(const RunTimes&);
  RunTimes(const RunTimes& other);

  std::map<Category, int> counts;
  std::map<Category, long> times;
  std::stack<Element> category_stack;

  // millisecond precision timer.
  DLL_PUBLIC long getCurrentTime();
  void addTime(Category c, long milliseconds);

  long lastTime;

public:
  DLL_PUBLIC void addCount(Category c);
  DLL_PUBLIC void start(Category c);
  DLL_PUBLIC void stop(Category c);
  DLL_PUBLIC void print();

  std::string getDifference();

  void resetDifference() { getDifference(); }

  void difference() { std::cout << getDifference() << std::endl << std::endl; }

  RunTimes() { lastTime = getCurrentTime(); }

  void clear()
  {
    counts.clear();
    times.clear();
    while (!category_stack.empty())
    {
      category_stack.pop();
    }
  }
};

#endif
