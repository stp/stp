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

#include <stack>
#include <map>
#include <string>
//#include "../sat/utils/System.h"
#include <iomanip>
#include <iostream>
#include <sstream>

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
    AlwaysTrue
  };

  static std::string CategoryNames[];

  typedef std::pair<Category, long> Element;

private:
  RunTimes& operator=(const RunTimes&);
  RunTimes(const RunTimes& other);

  std::map<Category, int> counts;
  std::map<Category, long> times;
  std::stack<Element> category_stack;

  // millisecond precision timer.
  long getCurrentTime();
  void addTime(Category c, long milliseconds);

  long lastTime;

public:
  void addCount(Category c);
  void start(Category c);
  void stop(Category c);
  void print();

  std::string getDifference();

  void resetDifference() { getDifference(); }

  void difference() { std::cout << getDifference() << std::endl << std::endl; }

  RunTimes() { lastTime = getCurrentTime(); }

  void clear()
  {
    counts.clear();
    times.clear();
    while (!category_stack.empty()) {
      category_stack.pop();
    }
  }
};

#endif
