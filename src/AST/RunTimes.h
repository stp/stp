// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef RUNTIMES_H
#define RUNTIMES_H

#include <stack>
#include <map>
#include <string>

class RunTimes
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
      CreateSubstitutionMap, 
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
      IntervalPropagation
    };

  static std::string CategoryNames[];
  
  typedef std::pair<Category, long> Element;
  
private:
  RunTimes& operator =(const RunTimes&);
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
  
  std::string getDifference()
  {
    std::stringstream s;
    long val = getCurrentTime();
    s << (val -  lastTime) << "ms" ;
    lastTime = val;
    return s.str();
  }

  void difference()
  {
	  std::cout << getDifference()<< std::endl << std::endl;

  }

  RunTimes()
  {
	  lastTime = getCurrentTime();
  }
  
  void clear()
  {
    counts.clear();
    times.clear();
    category_stack.empty();
  }
};

#endif
