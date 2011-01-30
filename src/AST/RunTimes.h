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
      ArrayReadRefinement
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
  
  void difference()
  {
	  long val = getCurrentTime();
	  std::cout << (val -  lastTime) << "ms" << std::endl;
	  lastTime = val;
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
