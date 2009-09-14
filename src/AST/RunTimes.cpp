//Hold the runtime statistics. E.g. how long was spent in simplification.
//The times don't add up to the runtime, because we allow multiple times to
//be counted simultaneously. For example, the current Transform()s call
//Simplify_TopLevel, so inside simplify time will be counted towards both
//Simplify_TopLevel & Transform.

// This is intended as a low overhead profiling class. So runtimes can
// always be tracked.

#include "RunTimes.h"
#include <cassert>
#include <sys/time.h>
#include <sstream>
#include <iostream>
#include <utility>

// BE VERY CAREFUL> Update the Category Names to match.
std::string RunTimes::CategoryNames[] = { "Transforming", "Simplifying", "Parsing", "CNF Conversion", "Bit Blasting", "Solving"};

namespace BEEV
{
	void FatalError(const char * str);
}


long RunTimes::getCurrentTime()
{
	timeval t;
	gettimeofday(&t, NULL);
	return (1000 * t.tv_sec) + (t.tv_usec / 1000);
}

void RunTimes::print()
{
	if (0 !=  category_stack.size())
		BEEV::FatalError("category stack is not yet emptuy");

	std::ostringstream result;
	result << "statistics\n";
	std::map<Category, int>::const_iterator it1 = counts.begin();
	std::map<Category, long>::const_iterator it2 = times.begin();

	while (it1 != counts.end())
	{
		result << " " << CategoryNames[it1->first] << ": " << it1->second;
		if ((it2 = times.find(it1->first)) != times.end())
			result << " [" << it2->second << "ms]";
		result << std::endl;
		it1++;
	}

	std::cerr << result.str();
	// iterator
}

void RunTimes::addTime(Category c, long milliseconds)
{
	std::map<Category, long>::iterator it;
	if ((it = times.find(c)) == times.end())
	{
		times[c] = milliseconds;
	}
	else
	{
		it->second += milliseconds;
	}

}

void RunTimes::addCount(Category c)
{
	std::map<Category, int>::iterator it;
	if ((it = counts.find(c)) == counts.end())
	{
		counts[c] = 1;
	}
	else
	{
		it->second++;
	}
}

void RunTimes::stop(Category c)
{
	Element e = category_stack.top();
	category_stack.pop();
	if (e.first != c)
	{
		std::cerr << e.first;
		std::cerr << c;
		BEEV::FatalError("Don't match");
	}
	addTime(c, getCurrentTime() - e.second);
	addCount(c);
}

void RunTimes::start(Category c)
{
	category_stack.push(std::make_pair(c, getCurrentTime()));
}
