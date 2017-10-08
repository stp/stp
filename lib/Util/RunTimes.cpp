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

// Hold the runtime statistics. E.g. how long was spent in simplification.
// The times don't add up to the runtime, because we allow multiple times to
// be counted simultaneously. For example, the current Transform()s call
// Simplify_TopLevel, so inside simplify time will be counted towards both
// Simplify_TopLevel & Transform.

// This is intended as a low overhead profiling class. So runtimes can
// always be tracked.

#include "stp/Util/RunTimes.h"
#include "minisat/utils/System.h"
#include "stp/Util/Attributes.h"
#include <cassert>
#include <iostream>
#include <sstream>
#include <sys/time.h>
#include <utility>

namespace stp
{
ATTR_NORETURN void FatalError(const char* str);
}

long RunTimes::getCurrentTime()
{
  timeval t;
  gettimeofday(&t, NULL);
  return (1000 * t.tv_sec) + (t.tv_usec / 1000);
}

void RunTimes::print()
{
  if (!category_stack.empty())
  {
    std::cerr << "size:" << category_stack.size() << std::endl;
    std::cerr << "top:" << CategoryNames[category_stack.top().first]
              << std::endl;
    stp::FatalError("category stack is not yet empty!!");
  }

  std::ostringstream result;
  result << "statistics\n";
  std::map<Category, int>::const_iterator it1 = counts.begin();
  std::map<Category, long>::const_iterator it2 = times.begin();

  int cummulative_ms = 0;

  while (it1 != counts.end())
  {
    int time_ms = 0;
    if ((it2 = times.find(it1->first)) != times.end())
      time_ms = it2->second;

    if (time_ms != 0)
    {
      result << " " << CategoryNames[it1->first] << ": " << it1->second;
      result << " [" << time_ms << "ms]";
      result << std::endl;
      cummulative_ms += time_ms;
    }
    it1++;
  }
  std::cerr << result.str();

  std::ios_base::fmtflags f(std::cerr.flags());

  std::cerr << std::fixed;
  std::cerr.precision(2);
  std::cerr << "Statistics Total: " << ((double)cummulative_ms) / 1000 << "s"
            << std::endl;
  std::cerr << "CPU Time Used   : " << Minisat::cpuTime() << "s" << std::endl;
  std::cerr << "Peak Memory Used: " << Minisat::memUsed() / (1024.0 * 1024.0)
            << "MB" << std::endl;

  std::cerr.flags(f);
  clear();
}

std::string RunTimes::getDifference()
{
  std::stringstream s;
  long val = getCurrentTime();
  s << (val - lastTime) << "ms";
  lastTime = val;
  s << ":" << std::fixed << std::setprecision(0)
    << Minisat::memUsed() / (1024.0 * 1024.0) << "MB";
  return s.str();
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
    stp::FatalError("Don't match");
  }
  addTime(c, getCurrentTime() - e.second);
  addCount(c);
}

void RunTimes::start(Category c)
{
  category_stack.push(std::make_pair(c, getCurrentTime()));
}
