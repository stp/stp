/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: 10/04/2012
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

#ifndef STOPWATCH_H_
#define STOPWATCH_H_

#include <ctime>

class Stopwatch
{
public:
  Stopwatch() : start(std::clock()) {}
  void stop()
  {
    clock_t total = clock() - start;
    cerr << "ticks: " << total << " " << (float(total) / CLOCKS_PER_SEC) << "s"
         << endl;
  }
  clock_t stop2()
  {
    clock_t total = clock() - start;
    return total;
  }

private:
  std::clock_t start;
};

struct Stopwatch2
{
  Stopwatch2() : elapsed(0), start_t(0) {}
  void stop()
  {
    elapsed += (clock() - start_t);
    start_t = 0;
  }

  void start()
  {
    assert(start_t == 0);
    start_t = clock();
  }

  std::clock_t elapsed;
  std::clock_t start_t;
};

#endif /* STOPWATCH_H_ */
