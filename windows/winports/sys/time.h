/**************
 *
 * Author: Trevor Hansen
 *
 * Date: Jun, 2011
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

// C++ windows related time implementation

#ifndef __TIME_H__
#define __TIME_H__ 1

#if defined(_MSC_VER)
// windows missed gettimeofday function
struct timezone
{
  int tz_minuteswest; /* minutes W of Greenwich */
  int tz_dsttime;     /* type of dst correction */
};

#if !defined(WINDOWS_H_INCLUDED)
struct timeval
{
  long tv_sec;
  long tv_usec;
};
#endif

namespace stp
{
int gettimeofdayWin32(struct timeval* tv, struct timezone* tz);
}

#if !defined(gettimeofday)
// #define'ing gettimeofday to avoid generating the symbol gettimeofday
#define gettimeofday(tv, tz) stp::gettimeofdayWin32(tv, tz);
#endif

#endif // defined(_MSC_VER)

/************************************************************************/
#endif
