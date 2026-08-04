/********************************************************************
 * AUTHORS: Michael Katelman , Vijay Ganesh, Dan Liew
 *
 * BEGIN DATE: Oct, 2008
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

/*! @brief The following code declares a class to write to a file
 * descriptor or file handle.
 *
 * See
 *      http://www.josuttis.com/cppcode
 * for details and the latest version.
 *
 * - open:
 *      - integrating BUFSIZ on some systems?
 *      - i18n
 *
 * (C) Copyright Nicolai M. Josuttis 2001.
 * Permission to copy, use, modify, sell and distribute this software
 * is granted provided this copyright notice appears in all copies.
 * This software is provided "as is" without express or implied
 * warranty, and with no claim as to its suitability for any purpose.
 *
 * Version: Jul 28, 2002
 * History:
 *  Jul 28, 2002: bugfix memcpy() => memmove()
 *  Aug 05, 2001: first public version
 */
#ifndef __FDSTREAM_HPP__
#define __FDSTREAM_HPP__

#include <ostream>
#include <streambuf>

// for EOF:
#include <cstdio>

// low-level write function
#ifdef _MSC_VER
#include <io.h>
#else
#include <unistd.h>
// extern "C" {
//    int write (int fd, const char* buf, int num);
//}
#endif

namespace std
{

/************************************************************
 * fdostream
 * - a stream that writes on a file descriptor
 ************************************************************/

class fdoutbuf : public std::streambuf
{
protected:
  int fd; // file descriptor
public:
  // constructor
  fdoutbuf(int _fd) : fd(_fd) {}

protected:
  // write one character
  virtual int_type overflow(int_type c)
  {
    if (c != EOF)
    {
      char z = c;
      if (write(fd, &z, 1) != 1)
      {
        return EOF;
      }
    }
    return c;
  }
  // write multiple characters
  virtual std::streamsize xsputn(const char* s, std::streamsize num)
  {
    return write(fd, s, num);
  }
};

class fdostream : public std::ostream
{
protected:
  fdoutbuf buf;

public:
  fdostream(int fd) : std::ostream(0), buf(fd) { rdbuf(&buf); }
};
}

#endif /*__FDSTREAM_HPP__*/
