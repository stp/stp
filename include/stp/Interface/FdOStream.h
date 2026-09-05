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

// A write-only std::ostream over a file descriptor the caller owns, for the
// C-interface functions that take an fd. Output goes straight to the
// descriptor -- there is no buffer to flush -- and the descriptor is left
// open when the stream goes away.

#ifndef FDOSTREAM_H_
#define FDOSTREAM_H_

#include <ostream>
#include <streambuf>

#ifdef _MSC_VER
#include <io.h>
#else
#include <unistd.h>
#endif

namespace stp
{

class FdOutBuf : public std::streambuf
{
public:
  explicit FdOutBuf(int fd) : fd(fd) {}

protected:
  int_type overflow(int_type c) override
  {
    if (!traits_type::eq_int_type(c, traits_type::eof()))
    {
      const char ch = traits_type::to_char_type(c);
      if (writeAll(&ch, 1) != 1)
        return traits_type::eof();
    }
    return traits_type::not_eof(c);
  }

  std::streamsize xsputn(const char* s, std::streamsize n) override
  {
    return writeAll(s, n);
  }

private:
  // write() may stop short of the whole request (a pipe filling up, a
  // signal); the stream contract wants everything out or an error.
  std::streamsize writeAll(const char* s, std::streamsize n)
  {
    std::streamsize done = 0;
    while (done < n)
    {
#ifdef _MSC_VER
      const int got =
          _write(fd, s + done, static_cast<unsigned int>(n - done));
#else
      const ssize_t got = write(fd, s + done, static_cast<size_t>(n - done));
#endif
      if (got <= 0)
        break;
      done += got;
    }
    return done;
  }

  int fd;
};

class FdOStream : public std::ostream
{
public:
  explicit FdOStream(int fd) : std::ostream(nullptr), buf(fd) { rdbuf(&buf); }

private:
  FdOutBuf buf;
};

} // namespace stp

#endif
