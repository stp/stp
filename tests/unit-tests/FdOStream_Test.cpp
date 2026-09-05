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

// FdOStream backs the fd-taking C-interface printers (vc_printExprFile,
// vc_printCounterExampleFile). What those callers rely on: everything
// written through the stream reaches the descriptor byte-for-byte, without
// the caller flushing, and a dead descriptor surfaces as a stream error
// rather than silence.

#include "stp/Interface/FdOStream.h"
#include <cstdio>
#include <gtest/gtest.h>
#include <string>

#ifdef _MSC_VER
#include <io.h>
#define stp_test_fileno _fileno
#define stp_test_lseek _lseek
#define stp_test_read _read
#define stp_test_dup _dup
#define stp_test_close _close
#else
#include <unistd.h>
#define stp_test_fileno fileno
#define stp_test_lseek lseek
#define stp_test_read read
#define stp_test_dup dup
#define stp_test_close close
#endif

namespace
{

// A temporary file the OS deletes on close, exposed as a raw descriptor.
struct TempFd
{
  FILE* file;
  int fd;

  TempFd() : file(std::tmpfile()), fd(stp_test_fileno(file)) {}
  ~TempFd() { std::fclose(file); }

  // Everything the descriptor received, read back through the descriptor
  // itself so no stdio buffering can interfere.
  std::string contents() const
  {
    std::string all;
    stp_test_lseek(fd, 0, SEEK_SET);
    char chunk[4096];
    for (;;)
    {
      const auto got = stp_test_read(fd, chunk, sizeof(chunk));
      if (got <= 0)
        break;
      all.append(chunk, static_cast<size_t>(got));
    }
    return all;
  }
};

TEST(FdOStream_Test, formatted_output_reaches_the_descriptor)
{
  TempFd tmp;
  stp::FdOStream os(tmp.fd);

  os << "x = " << 42 << ", mask = 0x" << std::hex << 255 << std::dec << '\n'
     << "done";

  EXPECT_TRUE(os.good());
  EXPECT_EQ(tmp.contents(), "x = 42, mask = 0xff\ndone");
}

TEST(FdOStream_Test, no_flush_is_needed)
{
  TempFd tmp;
  stp::FdOStream os(tmp.fd);

  os << "immediately visible";

  // Deliberately no flush: the callers in c_interface.cpp don't flush
  // either, so the bytes have to be at the descriptor already.
  EXPECT_EQ(tmp.contents(), "immediately visible");
}

TEST(FdOStream_Test, single_character_writes)
{
  TempFd tmp;
  stp::FdOStream os(tmp.fd);

  std::string expected;
  for (int i = 0; i < 1000; i++)
  {
    const char c = static_cast<char>('a' + i % 26);
    os.put(c);
    expected.push_back(c);
  }

  EXPECT_TRUE(os.good());
  EXPECT_EQ(tmp.contents(), expected);
}

TEST(FdOStream_Test, large_write_arrives_intact)
{
  TempFd tmp;
  stp::FdOStream os(tmp.fd);

  std::string big;
  big.reserve(1 << 20);
  while (big.size() < (1 << 20))
    big += "0123456789abcdef";

  os.write(big.data(), big.size());

  EXPECT_TRUE(os.good());
  EXPECT_EQ(tmp.contents(), big);
}

TEST(FdOStream_Test, dead_descriptor_sets_badbit)
{
  TempFd tmp;
  const int dead = stp_test_dup(tmp.fd);
  stp_test_close(dead);

  stp::FdOStream os(dead);
  EXPECT_TRUE(os.good());

  os << "lost";
  EXPECT_TRUE(os.bad());

  os.clear();
  os.put('x');
  EXPECT_TRUE(os.bad());
}

} // namespace
