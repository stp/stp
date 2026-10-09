/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: October, 2026
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

// stp-p runs on the build's allocator: a static archive the link skips
// leaves every process on libc's malloc, a third slower on short inputs.
// Registered only when the build links mimalloc statically; STP_P is the
// stp-p binary.
#include <gtest/gtest.h>
#include <cstdlib>
#include <string>
#include <sys/wait.h>
#include <unistd.h>

TEST(StppAllocator, StpPStartsOnMimalloc)
{
  int fds[2];
  ASSERT_EQ(pipe(fds), 0);
  const pid_t pid = fork();
  ASSERT_GE(pid, 0);
  if (!pid)
  {
    dup2(fds[1], STDERR_FILENO);
    dup2(fds[1], STDOUT_FILENO);
    close(fds[0]);
    close(fds[1]);
    setenv("MIMALLOC_VERBOSE", "1", 1);
    execl(STP_P, STP_P, "--version", static_cast<char*>(nullptr));
    _exit(127);
  }
  close(fds[1]);
  std::string output;
  char buffer[4096];
  for (ssize_t n; (n = read(fds[0], buffer, sizeof buffer)) > 0;)
    output.append(buffer, n);
  close(fds[0]);
  int status = 0;
  ASSERT_EQ(waitpid(pid, &status, 0), pid);
  EXPECT_TRUE(WIFEXITED(status) && WEXITSTATUS(status) == 0) << output;
  EXPECT_NE(output.find("mimalloc: process init"), std::string::npos) << output;
  EXPECT_NE(output.find("stp-p (STP "), std::string::npos) << output;
}
