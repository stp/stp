/********************************************************************
 * AUTHORS: Andrew Teylu
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

#include "stp/c_interface.h"

#include <cerrno>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>

#if defined(__unix__) || defined(__APPLE__)
#include <sys/resource.h>
#endif

namespace
{

uint64_t parseIterations(const char* text)
{
  errno = 0;
  char* end = nullptr;
  const unsigned long long value = std::strtoull(text, &end, 10);
  if (errno != 0 || end == text || *end != '\0' || value == 0)
    return 0;
  return static_cast<uint64_t>(value);
}

uint64_t peakRSSKiB()
{
#if defined(__linux__)
  // Linux's getrusage(RUSAGE_SELF).ru_maxrss can retain the invoking shell's
  // high-water mark when that shell tail-execs this program. /proc belongs to
  // the new address space and therefore measures this benchmark itself.
  std::FILE* status = std::fopen("/proc/self/status", "r");
  if (status == nullptr)
    return 0;
  char line[256];
  uint64_t peak = 0;
  while (std::fgets(line, sizeof(line), status) != nullptr)
  {
    unsigned long long value = 0;
    if (std::sscanf(line, "VmHWM: %llu kB", &value) == 1)
    {
      peak = static_cast<uint64_t>(value);
      break;
    }
  }
  std::fclose(status);
  return peak;
#elif defined(__APPLE__)
  struct rusage usage;
  if (getrusage(RUSAGE_SELF, &usage) != 0)
    return 0;
  return static_cast<uint64_t>(usage.ru_maxrss) / 1024;
#elif defined(__unix__)
  struct rusage usage;
  if (getrusage(RUSAGE_SELF, &usage) != 0)
    return 0;
  return static_cast<uint64_t>(usage.ru_maxrss);
#else
  return 0;
#endif
}

} // namespace

int main(int argc, char** argv)
{
  uint64_t iterations = 1000000;
  bool enableUF = false;
  for (int i = 1; i < argc; ++i)
  {
    if (std::strcmp(argv[i], "--uf") == 0)
      enableUF = true;
    else if (std::strcmp(argv[i], "--iterations") == 0 && i + 1 < argc)
    {
      iterations = parseIterations(argv[++i]);
      if (iterations == 0)
      {
        std::fprintf(stderr, "invalid --iterations value\n");
        return 2;
      }
    }
    else
    {
      std::fprintf(stderr,
                   "usage: %s [--uf] [--iterations positive-integer]\n",
                   argv[0]);
      return 2;
    }
  }

  VC vc = vc_createValidityChecker();
  if (vc == nullptr)
    return 3;
  // Every benchmarked wrapper has exactly one owner: the loop below. This
  // makes the benchmark independent of STP's optional context-persist list.
  vc_setInterfaceFlags(vc, EXPRDELETE, 0);
  if (enableUF)
    vc_setFlag(vc, 'u');

  const std::chrono::steady_clock::time_point start =
      std::chrono::steady_clock::now();
  for (uint64_t i = 0; i < iterations; ++i)
  {
    // Deliberately request the same hash-consed constant. The measured churn
    // is the public Expr wrapper and, in UF mode, its live-handle registry.
    Expr expression = vc_bvConstExprFromInt(vc, 8, 42);
    if (expression == nullptr)
      return 4;
    vc_DeleteExpr(expression);
  }
  const std::chrono::duration<double> elapsed =
      std::chrono::steady_clock::now() - start;

  const uint64_t peak = peakRSSKiB();
  vc_Destroy(vc);
  std::printf("mode=%s iterations=%llu seconds=%.6f peak_rss_kib=%llu\n",
              enableUF ? "uf" : "legacy",
              static_cast<unsigned long long>(iterations), elapsed.count(),
              static_cast<unsigned long long>(peak));
  return 0;
}
