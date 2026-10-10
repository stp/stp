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

// Run in a child with a bounded address space. Keep the library's allocator
// choice with its embedder, as a normal C++ API consumer does.
#include <stp/stp.hpp>

#include <cstdio>
#include <exception>

int main(int argc, char** argv)
{
  try
  {
    if (argc == 1)
    {
      for (const auto& backend : stp::sat_backends())
        std::puts(backend.c_str());
      return 0;
    }
    if (argc != 3)
      return 2;
    stp::TermManager tm;
    stp::Options options;
    options.set("sat-backend", argv[1]);
    options.set_bool("produce-models", false);
    stp::Solver solver(tm, options);
    try
    {
      solver.parse_file(argv[2]);
      if (!solver.check_sat().is_sat())
        return 3;
      std::puts("sat");
      return 0;
    }
    catch (const stp::UnsafeError& e)
    {
      if (e.code() != stp::ErrorCode::RESOURCE || e.recoverable())
        throw;
      std::fprintf(stderr, "%s\n", e.what());
      // The failure belongs to this manager; another solver must refuse it.
      try
      {
        stp::Solver again(tm);
        return 4;
      }
      catch (const stp::Error& poisoned)
      {
        if (poisoned.code() != stp::ErrorCode::STATE)
          throw;
      }
      return 255;
    }
  }
  catch (const std::exception& e)
  {
    std::fprintf(stderr, "unexpected error: %s\n", e.what());
    return 5;
  }
}
