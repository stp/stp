/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
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

// Library.cpp -- the library-level queries: version and capabilities.

#include "Internal.h"

#include "stp/Sat/SATSolverFactory.h"
#include "stp/Util/GitSHA1.h"
#include "stp/config.h"

#include <sstream>

namespace stp
{
namespace api
{

Version version()
{
  Version v;
  v.major = STP_VERSION_MAJOR;
  v.minor = STP_VERSION_MINOR;
#ifdef STP_VERSION_PATCH
  v.patch = STP_VERSION_PATCH;
#else
  v.patch = 0;
#endif
  v.string = STP_VERSION;
  v.git_sha = get_git_version_sha();
  v.git_tag = get_git_version_tag();
  v.build_info = get_compilation_env();
  return v;
}

std::vector<std::string> sat_backends()
{
  std::vector<std::string> out;
#if STP_BUILD_WITH_CRYPTOMINISAT
  out.emplace_back("cryptominisat");
#endif
#if STP_BUILD_WITH_CADICAL
  out.emplace_back("cadical");
#endif
#if STP_BUILD_WITH_MINISAT
  out.emplace_back("minisat");
  out.emplace_back("simplifying-minisat");
#endif
  return out;
}

bool has_sat_backend(std::string_view name)
{
  for (const std::string& b : sat_backends())
    if (name == b)
      return true;
  return false;
}

std::map<std::string, std::string> capabilities()
{
  std::map<std::string, std::string> c;
  std::string backends;
  for (const std::string& b : sat_backends())
    backends += (backends.empty() ? "" : ",") + b;
  c["sat.backends"] = backends;
  for (const std::string& entry : compiledSolverVersions())
  {
    const std::size_t space = entry.find(' ');
    if (space != std::string::npos)
      c["sat.backend." + entry.substr(0, space) + ".version"] = entry.substr(space + 1);
  }
  c["array.element-sorts"] = "bv,fp,rm,uninterpreted";
  c["array.index-sorts"] = "bv,fp,rm,uninterpreted";
  c["array.const-equality"] = "false";
  c["lra"] = "true";
  c["real.nonlinear"] = "false";
#ifdef STP_HAVE_HIGHS
  c["highs"] = "true";
#else
  c["highs"] = "false";
#endif
  c["fp.rem.limit"] = "2^eb+sb-4<=2304";
  c["kind.FP_TO_REAL"] = "values-only";
  c["kind.FP_TO_FP_FROM_REAL"] = "values-only";
  c["cores.assertions"] = "false";
  c["cores.assumptions"] = "true";
  c["solvers-per-manager"] = "unbounded";
  c["interrupt.cryptominisat"] = "between-solver-calls";
  c["threads"] = "any-thread-one-call-at-a-time";
  c["api.version"] = "3.0.0-alpha";
  return c;
}

} // namespace api
} // namespace stp
