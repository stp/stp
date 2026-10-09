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

#include "Portfolio.h"
#include <algorithm>
#include <stdexcept>

namespace stpp
{
const std::vector<Config>& configs()
{
  using R = Config::Route;
  // stp-p's own: ordinary STP, and the eager array axioms that let a check
  // with many array reads offer the group its fork point (an equality
  // between arrays of floating-point elements, or a constant array, still
  // refines). The rest are the test driver's: the seed offsets (the
  // seed-only control), the hedge's route alone, and CNF and CaDiCaL
  // variants for --portfolio.
  static const std::vector<Config> table = {
      {"default", R::Batch, 0, {}, "ordinary STP", true},
      {"eager-arrays", R::Batch, 0, {{"ackermanize", "true"}},
       "array-read axioms encoded eagerly, exact floating point", true},
      {"seed1", R::Batch, 1, {}, "ordinary STP, random seed + 1"},
      {"seed2", R::Batch, 2, {}, "ordinary STP, random seed + 2"},
      {"seed3", R::Batch, 3, {}, "ordinary STP, random seed + 3"},
      {"retained", R::Retained, 0, {},
       "the hedge's route: the incremental driver's plain check"},
      {"cnf-gia-high", R::Batch, 0, {{"cnf-generation-effort", "gia-high"}},
       "higher-effort LUT-mapped CNF"},
      {"cnf-new-low", R::Batch, 0, {{"cnf-generation-effort", "new-low"}},
       "pattern recovery without maximal-AND collapse"},
      {"no-factor", R::Batch, 0, {{"cadical-factor", "off"}},
       "CaDiCaL without bounded variable addition"},
  };
  return table;
}

const Config& config(const std::string& name)
{
  const auto& table = configs();
  auto it = std::find_if(table.begin(), table.end(),
                         [&](const Config& c) { return c.name == name; });
  if (it == table.end())
    throw std::runtime_error("unknown configuration: " + name);
  return *it;
}

std::vector<std::string> portfolio_list(const std::string& text)
{
  std::vector<std::string> names;
  std::size_t at = 0;
  for (;;)
  {
    auto comma = text.find(',', at);
    auto name = text.substr(at, comma == std::string::npos ? std::string::npos
                                                           : comma - at);
    config(name);
    if (std::find(names.begin(), names.end(), name) != names.end())
      throw std::runtime_error("duplicate portfolio configuration: " + name);
    names.push_back(name);
    if (comma == std::string::npos)
      break;
    at = comma + 1;
  }
  return names;
}
} // namespace stpp
