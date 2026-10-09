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

#pragma once
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

namespace stpp
{
// One sequential solver configuration. A Batch configuration is the ordinary
// route with its option overrides; the Retained route is the incremental
// driver's plain check, the group's hedge. Option names and values are the
// public stp::Options registry's. stp-p offers the `product` entries only
// (default and eager-arrays); the test driver offers every entry, for
// portfolios and measurements.
struct Config
{
  enum class Route
  {
    Batch,
    Retained
  };
  std::string name;
  Route route = Route::Batch;
  std::uint32_t seed_offset = 0;
  std::vector<std::pair<std::string, std::string>> options;
  std::string summary;
  bool product = false;
};
const std::vector<Config>& configs();
// Throws for a name the table does not hold. (Which entries stp-p offers is
// its command line's to check: Config::product.)
const Config& config(const std::string& name);
// The comma-separated portfolio list, validated: known, distinct names.
std::vector<std::string> portfolio_list(const std::string& text);
} // namespace stpp
