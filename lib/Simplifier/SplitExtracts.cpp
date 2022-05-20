/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: May-2022
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

#include "stp/Simplifier/SplitExtracts.h"
#include "stp/Simplifier/SubstitutionMap.h"

namespace stp
{
  void SplitExtracts::buildMap(const ASTNode & n, std::unordered_set<uint64_t> &visited, NodeToExtractsMap& nodeToExtracts)
  {
    if (n.Degree() == 0)
      return;

    if (!visited.insert(n.GetNodeNum()).second)
      return;

    for (const auto & c :n)
    {
      if (c.GetKind() == stp::SYMBOL && n.GetKind() == stp::BVEXTRACT)
      {
        nodeToExtracts[c].push_back(std::make_tuple(n, n[1].GetUnsignedConst(), n[2].GetUnsignedConst()));
        extractsFound++;
      }
      else if (c.GetKind() == stp::SYMBOL)
      {
      nodeToExtracts[c].push_back(std::make_tuple(ASTUndefined, UINT64_MAX,0));
      }

      buildMap(c,visited,nodeToExtracts);
    }
  }

  ASTNode SplitExtracts::topLevel(const ASTNode& n)
  { 
    assert(bm.UserFlags.enable_split_extracts);

    // TODO doesn't construct the model yet.
    // It requires a messy implementation.
    if (bm.UserFlags.construct_counterexample_flag)
    {
      if (bm.UserFlags.stats_flag)
        std::cerr << "{Split Extracts} Disabled" << std::endl;
      return n;
    }

    ASTNode result = n;

    introduced = 0;
    extractsFound =0;

    // Needs the full global context to figure it out.
    // Think, we might be able to keep visited between invocations
    // of topLevel if no extracts are found?
    NodeToExtractsMap  nodeToExtracts;

    bm.GetRunTimes()->start(RunTimes::SplitExtracts);

    std::unordered_set<uint64_t> visited;
    buildMap(n,visited, nodeToExtracts);

    if (extractsFound > 0)
    {
      ASTNodeMap fromTo;

      for (const auto& e: nodeToExtracts )
      {
        const auto& symbol = e.first;
        assert(symbol.GetKind() == SYMBOL);

        auto ranges = e.second;

        if (ranges.size() < 2)
          continue; // Don't want to split if there's just one.

        auto comp = [](const auto& p0, const auto& p1)
        { 
          return std::get<2>(p0) < std::get<2>(p1); 
        };

        // Afterwards e.g. (4,0) (3,3) (8,5)
        sort(ranges.begin(), ranges.end(), comp);

        uint64_t highest = 0;

        for (unsigned i = 0; i < ranges.size(); i++)
        {
          const auto extract = std::get<0>(ranges[i]);
          const auto high = std::get<1>(ranges[i]);
          const auto low = std::get<2>(ranges[i]);
          assert(high >= low);

          bool replace = true;
          if (i+1 != ranges.size())  // check up.
          {
            // e.g. if (4,3) (6,4)..
            if (std::get<2>(ranges[i+1]) <= high)
            replace = false;
          }

        if (i != 0) // check down.
        {
            if (low <= highest)
            replace = false;

          highest = std::max(high, highest);
        }
        else
        {
          highest = high;
        }

          if (replace)
          {
          assert(extract.GetKind() == BVEXTRACT);
          assert(extract[0] == symbol);
            const auto fresh = bm.CreateFreshVariable(0,high-low+1, "_STP");
          fromTo.insert({extract,fresh});
          introduced++;
          }
        }
      }

      if (fromTo.size() > 0)
      {
        ASTNodeMap cache;
        result = stp::SubstitutionMap::replace(n, fromTo, cache, bm.defaultNodeFactory);
      }
    }

    bm.GetRunTimes()->stop(RunTimes::SplitExtracts);

    if (bm.UserFlags.stats_flag)
    {
      std::cerr << "{Split Extracts} Extracts over variables found: " << extractsFound << std::endl;
      std::cerr << "{Split Extracts} variables introduced: " << introduced << std::endl;
    }

    return result;
  }
}
