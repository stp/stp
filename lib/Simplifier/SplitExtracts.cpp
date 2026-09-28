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
#include "stp/Simplifier/Simplifier.h"

namespace stp
{
  // The walk is over the whole input, so its depth is the input's depth and
  // it cannot be left on the call stack: the depth is chosen by whoever wrote
  // the query. Frames carry the position within the parent's children, so
  // the order entries are appended in is exactly what the recursion produced
  // -- ranges for one symbol are sorted afterwards by an unstable sort, and
  // equal keys would otherwise be free to reorder.
  void SplitExtracts::buildMap(const ASTNode & n, std::unordered_set<uint64_t> &visited, NodeToExtractsMap& nodeToExtracts)
  {
    if (n.Degree() == 0)
      return;

    if (!visited.insert(n.GetNodeNum()).second)
      return;

    struct Frame
    {
      ASTNode n;
      size_t i = 0; // the operand being worked on
    };

    std::vector<Frame> stack;
    stack.push_back(Frame{n});

    while (!stack.empty())
    {
      if (stack.back().i == stack.back().n.Degree())
      {
        stack.pop_back();
        continue;
      }

      // Both are read before anything can push and invalidate the frame.
      const ASTNode parent = stack.back().n;
      const ASTNode c = parent[stack.back().i];
      stack.back().i++;

      if (c.GetKind() == stp::SYMBOL && parent.GetKind() == stp::BVEXTRACT)
      {
        nodeToExtracts[c].push_back(std::make_tuple(parent, parent[1].GetUnsignedConst(), parent[2].GetUnsignedConst()));
        extractsFound++;
      }
      else if (c.GetKind() == stp::SYMBOL)
      {
        nodeToExtracts[c].push_back(std::make_tuple(ASTUndefined, UINT64_MAX,0));
      }

      // The two early returns of the recursive form, in the same order.
      if (c.Degree() == 0)
        continue;
      if (!visited.insert(c.GetNodeNum()).second)
        continue;

      stack.push_back(Frame{c});
    }
  }

  ASTNode SplitExtracts::topLevel(const ASTNode& n, Simplifier* simp)
  {
    assert(bm.UserFlags.enable_split_extracts);

    introduced = 0;
    extractsFound =0;

    bm.GetRunTimes()->start(RunTimes::SplitExtracts);

    // Splitting records a definition of the symbol in the substitution map,
    // which requires that the symbol isn't already a key of the map.
    // After applying any pending substitutions, no symbol left in the
    // formula is a key.
    ASTNode result = simp->applySubstitutionMapAtTopLevel(n);

    // Needs the full global context to figure it out.
    // Think, we might be able to keep visited between invocations
    // of topLevel if no extracts are found?
    NodeToExtractsMap  nodeToExtracts;

    std::unordered_set<uint64_t> visited;
    buildMap(result, visited, nodeToExtracts);

    if (extractsFound > 0)
    {
      bool substitutionsAdded = false;

      for (const auto& e: nodeToExtracts )
      {
        [[maybe_unused]] const auto& symbol = e.first;
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

        // An extract is split out iff its range overlaps no other use of
        // the symbol. Non-extract uses were recorded as covering every
        // bit, so they block all splitting.
        std::vector<std::pair<uint64_t, uint64_t>> toSplit; // (high, low)
        uint64_t highest = 0;

        for (unsigned i = 0; i < ranges.size(); i++)
        {
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
          assert(std::get<0>(ranges[i]).GetKind() == BVEXTRACT);
          assert(std::get<0>(ranges[i])[0] == symbol);
          toSplit.push_back({high, low});
          }
        }

        if (toSplit.empty())
          continue;

        // Rename the symbol piecewise: a fresh variable for each split
        // range and for each gap between them. The one substitution map
        // entry both rewrites the formula (a split extract over the concat
        // simplifies to its fresh variable) and rebuilds the symbol's
        // value during model construction.
        const uint64_t width = symbol.GetValueWidth();
        ASTNode concatenated;
        const auto append = [&](const ASTNode& piece) {
          if (concatenated.IsNull())
            concatenated = piece;
          else
            concatenated = bm.defaultNodeFactory->CreateTerm(
                BVCONCAT,
                concatenated.GetValueWidth() + piece.GetValueWidth(), piece,
                concatenated);
        };

        uint64_t nextBit = 0;
        for (const auto& range : toSplit)
        {
          const uint64_t high = range.first;
          const uint64_t low = range.second;
          if (low > nextBit)
            append(bm.CreateFreshVariable(0, low - nextBit, "_STP"));
          append(bm.CreateFreshVariable(0, high - low + 1, "_STP"));
          nextBit = high + 1;
        }
        if (nextBit < width)
          append(bm.CreateFreshVariable(0, width - nextBit, "_STP"));

        assert(concatenated.GetValueWidth() == width);

        // Fails if the extensionality context protects the symbol.
        if (simp->UpdateSubstitutionMapFewChecks(symbol, concatenated))
        {
          introduced += toSplit.size();
          substitutionsAdded = true;
        }
      }

      if (substitutionsAdded)
        result = simp->applySubstitutionMapAtTopLevel(result);
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
