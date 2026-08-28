/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: Aug, 2026
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

#include "stp/STPManager/UserDefinedFlags.h"

#include <cctype>
#include <ostream>
#include <sstream>
#include <vector>

namespace stp
{

namespace
{

// In BVSchemaGroup order; the static_assert below is the only thing that
// keeps the two in step.
const char* const GROUP_NAMES[] = {"base",
                                   "udiv15",
                                   "udiv-observed",
                                   "udiv-tail",
                                   "urem",
                                   "quotient-one-quot",
                                   "quotient-one-rem",
                                   "mul8",
                                   "mul-ref3",
                                   "mul-tail",
                                   "add"};

static_assert(sizeof(GROUP_NAMES) / sizeof(GROUP_NAMES[0]) ==
                  BV_SCHEMA_GROUP_COUNT,
              "BV schema group names are out of step with the enum");

std::string trim(const std::string& text)
{
  size_t first = 0;
  while (first < text.size() &&
         std::isspace(static_cast<unsigned char>(text[first])))
    ++first;
  size_t last = text.size();
  while (last > first &&
         std::isspace(static_cast<unsigned char>(text[last - 1])))
    --last;
  return text.substr(first, last - first);
}

std::string expectedGroups()
{
  std::ostringstream out;
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
  {
    if (i != 0)
      out << ", ";
    out << GROUP_NAMES[i];
  }
  out << ", udiv, mul6, quotient-one, all, or none";
  return out.str();
}

bool groupAliasMask(const std::string& token, uint32_t& aliasMask)
{
  if (token == "udiv")
    aliasMask = bvSchemaGroupBit(BVSchemaGroup::UDIV15) |
                bvSchemaGroupBit(BVSchemaGroup::UDIV_OBSERVED);
  else if (token == "mul6")
    aliasMask = bvSchemaGroupBit(BVSchemaGroup::MUL_REF3);
  else if (token == "quotient-one")
    aliasMask = bvSchemaGroupBit(BVSchemaGroup::QUOTIENT_ONE_REM) |
                bvSchemaGroupBit(BVSchemaGroup::QUOTIENT_ONE_QUOT);
  else
    return false;
  return true;
}

} // namespace

const char* bvSchemaGroupName(BVSchemaGroup group)
{
  const unsigned index = static_cast<unsigned>(group);
  return index < BV_SCHEMA_GROUP_COUNT ? GROUP_NAMES[index] : "unknown";
}

bool parseBVSchemaGroups(const std::string& text, uint32_t& mask,
                         std::string& error)
{
  std::vector<std::string> tokens;
  size_t begin = 0;
  while (begin <= text.size())
  {
    const size_t comma = text.find(',', begin);
    const size_t end = comma == std::string::npos ? text.size() : comma;
    const std::string token = trim(text.substr(begin, end - begin));
    if (token.empty())
    {
      error = "empty BV schema group; expected " + expectedGroups();
      return false;
    }
    tokens.push_back(token);
    if (comma == std::string::npos)
      break;
    begin = comma + 1;
  }

  if (tokens.size() != 1 && (tokens[0] == "all" || tokens[0] == "none"))
  {
    error = "'all' and 'none' must be used alone";
    return false;
  }
  for (size_t i = 1; i < tokens.size(); ++i)
    if (tokens[i] == "all" || tokens[i] == "none")
    {
      error = "'all' and 'none' must be used alone";
      return false;
    }

  if (tokens.size() == 1 && tokens[0] == "all")
  {
    mask = BV_SCHEMA_GROUP_ALL;
    error.clear();
    return true;
  }
  if (tokens.size() == 1 && tokens[0] == "none")
  {
    mask = 0;
    error.clear();
    return true;
  }

  uint32_t parsed = 0;
  for (const std::string& token : tokens)
  {
    bool found = false;
    for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
      if (token == GROUP_NAMES[i])
      {
        parsed |= bvSchemaGroupBit(static_cast<BVSchemaGroup>(i));
        found = true;
        break;
      }
    uint32_t aliasMask = 0;
    if (!found && groupAliasMask(token, aliasMask))
    {
      parsed |= aliasMask;
      found = true;
    }
    if (!found)
    {
      error = "unknown BV schema group '" + token + "'; expected " +
              expectedGroups();
      return false;
    }
  }

  mask = parsed;
  error.clear();
  return true;
}

std::string formatBVSchemaGroups(uint32_t mask)
{
  if (mask == 0)
    return "none";
  if (mask == BV_SCHEMA_GROUP_ALL)
    return "all";

  std::ostringstream out;
  bool first = true;
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
    if (bvSchemaGroupEnabled(mask, static_cast<BVSchemaGroup>(i)))
    {
      if (!first)
        out << ',';
      out << GROUP_NAMES[i];
      first = false;
    }
  return out.str();
}


void printAbstractionCoverage(const UserDefinedFlags& uf, std::ostream& out)
{
  // Report what reached the bit-blaster, what abstraction accepted, and what
  // refinement spent. Counting syntax instead would include arithmetic that
  // simplification retired before it could cost either abstraction or SAT.
  const UserDefinedFlags::EncodingCoverage& c = uf.coverage;
  // In AbstractionKind order; a kind added there needs a name here.
  static const char* kindNames[] = {"eq",   "compare", "ite",
                                    "plus", "mult",    "divmod"};
  static_assert(sizeof(kindNames) / sizeof(kindNames[0]) ==
                    UserDefinedFlags::EncodingCoverage::KINDS,
                "abstraction kind names are out of step with the counters");

  out << "Abstraction coverage (candidates -> abstracted):";
  for (unsigned i = 0; i < UserDefinedFlags::EncodingCoverage::KINDS; ++i)
    out << " " << kindNames[i] << "=" << c.bv_candidates[i] << "->"
        << c.bv_abstracted[i];
  out << std::endl
      << "Abstraction refinement: rounds=" << c.bv_refinement_rounds
      << " blocking=" << c.bv_blocking_lemmas
      << " schema=" << c.bv_schema_lemmas
      << " exact=" << c.bv_exact_escalations
      << " exact-mult=" << c.bv_exact_escalations_mult
      << " exact-divmod=" << c.bv_exact_escalations_divmod << std::endl;

  // Keep the established refinement line stable, and print this one whenever
  // there is a cost to report rather than whenever a refinement gave up.
  if (c.bv_exact_clauses != 0 || c.bv_exact_variables != 0)
    out << "Abstraction circuit cost: clauses=" << c.bv_exact_clauses
        << " variables=" << c.bv_exact_variables
        << " microseconds=" << c.bv_exact_microseconds << std::endl;

  // Reported separately from the line above, because what the schemas cost is
  // the thing a comparison between refinement settings is about. Rolled into
  // the full-width installs it would be invisible next to one exact divider;
  // reported on its own a run whose only refinement was schema lemmas has a
  // price rather than a blank.
  if (c.bv_schema_clauses != 0 || c.bv_schema_variables != 0)
    out << "Abstraction schema cost: clauses=" << c.bv_schema_clauses
        << " variables=" << c.bv_schema_variables
        << " microseconds=" << c.bv_schema_microseconds << std::endl;

  // Always the complete partition, zeros included: a zero says that an
  // enabled family fired nothing, which is only readable next to the mask
  // that was selected. Omitting the empty ones would make the two runs a
  // comparison is between look like different reports.
  out << "Abstraction schemas by group:";
  for (unsigned i = 0; i < BV_SCHEMA_GROUP_COUNT; ++i)
    out << " " << bvSchemaGroupName(static_cast<BVSchemaGroup>(i)) << "="
        << c.bv_schema_group_lemmas[i];
  out << std::endl;
}

} // namespace stp
