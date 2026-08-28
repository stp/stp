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

#include <ostream>

namespace stp
{

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
}

} // namespace stp
