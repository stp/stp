/********************************************************************
 * AUTHORS: Trevor Hansen
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

#ifndef TOCNFGIA_H_
#define TOCNFGIA_H_

// From ABC
#include "aig/gia/gia.h"

#include "stp/AIG/CNF.h"
#include "stp/STPManager/UserDefinedFlags.h"
#include "stp/ToSat/BBNodeManagerGia.h"
#include "stp/ToSat/ToSATBase.h"

namespace stp
{

// The Gia backend's route to CNF, and the whole of it: assert the formula as
// the manager's one output, hand the graph to Mf_ManGenerateCnf, and project
// the inputs back to the symbols they came from.
//
// Mf_ManGenerateCnf is the generator behind --cnf-generation-effort low, high
// and very-high, and it takes a Gia. ToCNFAIG reaches it by building an ABC
// Aig and calling Gia_ManFromAig, so a graph at 48 bytes an object and a
// graph at 12 are both live when the mapper runs. Here the blaster built the
// Gia, so there is no Aig and no conversion -- nothing between the manager
// and the generator at all.
//
// ToCNFAIG also has a dag-aware rewriting loop and a manager-to-manager copy
// to re-index after. Neither applies: Dar rewriting is an Aig pass with no
// Gia equivalent that does not convert, and nothing else here renumbers.
class ToCNFGia
{
  UserDefinedFlags& uf;

  // The LUT size Mf enumerates cuts up to, which is what the effort level
  // selects. 3, 6 and 8 are the sizes ToCNFAIG uses for low, high and
  // very-high, and the gia- levels mirror them so that an A/B between the two
  // backends is one word on the command line.
  int nLutSize;

  static int lutSizeOf(const UserDefinedFlags& uf)
  {
    switch (uf.cnf_effort)
    {
      case UserDefinedFlags::CNF_EFFORT_GIA_LOW:
        return 3;
      case UserDefinedFlags::CNF_EFFORT_GIA_VERY_HIGH:
        return 8;
      case UserDefinedFlags::CNF_EFFORT_GIA_HIGH:
      default:
        return 6;
    }
  }

public:
  // One argument, like the other two lowerings, so that the templated body in
  // ToSATAIG constructs any of them the same way. The LUT size is not a
  // second knob -- it is the effort level, read back off the flags.
  explicit ToCNFGia(UserDefinedFlags& _uf) : uf(_uf), nLutSize(lutSizeOf(_uf))
  {
    assert(nLutSize >= 3 && nLutSize <= 8);
  }

  // The same signature as ToCNFAIG::toCNF and ToCNFTseitin::toCNF, so one
  // templated body drives any of them.
  //
  // needAbsRef is taken and ignored, as it is by the Tseitin writer. It
  // exists on the ABC-Aig path to suppress Aig_ManCleanup, because a cleanup
  // renumbers and refinement has to be able to name an input afterwards.
  // Nothing here removes an object, so there is nothing for the flag to
  // protect.
  void toCNF(const BBNodeGia& top, CNF& cnf,
             ToSATBase::ASTNodeToSATVar& nodeToVars, bool needAbsRef,
             BBNodeManagerGia& mgr);
};

} // namespace stp

#endif /* TOCNFGIA_H_ */
