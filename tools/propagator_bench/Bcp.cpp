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

// The other reference the propagators can be held against: not the ideal, but
// what unit propagation on the bit-blasted encoding deduces on its own.
//
// STP bit-blasts to CNF and hands the result to a SAT solver, so a word-level
// propagator only earns its keep if it fixes bits that boolean constraint
// propagation over the same circuit would not have fixed anyway. This encodes
// `op(children) = result` once per (operation, layout), then per case asserts
// the known bits as unit clauses and counts what comes out fixed at decision
// level zero.
//
// This is the measurement that tools/measure_constantbitprop used to make,
// through include/stp/Util/BBAsProp.h. That version handled two same-width
// children and one result, which is why its table only ever covered bvsge.
// Three things it did not do, all of which matter once the other operations
// are in scope:
//
//   * The ArrayTransformer runs first. sbvdiv, sbvrem and sbvmod are not
//     bit-blasted directly -- they are rewritten into other operations -- so
//     bit-blasting them straight would hit an unhandled kind.
//   * Bits of a symbol that never reached the CNF are marked with a sentinel
//     in the variable map rather than a variable number, and have to be
//     skipped instead of asserted.
//   * Structural children (the bounds of an extract, the width of an extend)
//     are constants in the encoded node, so they are neither asserted nor
//     counted. Both sides of the comparison are taken over the varying
//     children and the result only.
//
// CryptoMiniSat only: getFixedCountWithAssumptions is a CryptoMiniSat5
// method. Without it the whole file compiles to a "not available" stub and
// --bcp-check is refused at the command line.

#include "PropagatorBench.h"

#ifdef USE_CRYPTOMINISAT

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/Sat/CryptoMinisat5.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/ToSat/ToSATAIG.h"

#include <unordered_set>

using namespace stp;

namespace propbench
{

// The CNF for one (operation, layout), reused across every case: bit-blasting
// is far more expensive than the propagation being measured.
struct BcpEncoding
{
  BcpEncoding(STPMgr* mgr_, const OpSpec& op, const Layout& l)
      : mgr(mgr_), sm(mgr_), simp(mgr_, &sm), at(mgr_, &simp), aig(mgr_, &at),
        ok(false)
  {
    const ASTNode node = buildNode(mgr, op, l);

    std::stringstream rname;
    rname << "pb_bcp_r_" << op.name << "_" << l.outWidth << "_"
          << l.children.size();
    const ASTNode result =
        mgr->CreateSymbol(rname.str().c_str(), 0, l.outIsBoolean ? 0 : l.outWidth);

    ASTNode constraint =
        l.outIsBoolean ? mgr->CreateNode(IFF, node, result)
                       : mgr->CreateNode(EQ, node, result);
    BVTypeCheck(constraint);

    // sbvdiv, sbvrem and sbvmod reach the bit-blaster only after this.
    constraint = at.TransformFormula_TopLevel(constraint);

    if (!aig.bitblast(constraint, false, cnf))
      return;
    // NULL means the AIG node budget stopped the blast. This tool never sets
    // one, so it cannot happen today -- but leaving `ok` false is the honest
    // answer for a layout with no CNF, and costs a single branch.
    const ToSATBase::ASTNodeToSATVar& map = aig.SATVar_to_SymbolIndexMap();

    // The varying children, in layout order, then the result. GetChildren()
    // returns the view by value, so it is held in a named local: binding a
    // reference to an element of the temporary would dangle at the end of the
    // full expression, which gcc 13 diagnoses under -Wdangling-reference.
    const ASTChildren nodeChildren = node.GetChildren();
    for (unsigned i : l.varying())
    {
      if (!collect(map, nodeChildren[i],
                   l.children[i].isBoolean ? 1 : l.children[i].width))
        return;
    }
    if (!collect(map, result, l.outIsBoolean ? 1 : l.outWidth))
      return;

    ok = true;
  }

  // Counts the variables fixed at level zero once `bits` are asserted, or
  // reports that unit propagation refuted them. `bits` is the varying children
  // followed by the result, matching vars.
  bool propagate(const vector<const FixedBits*>& bits, unsigned& fixed) const
  {
    CryptoMiniSat5 solver(1);
    aig.add_cnf_to_solver(solver, cnf);

    SATSolver::vec_literals assumps;
    for (size_t s = 0; s < bits.size(); s++)
      for (unsigned i = 0; i < bits[s]->getWidth(); i++)
      {
        if (!bits[s]->isFixed(i) || vars[s][i] == NOT_ENCODED)
          continue;
        assumps.push(
            SATSolver::mkLit(vars[s][i], !bits[s]->getValue(i)));
      }

    bool conflict = false;
    fixed = solver.getFixedCountWithAssumptions(assumps, interesting, conflict);
    return !conflict;
  }

  // How many of the given bits this encoding can see at all. Bits that never
  // reached the CNF are invisible to propagation, so they are excluded from
  // both sides of the comparison rather than counted as a loss.
  unsigned visibleFixed(const vector<const FixedBits*>& bits) const
  {
    unsigned n = 0;
    for (size_t s = 0; s < bits.size(); s++)
      for (unsigned i = 0; i < bits[s]->getWidth(); i++)
        if (bits[s]->isFixed(i) && vars[s][i] != NOT_ENCODED)
          n++;
    return n;
  }

  bool usable() const { return ok; }
  unsigned clauses() const { return (unsigned)cnf.clauseCount(); }
  unsigned variables() const { return cnf.varCount(); }

private:
  // constexpr, not const: resize() below binds it by reference, which needs
  // a definition, and in C++17 a constexpr static member is implicitly inline.
  static constexpr unsigned NOT_ENCODED = ~((unsigned)0);

  // addVariables() in ToCNFAIG.cpp writes NOT_ENCODED for the bits of a symbol
  // that did not make it into the CNF.
  bool collect(const ToSATBase::ASTNodeToSATVar& map, const ASTNode& sym,
               unsigned width)
  {
    const ToSATBase::ASTNodeToSATVar::const_iterator it = map.find(sym);
    if (it == map.end())
      return false; // simplified away entirely; nothing to compare

    vector<unsigned> v(it->second);
    v.resize(width, NOT_ENCODED);
    for (unsigned i = 0; i < width; i++)
      if (v[i] != NOT_ENCODED)
        interesting.insert(v[i]);
    vars.push_back(v);
    return true;
  }

  STPMgr* mgr;
  SubstitutionMap sm;
  Simplifier simp;
  ArrayTransformer at;
  mutable ToSATAIG aig;
  CNF cnf;
  vector<vector<unsigned>> vars; // one entry per varying child, then result
  std::unordered_set<unsigned> interesting;
  bool ok;
};

bool bcpAvailable()
{
  return true;
}

BcpEncoding* makeBcpEncoding(STPMgr* mgr, const OpSpec& op, const Layout& l)
{
  BcpEncoding* e = new BcpEncoding(mgr, op, l);
  if (!e->usable())
  {
    delete e;
    return NULL;
  }
  return e;
}

void destroyBcpEncoding(BcpEncoding* e)
{
  delete e;
}

bool bcpPropagate(const BcpEncoding* e, const vector<const FixedBits*>& bits,
                  unsigned& fixed)
{
  return e->propagate(bits, fixed);
}

unsigned bcpVisibleFixed(const BcpEncoding* e,
                         const vector<const FixedBits*>& bits)
{
  return e->visibleFixed(bits);
}

unsigned bcpClauses(const BcpEncoding* e)
{
  return e->clauses();
}

unsigned bcpVariables(const BcpEncoding* e)
{
  return e->variables();
}

} // namespace propbench

#else // !USE_CRYPTOMINISAT

namespace propbench
{

bool bcpAvailable()
{
  return false;
}

BcpEncoding* makeBcpEncoding(stp::STPMgr*, const OpSpec&, const Layout&)
{
  return NULL;
}

void destroyBcpEncoding(BcpEncoding*) {}

bool bcpPropagate(const BcpEncoding*, const vector<const FixedBits*>&,
                  unsigned& fixed)
{
  fixed = 0;
  return true;
}

unsigned bcpVisibleFixed(const BcpEncoding*, const vector<const FixedBits*>&)
{
  return 0;
}

unsigned bcpClauses(const BcpEncoding*)
{
  return 0;
}

unsigned bcpVariables(const BcpEncoding*)
{
  return 0;
}

} // namespace propbench

#endif
