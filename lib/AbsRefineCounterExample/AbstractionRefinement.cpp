/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
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

#include "stp/AST/AST.h"
#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/AbsRefineCounterExample/ArrayReadRefinementProgress.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/STPManager/STPManager.h"
#include <cassert>
#include <math.h>

namespace stp
{
using std::pair;
using std::map;

void ArrayReadRefinementProgress::verifyStableBinding(
    const ASTNode& leaf,
    const ToSATBase::ASTNodeToSATVar& currentBindings)
{
  if (leaf.isConstant())
    return;

  ToSATBase::ASTNodeToSATVar::const_iterator current =
      currentBindings.find(leaf);
  if (current == currentBindings.end() ||
      current->second.size() != leaf.GetValueWidth())
    FatalError("Incremental array refinement has no stable SAT binding for "
               "an axiom leaf: ",
               leaf);
  for (size_t i = 0; i < current->second.size(); ++i)
    if (current->second[i] == ~((unsigned)0))
      FatalError("Incremental array refinement has an incomplete SAT binding "
                 "for an axiom leaf: ",
                 leaf);

  std::map<ASTNode, std::vector<unsigned>, ExprLess>::const_iterator prior =
      stableBindings.find(leaf);
  if (prior == stableBindings.end())
  {
    stableBindings.insert(std::make_pair(leaf, current->second));
    return;
  }
  if (prior->second != current->second)
    FatalError("Incremental array refinement changed an axiom leaf's SAT "
               "binding inside one check-sat: ",
               leaf);
}

bool ArrayReadRefinementProgress::claim(
    const ASTNode& index0, const ASTNode& index1, const ASTNode& value0,
    const ASTNode& value1,
    const ToSATBase::ASTNodeToSATVar& currentBindings)
{
  verifyStableBinding(index0, currentBindings);
  verifyStableBinding(index1, currentBindings);
  verifyStableBinding(value0, currentBindings);
  verifyStableBinding(value1, currentBindings);

  const AxiomKey key = {{index0, index1, value0, value1}};
  return emitted.insert(key).second;
}

/******************************************************************
 * Abstraction Refinement related functions
 ******************************************************************/

void getSatVariables(const ASTNode& a, vector<unsigned>& v_a,
                     SATSolver& SatSolver, ToSATBase::ASTNodeToSATVar& satVar)
{
  ToSATBase::ASTNodeToSATVar::iterator it = satVar.find(a);
  if (it != satVar.end())
  {
    v_a = it->second;

    // ToCNFAIG::fill_node_to_var() writes ~0u for a bit of a symbol that
    // reached no SAT variable, and the same value arrives from a CNF
    // generator that left an object's variable number at -1. getEquals()
    // indexes this vector straight into mkLit(), where the sentinel wraps
    // into a variable far past the solver's range: MiniSat then indexes
    // its assignment array out of bounds, and Cadical is handed a literal
    // beyond max_var.
    //
    // There is no safe recovery. Allocating a fresh variable for the
    // missing bit -- what the branch below does for a symbol that was
    // never bit-blasted at all -- would carry no connection to the term
    // the axiom is about, so the congruence clause could fail to rule out
    // the candidate model it was built from. The array-equality encoder
    // rejects the same shape for the same reason; see
    // ExtensionalityContext::checkPreencodedBV().
    for (size_t i = 0, size = v_a.size(); i < size; ++i)
      if (v_a[i] == ~((unsigned)0))
        FatalError("An array axiom leaf has a bit with no SAT variable: ", a);
  }
  else if (!a.isConstant())
  {
    assert(a.GetKind() == SYMBOL);
    // It was ommitted from the initial problem, so assign it freshly.
    for (unsigned i = 0; i < a.GetValueWidth(); i++)
    {
      uint32_t v = SatSolver.newVar();
      // We probably don't want the variable eliminated.
      SatSolver.setFrozen(v);
      v_a.push_back(v);
    }
    satVar.insert(make_pair(a, v_a));
  }
}

// This function adds the clauses to constrain that "a" and "b" equal a fresh
// variable
// (which it returns).
// Because it's used to create array axionms (a=b)-> (c=d), it can be
// used to only add one of the two polarities.
uint32_t getEquals(SATSolver& SatSolver, const ASTNode& a, const ASTNode& b,
                   ToSATBase::ASTNodeToSATVar& satVar, Polarity polary)
{
  const unsigned width = a.GetValueWidth();
  assert(width == b.GetValueWidth());

  vector<unsigned> v_a;
  vector<unsigned> v_b;

  getSatVariables(a, v_a, SatSolver, satVar);
  getSatVariables(b, v_b, SatSolver, satVar);

  // The only time v_a or v_b will be empty is if "a" resp. "b" is a constant.

  if (v_a.size() == width && v_b.size() == width)
  {
    SATSolver::vec_literals all;
    const int result = SatSolver.newVar();

    for (unsigned i = 0; i < width; i++)
    {
      SATSolver::vec_literals s;

      if (polary != Polarity::RIGHT_ONLY)
      {
        int nv0 = SatSolver.newVar();
        s.push(SATSolver::mkLit(v_a[i], true));
        s.push(SATSolver::mkLit(v_b[i], true));
        s.push(SATSolver::mkLit(nv0, false));
        SatSolver.addClause(s);
        s.clear();

        s.push(SATSolver::mkLit(v_a[i], false));
        s.push(SATSolver::mkLit(v_b[i], false));
        s.push(SATSolver::mkLit(nv0, false));
        SatSolver.addClause(s);
        s.clear();

        all.push(SATSolver::mkLit(nv0, true));
      }

      if (polary != Polarity::LEFT_ONLY)
      {
        s.push(SATSolver::mkLit(v_a[i], true));
        s.push(SATSolver::mkLit(v_b[i], false));
        s.push(SATSolver::mkLit(result, true));
        SatSolver.addClause(s);
        s.clear();

        s.push(SATSolver::mkLit(v_a[i], false));
        s.push(SATSolver::mkLit(v_b[i], true));
        s.push(SATSolver::mkLit(result, true));
        SatSolver.addClause(s);
        s.clear();
      }
    }
    if (all.size() > 0)
    {
      all.push(SATSolver::mkLit(result, false));
      SatSolver.addClause(all);
    }
    return result;
  }
  else if ((v_a.size() == 0) ^ (v_b.size() == 0))
  {
    ASTNode constant = a.isConstant() ? a : b;
    vector<unsigned> vec = v_a.size() == 0 ? v_b : v_a;
    assert(constant.isConstant());
    assert(vec.size() == width);

    SATSolver::vec_literals all;
    const int result = SatSolver.newVar();
    all.push(SATSolver::mkLit(result, false));

    CBV v = constant.GetBVConst();
    for (unsigned i = 0; i < width; i++)
    {
      if (polary != Polarity::RIGHT_ONLY)
      {
        if (CONSTANTBV::BitVector_bit_test(v, i))
          all.push(SATSolver::mkLit(vec[i], true));
        else
          all.push(SATSolver::mkLit(vec[i], false));
      }

      if (polary != Polarity::LEFT_ONLY)
      {
        SATSolver::vec_literals p;
        p.push(SATSolver::mkLit(result, true));
        if (CONSTANTBV::BitVector_bit_test(v, i))
          p.push(SATSolver::mkLit(vec[i], false));
        else
          p.push(SATSolver::mkLit(vec[i], true));

        SatSolver.addClause(p);
      }
    }
    if (all.size() > 1)
      SatSolver.addClause(all);
    return result;
  }
  else if (a.isConstant() && b.isConstant())
  {
    // A congruence axiom between two constant indexes (reachable when
    // both spell one value under different constant nodes -- a float
    // constant interns apart from the plain constant with its bits):
    // the equality's truth is just their bits; pin a fresh variable to
    // it.
    const int result = SatSolver.newVar();
    SATSolver::vec_literals unit;
    unit.push(SATSolver::mkLit(result, !constantsSameBits(a, b)));
    SatSolver.addClause(unit);
    return result;
  }
  else
  {
    FatalError("Unexpected, both must be constants..");
  }
}

/******************************************************************
 * ARRAY READ ABSTRACTION REFINEMENT
 *
 * SATBased_ArrayReadRefinement()
 *
 * What it really does is, for each array, loop over each index i.
 * inside that loop, it finds all the true and false axioms with i
 * as first index.  When it's got them all, it adds the false axioms
 * to the formula and re-solves, and returns if the result is
 * correct.  Otherwise, it goes on to the next index.
 *
 * If it gets through all the indices without a correct result
 * (which I think is impossible), it then solves with all the true
 * axioms, too.
 *
 * This is not the most obvious way to do it, and I don't know how
 * it compares with other approaches (e.g., one false axiom at a
 * time or all the false axioms each time).
 *****************************************************************/
struct AxiomToBe
{
  AxiomToBe(ASTNode i0, ASTNode i1, ASTNode v0, ASTNode v1)
  {
    index0 = i0;
    index1 = i1;
    value0 = v0;
    value1 = v1;
  }
  ASTNode index0, index1;
  ASTNode value0, value1;
};

void applyAxiomToSAT(SATSolver& SatSolver, AxiomToBe& toBe,
                     ToSATBase::ASTNodeToSATVar& satVar)
{
  uint32_t a = getEquals(SatSolver, toBe.index0, toBe.index1, satVar,
                         Polarity::LEFT_ONLY);
  uint32_t b = getEquals(SatSolver, toBe.value0, toBe.value1, satVar,
                         Polarity::RIGHT_ONLY);
  SATSolver::vec_literals satSolverClause;
  satSolverClause.push(SATSolver::mkLit(a, true));
  satSolverClause.push(SATSolver::mkLit(b, false));
  SatSolver.addClause(satSolverClause);
}

size_t applyAxiomsToSolver(ToSATBase::ASTNodeToSATVar& satVar,
                           vector<AxiomToBe>& toBe, SATSolver& SatSolver,
                           ArrayReadRefinementProgress* progress)
{
  // Preserve the batch path exactly: no memo allocation, node retention or
  // binding copies when the caller did not request transactional progress.
  if (progress == NULL)
  {
    const size_t emitted = toBe.size();
    for (size_t i = 0; i < toBe.size(); i++)
      applyAxiomToSAT(SatSolver, toBe[i], satVar);
    toBe.clear();
    return emitted;
  }

  size_t emitted = 0;
  for (size_t i = 0; i < toBe.size(); i++)
  {
    const AxiomToBe& a = toBe[i];
    if (!progress->claim(a.index0, a.index1, a.value0, a.value1, satVar))
      continue;
    applyAxiomToSAT(SatSolver, toBe[i], satVar);
    ++emitted;
  }
  toBe.clear();
  return emitted;
}

bool sortBySize(const pair<ASTNode, ArrayTransformer::arrTypeMap>& a,
                const pair<ASTNode, ArrayTransformer::arrTypeMap>& b)
{
  return a.second.size() < b.second.size();
}

bool sortByIndexConstants(const pair<ASTNode, ArrayTransformer::ArrayRead>& a,
                          const pair<ASTNode, ArrayTransformer::ArrayRead>& b)
{
  int aCount = ((a.second.index_symbol.isConstant()) ? 2 : 0) +
               (a.second.symbol.isConstant() ? 1 : 0);
  int bCount = ((b.second.index_symbol.isConstant()) ? 2 : 0) +
               (b.second.symbol.isConstant() ? 1 : 0);
  return aCount > bCount;
}

// Path lemmas for one round over the abstracted write-chain reads
// (ArrayTransformer::chainReads). A row's meaning is the first-match walk
// down its levels; the lemma for a match at level k is the clause
//
//   (i_1 = j) or ... or (i_{k-1} = j) or not(i_k = j) or (R = v_k)
//
// and the fall-through lemma replaces the final two literals with the
// base-read equality. Everything is stated over the anchors the transform
// bound, so the equalities encode directly against live SAT variables; a
// guard equality is used in both polarities across a row's clauses, so its
// comparison circuit is built once per row with Polarity::BOTH and reused.
// With emitAll false only the clause the current model violates is added
// (absent, or the model could not violate it); emitAll true adds a row's
// whole case split, which pins R completely.
size_t AbsRefine_CounterExample::emitChainReadLemmas(
    SATSolver& SatSolver, ToSATBase* tosat, bool emitAll,
    ArrayReadRefinementProgress* progress, ChainLemmaState* state)
{
  const ArrayTransformer::ChainReadsMap& chains = ArrayTransform->chainReads;
  if (chains.empty())
    return 0;

  ToSATBase::ASTNodeToSATVar& satVar = tosat->SATVar_to_SymbolIndexMap();
  size_t emitted = 0;

  for (ArrayTransformer::ChainReadsMap::const_iterator cit = chains.begin();
       cit != chains.end(); cit++)
  {
    for (ArrayTransformer::ChainIndexMap::const_iterator rit =
             cit->second.begin();
         rit != cit->second.end(); rit++)
    {
      const ArrayTransformer::ChainRow& row = rit->second;
      const size_t nLevels = row.levels.size();

      // The position the model resolves the read at: the first level whose
      // index matches, or nLevels for the fall-through.
      size_t resolved = nLevels;
      ASTNode expected;
      if (!emitAll)
      {
        const ASTNode jVal = TermToConstTermUsingModel(row.indexAnchor);
        for (size_t k = 0; k < nLevels; k++)
        {
          if (TermToConstTermUsingModel(row.levels[k].indexAnchor) == jVal)
          {
            resolved = k;
            expected = TermToConstTermUsingModel(row.levels[k].valueAnchor);
            break;
          }
        }
        if (resolved == nLevels)
        {
          if (row.baseReadSymbol.IsNull())
            continue; // a sure-hit tail: some level always matches
          expected = TermToConstTermUsingModel(row.baseReadSymbol);
        }
        if (TermToConstTermUsingModel(row.symbol) == expected)
          continue;
      }

      // Guard equality variables, cached across this check's rounds so a
      // deep row does not rebuild its comparison circuits every round.
      std::vector<int64_t>& guardVar = state->guards[row.symbol];
      if (guardVar.empty())
        guardVar.assign(nLevels, -1);
      const auto guard = [&](size_t m) {
        if (guardVar[m] < 0)
          guardVar[m] = getEquals(SatSolver, row.levels[m].indexAnchor,
                                  row.indexAnchor, satVar, Polarity::BOTH);
        return (uint32_t)guardVar[m];
      };

      const auto emitAt = [&](size_t k) {
        // Claimed under a key no congruence axiom can produce: the chain
        // read's own symbol leads it.
        const ASTNode& valueSide =
            (k < nLevels) ? row.levels[k].valueAnchor : row.baseReadSymbol;
        if (progress != NULL &&
            !progress->claim(row.symbol,
                             (k < nLevels) ? row.levels[k].indexAnchor
                                           : row.indexAnchor,
                             valueSide, row.symbol, satVar))
          return;
        SATSolver::vec_literals clause;
        for (size_t m = 0; m < k && m < nLevels; m++)
          clause.push(SATSolver::mkLit(guard(m), false));
        if (k < nLevels)
          clause.push(SATSolver::mkLit(guard(k), true));
        const uint32_t valueEq = getEquals(SatSolver, row.symbol, valueSide,
                                           satVar, Polarity::RIGHT_ONLY);
        clause.push(SATSolver::mkLit(valueEq, false));
        SatSolver.addClause(clause);
        emitted++;
      };

      // The whole prefix up to the resolution point is emitted at once: a
      // later round can then only be violated deeper (or at the model's
      // next resolution point), so a row's rounds are bounded by how deep
      // the models actually reach, not by one level per round.
      size_t& frontier = state->frontiers[row.symbol];
      const size_t last = emitAll ? nLevels : resolved;
      for (size_t k = frontier; k <= last && k < nLevels; k++)
        emitAt(k);
      if (last == nLevels && !row.baseReadSymbol.IsNull())
        emitAt(nLevels);
      if (last + 1 > frontier)
        frontier = last + 1;
    }
  }
  return emitted;
}

SOLVER_RETURN_TYPE
AbsRefine_CounterExample::SATBased_ArrayReadRefinement(
    SATSolver& SatSolver, const ASTNode& original_input, ToSATBase* tosat,
    ArrayReadRefinementProgress* progress)
{
  vector<AxiomToBe> RemainingAxiomsVec;
  vector<AxiomToBe> FalseAxiomsVec;
  // NB. Because we stop this timer before entering the SAT solver, the count
  // it produces isn't the number of times Array Read Refinement was entered.
  bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
  /// Check the arrays with the least indexes first.

  vector<pair<ASTNode, ArrayTransformer::arrTypeMap>> arrayToIndex;
  arrayToIndex.insert(arrayToIndex.begin(),
                      ArrayTransform->arrayToIndexToRead.begin(),
                      ArrayTransform->arrayToIndexToRead.end());
  sort(arrayToIndex.begin(), arrayToIndex.end(), sortBySize);

  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  const bool extActive = ext != NULL && ext->activeInSolve();
  if (extActive)
    FatalError("array-equality: legacy array-read refinement was invoked "
               "during a solve owned by the extensionality checker");

  // The abstracted write-chain reads first: each round adds the one path
  // lemma per row that the current model violates, and the loop runs the
  // rows dry before the congruence axioms below are considered.
  ChainLemmaState chainState;
  for (;;)
  {
    const size_t chainEmitted =
        emitChainReadLemmas(SatSolver, tosat, false, progress, &chainState);
    if (chainEmitted == 0)
      break;
    bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
    const SOLVER_RETURN_TYPE res2 = CallSAT_ResultCheck(
        SatSolver, ASTTrue, original_input, original_input, tosat, true);
    if (SOLVER_UNDECIDED != res2)
      return res2;
    bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
  }

  // In these loops we try to construct Leibnitz axioms and add it to
  // the solve(). We add only those axioms that are false in the
  // current counterexample. we keep adding the axioms until there
  // are no more axioms to add
  //
  // for each array, fetch its list of indices seen so far
  for (vector<pair<ASTNode, ArrayTransformer::arrTypeMap>>::const_iterator
           iset = arrayToIndex.begin(),
           iset_end = arrayToIndex.end();
       iset != iset_end; iset++)
  {
    const map<ASTNode, ArrayTransformer::ArrayRead>& mapper = iset->second;

    vector<ASTNode> listOfIndices;
    listOfIndices.reserve(mapper.size());

    // Make a vector of the read symbols.
    ASTVec read_node_symbols;
    read_node_symbols.reserve(listOfIndices.size());

    vector<Kind> jKind;
    jKind.reserve(mapper.size());

    vector<ASTNode> concreteIndexes;
    concreteIndexes.reserve(mapper.size());

    vector<ASTNode> concreteValues;
    concreteValues.reserve(mapper.size());

    ASTVec index_symbols;

    vector<pair<ASTNode, ArrayTransformer::ArrayRead>> indexToRead;
    indexToRead.insert(indexToRead.begin(), mapper.begin(), mapper.end());
    sort(indexToRead.begin(), indexToRead.end(), sortByIndexConstants);

    for (vector<pair<ASTNode, ArrayTransformer::ArrayRead>>::const_iterator it =
             indexToRead.begin();
         it != indexToRead.end(); it++)
    {
      const ASTNode& the_index = it->first;
      listOfIndices.push_back(the_index);

      ASTNode arrsym = it->second.symbol;
      read_node_symbols.push_back(arrsym);

      index_symbols.push_back(it->second.index_symbol);

      assert(read_node_symbols[0].GetValueWidth() == arrsym.GetValueWidth());
      assert(listOfIndices[0].GetValueWidth() == the_index.GetValueWidth());

      jKind.push_back(the_index.GetKind());

      concreteIndexes.push_back(TermToConstTermUsingModel(the_index));
      concreteValues.push_back(TermToConstTermUsingModel(arrsym));
    }

    assert(listOfIndices.size() == mapper.size());

    // loop over the list of indices for the array and create LA,
    // and add to inputAlreadyInSAT
    for (size_t i = 0; i < listOfIndices.size(); i++)
    {
      const ASTNode& index_i = listOfIndices[i];
      const Kind iKind = index_i.GetKind();

      // Create all distinct pairs of indexes.
      for (size_t j = i + 1; j < listOfIndices.size(); j++)
      {
        const ASTNode& index_j = listOfIndices[j];

        // If the indexes are constants of different values, the cells are
        // distinct and no congruence is needed. Compare bits, not nodes:
        // a float constant interns apart from the plain constant with its
        // bits, and skipping such a pair drops a needed axiom for good.
        if (BVCONST == iKind && jKind[j] == BVCONST &&
            constantsDenoteDifferentValues(index_i, index_j))
          continue;

        if (ASTFalse == simp->CreateSimplifiedEQ(index_i, index_j))
          continue; // shortcut.

        AxiomToBe o(index_symbols[i], index_symbols[j], read_node_symbols[i],
                    read_node_symbols[j]);

        if (concreteIndexes[i] == concreteIndexes[j] &&
            concreteValues[i] != concreteValues[j])
        {
          FalseAxiomsVec.push_back(o);
          // ToSATBase::ASTNodeToSATVar	& satVar =
          // tosat->SATVar_to_SymbolIndexMap();
          // applyAxiomsToSolver(satVar, FalseAxiomsVec, SatSolver);
        }
        else
          RemainingAxiomsVec.push_back(o);
      }
      if (FalseAxiomsVec.size() > 0)
      {
        ToSATBase::ASTNodeToSATVar& satVar = tosat->SATVar_to_SymbolIndexMap();
        const size_t emitted = applyAxiomsToSolver(
            satVar, FalseAxiomsVec, SatSolver, progress);

        if (emitted > 0)
        {
          SOLVER_RETURN_TYPE res2;
          bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
          res2 = CallSAT_ResultCheck(SatSolver, ASTTrue, original_input,
                                     original_input, tosat, true);

          if (SOLVER_UNDECIDED != res2)
            return res2;
          bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
        }
      }
    }
  }
  if (RemainingAxiomsVec.size() > 0 || !ArrayTransform->chainReads.empty())
  {
    if (bm->UserFlags.stats_flag)
    {
      std::cout << "Adding all the remaining " << RemainingAxiomsVec.size()
                << " read axioms " << std::endl;
    }
    ToSATBase::ASTNodeToSATVar& satVar = tosat->SATVar_to_SymbolIndexMap();
    size_t emitted = applyAxiomsToSolver(
        satVar, RemainingAxiomsVec, SatSolver, progress);
    // The model-guided rounds above ran the rows dry against one model;
    // adding every remaining path lemma pins the chain reads completely,
    // so the final call cannot come back undecided for their sake.
    emitted += emitChainReadLemmas(SatSolver, tosat, true, progress,
                                   &chainState);

    bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
    if (emitted > 0)
      return CallSAT_ResultCheck(SatSolver, ASTTrue, original_input,
                                 original_input, tosat, true);
    return SOLVER_UNDECIDED;
  }

  bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
  return SOLVER_UNDECIDED;
}

} // end of namespace stp
