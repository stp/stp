/********************************************************************
 * AUTHORS: Vijay Ganesh
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

#include "stp/AbsRefineCounterExample/AbsRefine_CounterExample.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/FloatBlaster/FloatBlast.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/FpEncodingContext.h"
#include "stp/Printer/printers.h"
#include "stp/ToSat/ToSATAIG.h"
#include <memory>

const bool debug_counterexample = false;

namespace stp
{
using std::cout;

// Whether `n` is an access over an array whose declared index sort is
// floating-point -- the question FpTotalise::visit asks before canonicalising
// an index, asked here in the same terms.
//
// Deliberately says nothing about *this* node's own index. A constant index is
// already canonical, so an access carrying one may well need no rewrite; but
// "needs no rewrite" is a property of the whole access, not of its index, and
// only the encoding pass can decide it. A READ over a WRITE has the write's
// index to canonicalise however constant the read's index is, and short-
// circuiting on the read's kind sent exactly that shape down the raw-carrier
// path below, where a float symbol resolves to whichever NaN payload the SAT
// solver picked while the solve compared pack(unpack(x)).
//
// The caller already handles the no-rewrite case: encodeForModel returns the
// node unchanged, and the `encoded != term` test falls through. So the gate is
// the sort question and nothing else.
static bool isFpIndexedArrayAccess(const ASTNode& n)
{
  if ((n.GetKind() != READ && n.GetKind() != WRITE) || n.Degree() < 2)
    return false;

  const SourceSort array_sort = n[0].GetSourceSort();
  return array_sort.kind() == SourceSort::Kind::Array &&
         array_sort.index().kind() == SourceSort::Kind::FloatingPoint;
}

static ASTNode plainModelCarrier(STPMgr* bm, const ASTNode& value)
{
  // The plain twin of a source-sorted carrier constant: same bits, the
  // flavour every identity comparison in model evaluation expects.  SAT
  // model constants are plain bit-vectors, so retaining FloatingPoint or
  // RoundingMode decoration here would make equal carrier values distinct
  // interned AST nodes.
  const SourceSort::Kind sort = value.GetSourceSort().kind();
  if (value.GetKind() == BVCONST &&
      (value.GetExpWidth() != 0 || sort == SourceSort::Kind::RoundingMode))
    return bm->CreateBVConst(CONSTANTBV::BitVector_Clone(value.GetBVConst()),
                             value.GetValueWidth());
  return value;
}

class ScopedFpEncodedEvaluation final
{
public:
  explicit ScopedFpEncodedEvaluation(unsigned int& depth_) : depth(depth_)
  {
    ++depth;
  }

  ~ScopedFpEncodedEvaluation()
  {
    assert(depth > 0);
    --depth;
  }

private:
  unsigned int& depth;
};

FpEncodingContext&
AbsRefine_CounterExample::requireFpEncodingContext() const
{
  if (fpEncodingContext == NULL)
    FatalError("floating-point model evaluation has no solve encoding "
               "context");
  return *fpEncodingContext;
}

/*FUNCTION: constructs counterexample from MINISAT counterexample
 * step1 : iterate through MINISAT counterexample and assemble the
 * bits for each AST term. Store it in a map from ASTNode to vector
 * of bools (bits).
 *
 * step2: Iterate over the map from ASTNodes->Vector-of-Bools and
 * populate the CounterExampleMap data structure (ASTNode -> BVConst)
 */
void AbsRefine_CounterExample::ConstructCounterExample(
    SATSolver& newS, ToSATBase::ASTNodeToSATVar& satVarToSymbol)
{
  if (!newS.okay())
    return;
  if (!bm->UserFlags.construct_counterexample_flag)
    return;

  assert(CounterExampleMap.size() == 0);

  CopySolverMap_To_CounterExample();

  for (ToSATBase::ASTNodeToSATVar::const_iterator it = satVarToSymbol.begin();
       it != satVarToSymbol.end(); it++)
  {
    const ASTNode& symbol = it->first;
    const vector<unsigned>& v = it->second;

    const unsigned int symbolWidth = symbol.GetValueWidth();
    assert(symbol.GetKind() == SYMBOL);
    vector<bool> bitVector_array(symbolWidth, false);

    for (size_t index = 0; index < v.size(); index++)
    {
      const unsigned sat_variable_index = v[index];

      if (sat_variable_index == ~((unsigned)0)) // not sent to the sat solver.
        continue;

      if (newS.modelValue(sat_variable_index) == newS.undef_literal())
        continue;

      // assemble the counterexample here
      if (symbol.GetType() == BITVECTOR_TYPE ||
          symbol.GetType() == FLOATINGPOINT_TYPE)
      {
        // Collect the bits of 'symbol' and store in v. Store
        // in reverse order.
        bitVector_array[(symbolWidth - 1) - index] =
            (newS.modelValue(sat_variable_index) == newS.true_literal());
      }
      else
      {
        assert(symbol.GetType() == BOOLEAN_TYPE);
        if (newS.modelValue(sat_variable_index) == newS.true_literal())
          CounterExampleMap[symbol] = ASTTrue;
        else if (newS.modelValue(sat_variable_index) == newS.false_literal())
          CounterExampleMap[symbol] = ASTFalse;
        else
          FatalError("never heres.");
      }
    }

    if (symbol.GetType() == BITVECTOR_TYPE ||
        symbol.GetType() == FLOATINGPOINT_TYPE)
    {
      CounterExampleMap[symbol] =
          BoolVectoBVConst(&bitVector_array, symbol.GetValueWidth());
    }
  }

  // In an active array-equality solve the consistency checker owns the
  // complete array graph. Its input is the scalar SAT assignment above;
  // do not pre-populate concrete READ(array, value(index)) entries here.
  // Two syntactically different indexes can have the same candidate value,
  // and collapsing their read abstractions into one map key before rule C
  // runs loses exactly the disagreement the checker must turn into a lemma.
  // A conflict-free check publishes one validated observation batch later.
  {
    ExtensionalityContext* ext = bm->getExtensionalityIfAny();
    if (ext != NULL && ext->active())
    {
      if (!ext->checkerReady())
        FatalError("array-equality: a SAT candidate was materialized before "
                   "the complete array graph was bound");
      // SAT backends may leave a don't-care Boolean literal undefined.
      // Complete such directly encoded symbols with false, just as the BV
      // loop above completes undefined bits with zero. Preserve any concrete
      // value copied from the solver map.
      for (ToSATBase::ASTNodeToSATVar::const_iterator it =
               satVarToSymbol.begin();
           it != satVarToSymbol.end(); ++it)
      {
        const ASTNode& symbol = it->first;
        if (symbol.GetType() != BOOLEAN_TYPE)
          continue;
        ASTNodeMap::const_iterator assigned = CounterExampleMap.find(symbol);
        if (assigned == CounterExampleMap.end())
          CounterExampleMap[symbol] = ASTFalse;
        else if (ext->isProtected(symbol) &&
                 !(assigned->second.GetKind() == TRUE ||
                   assigned->second.GetKind() == FALSE))
          FatalError("array-equality: a protected Boolean SAT name has a "
                     "non-Boolean counterexample value",
                     symbol);
      }

      for (ASTNodeMap::const_iterator it = CounterExampleMap.begin();
           it != CounterExampleMap.end(); ++it)
        if (it->first.GetKind() == READ)
          FatalError("array-equality: preprocessing placed an array-read "
                     "observation in the candidate before the complete "
                     "graph was checked",
                     it->first);
      return;
    }
  }

  for (ArrayTransformer::ArrType::const_iterator
           it = ArrayTransform->arrayToIndexToRead.begin(),
           itend = ArrayTransform->arrayToIndexToRead.end();
       it != itend; it++)
  {
    const ASTNode& array = it->first;
    const std::map<ASTNode, ArrayTransformer::ArrayRead>& mapper = it->second;

    for (std::map<ASTNode, ArrayTransformer::ArrayRead>::const_iterator
             it2 = mapper.begin(),
             it2end = mapper.end();
         it2 != it2end; it2++)
    {
      const ASTNode& index = it2->first;
      const ASTNode& value_ite = it2->second.ite;

      // convert it to a constant array-read and store it in the
      // counter-example. First convert the index into a constant. then
      // construct the appropriate array-read and store it in the
      // counterexample
      ASTNode arrayread_index = TermToConstTermUsingModel(index, false);
      ASTNode key = bm->defaultNodeFactory->CreateTerm(
          READ, array.GetValueWidth(), array, arrayread_index);

      // Get the ITE corresponding to the array-read and convert it
      // to a constant against the model
      ASTNode value = TermToConstTermUsingModel(value_ite);
      // save the result in the counter_example
      // As in TermToConstTermUsingModel: never record a read as its own value.
      if (!simp->InsideSubstitutionMap(key) && key != value)
        CounterExampleMap[key] = value;
    }
  }
}

// FUNCTION: accepts a non-constant term, and returns the
// corresponding constant term with respect to a model.
//
// term READ(A,i) is treated as follows:
//
// 1. If (the boolean variable 'ArrayReadFlag' is true && ArrayRead
// 1. has value in counterexample), then return the value of the
// 1. arrayread.
//
// 2. If (the boolean variable 'ArrayReadFlag' is true && ArrayRead
// 2. doesn't have value in counterexample), then return the
// 2. arrayread itself (normalized such that arrayread has a constant
// 2. index)
//
// 3. If (the boolean variable 'ArrayReadFlag' is false) && ArrayRead
// 3. has a value in the counterexample then return the value of the
// 3. arrayread.
//
// 4. If (the boolean variable 'ArrayReadFlag' is false) && ArrayRead
// 4. doesn't have a value in the counterexample then complete it with an
// 4. arbitrary concrete value. RoundingMode reads use RNE, because junk
// 4. patterns in their 5-bit carrier are not values of that sort.
ASTNode AbsRefine_CounterExample::TermToConstTermUsingModel(const ASTNode& term,
                                                            bool ArrayReadFlag)
{
  return plainModelCarrier(
      bm, TermToConstTermUsingModel_inner(term, ArrayReadFlag));
}

ASTNode
AbsRefine_CounterExample::TermToConstTermUsingModel_inner(const ASTNode& term,
                                                          bool ArrayReadFlag)
{
  if (term.GetKind() == BVCONST)
    return term;

  const Kind k = term.GetKind();

  assert(is_Term_kind(k));
  assert(k != WRITE);
  assert(BOOLEAN_TYPE != term.GetType());

  // An array-typed entry is a definitional alias installed by equality
  // propagation (array symbol := array term), not a value; the READ case
  // resolves through it. Recursing on it here would hand an array term to
  // a walk that only understands element-typed values.
  ASTNodeMap::const_iterator it1;
  if (ARRAY_TYPE != term.GetType() &&
      (it1 = CounterExampleMap.find(term)) != CounterExampleMap.end())
  {
    // A copy, never a reference into the map: the recursion below can reach
    // an array equality, whose ModelQuery guard rolls CounterExampleMap back
    // by whole-map assignment -- freeing every node, including the one a
    // reference here would still be aliasing when the recursion returns.
    const ASTNode val = it1->second;
    if (BVCONST != val.GetKind())
    {
      // CounterExampleMap has two maps rolled into
      // one. SubstitutionMap and SolverMap.
      //
      // recursion is fine here. There are two maps that are checked
      // here. One is the substitutionmap. We garuntee that the value
      // of a key in the substitutionmap is always a constant.
      //
      // in the SolverMap we garuntee that "term" does not occur in
      // the value part of the map
      if (term == val)
      {
        FatalError("TermToConstTermUsingModel: "
                   "The input term is stored as-is "
                   "in the CounterExample: Not ok: ",
                   term);
      }
      return TermToConstTermUsingModel(val, ArrayReadFlag);
    }
    else
    {
      return val;
    }
  }

  // FP source operations are evaluated through the solve-owned lowering
  // context. This is deliberately before the target-language switch below:
  // counterexample evaluation must not maintain a second implementation of
  // totalisation, operand reconstruction, and SymFPU lowering.
  if (fpEncodedEvaluationDepth == 0 &&
      (is_FP_kind(k) || isFpIndexedArrayAccess(term)))
  {
    const ASTNode encoded =
        requireFpEncodingContext().encodeForModel(term);
    if (encoded == term && is_FP_kind(k))
      FatalError("floating-point model encoding made no progress: ", term);

    // The invariant this arm exists to hold: *a float's model value is its
    // canonical carrier*. A float symbol's raw model bits are whichever NaN
    // payload the SAT solver happened to pick, and the solve compared
    // pack(unpack(x)); the two agree on everything except the payload, which
    // is exactly what an array index distinguishes. So any node the encoding
    // pass rewrote must be evaluated through that rewrite and never through
    // its raw bits.
    //
    // Whether a rewrite was needed is the pass's answer to give, not ours:
    // an access whose indexes are all already canonical comes back unchanged
    // and falls through to the ordinary switch below.
    if (encoded != term)
    {
      // The lowered DAG retains source-sort metadata on carrier reads and
      // leaves. Keep the entire recursive evaluation in target mode so a
      // nested read-over-write cannot mistake that metadata for a fresh
      // source boundary and canonicalise it repeatedly.
      const ScopedFpEncodedEvaluation evaluating(fpEncodedEvaluationDepth);
      const ASTNode value =
          TermToConstTermUsingModel(encoded, ArrayReadFlag);
      if (term != value)
        CounterExampleMap[term] = value;
      return value;
    }
  }

  ASTNode output;
  switch (k)
  {
    case BVCONST:
      output = term;
      break;
    case SYMBOL:
    {
      if (term.GetType() == ARRAY_TYPE)
      {
        return term;
      }
      else
      {
        // Has been simplified out and can take any value. A RoundingMode's
        // 5-bit representation has 27 junk patterns, though, so complete that
        // sort with a real value rather than the ordinary all-zero default.
        output = bm->isRoundingModeSortedTerm(term)
                     ? bm->CreateBVConst(
                           5, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN)
                     : bm->CreateZeroConst(term.GetValueWidth());
      }
      break;
    }
    case READ:
    {
      ASTNode arrName = term[0];
      ASTNode index = term[1];
      if (0 == arrName.GetIndexWidth())
      {
        FatalError("TermToConstTermUsingModel: "
                   "array has 0 index width: ",
                   arrName);
      }

      // An array symbol that equality propagation substituted away is
      // defined by its (array-typed) entry in the counterexample map --
      // the copied-in substitution map. The solve never bit-blasted a
      // read of the vanished symbol, so no model entry can be keyed on
      // it; read through the definition instead.
      if (SYMBOL == arrName.GetKind())
      {
        ASTNodeMap::const_iterator sub = CounterExampleMap.find(arrName);
        if (sub != CounterExampleMap.end() &&
            ARRAY_TYPE == sub->second.GetType())
        {
          const ASTNode throughDefinition = bm->CreateTerm(
              READ, term.GetValueWidth(), sub->second, index);
          return TermToConstTermUsingModel(throughDefinition, ArrayReadFlag);
        }
      }

      // With array equality active, every read in the solve is
      // evaluated through its read-abstraction variable -- never by
      // expanding its write chain against the model. The consistency
      // checker, not the model-side expander, is the authority for
      // these reads: the abstraction variable holds whatever the SAT
      // solver assigned, and any disagreement with the array axioms is
      // exactly what the checker turns into a lemma.
      //
      // An owned read with no recorded abstraction variable was
      // simplified out of the formula before solving; it is evaluated
      // from the certified array contents instead: the recorded
      // observation at the concrete index if one exists at this level,
      // else the concrete write-hit value, else recurse into the base
      // array, defaulting to zero. This agrees with every recorded
      // access whenever the checker certifies the candidate.
      {
        ExtensionalityContext* ext = bm->getExtensionalityIfAny();
        if (ext != NULL && ext->active() && ext->arrayGraphFrozen() &&
            ext->ownsArray(arrName))
        {
          const ASTNode idxVal = TermToConstTermUsingModel(index, false);
          NodeFactory* hf = bm->hashingNodeFactory;
          ASTNode level = arrName;
          ASTNode val;
          while (true)
          {
            const ASTNode key = hf->CreateTerm(READ, level.GetValueWidth(),
                                               level, idxVal);
            ASTNodeMap::const_iterator cit = CounterExampleMap.find(key);
            if (cit != CounterExampleMap.end())
            {
              val = cit->second;
              if (BVCONST != val.GetKind())
                val = TermToConstTermUsingModel(val, false);
              break;
            }
            if (WRITE == level.GetKind())
            {
              const ASTNode writeIdx = TermToConstTermUsingModel(level[1],
                                                                 false);
              if (writeIdx == idxVal)
              {
                val = TermToConstTermUsingModel(level[2], false);
                break;
              }
              level = level[0];
              continue;
            }
            if (ITE == level.GetKind() && level.GetType() == ARRAY_TYPE)
            {
              const ASTNode cond = ComputeFormulaUsingModel(level[0]);
              if (cond == ASTTrue)
                level = level[1];
              else if (cond == ASTFalse)
                level = level[2];
              else
                FatalError("array-equality: an owned array if-then-else "
                           "condition has no concrete model value",
                           level[0]);
              continue;
            }
            // base array with no observation
            val = defaultCellValue(level);
            break;
          }
          CounterExampleMap[term] = val;
          return val;
        }
      }

      if (WRITE == arrName.GetKind()) // READ over a WRITE
      {
        ASTNode wrtterm = Expand_ReadOverWrite_UsingModel(term, ArrayReadFlag);
        if (wrtterm == term)
        {
          FatalError("TermToConstTermUsingModel: "
                     "Read_Over_Write term must be expanded "
                     "into an ITE",
                     term);
        }
        ASTNode rtterm = TermToConstTermUsingModel(wrtterm, ArrayReadFlag);
        assert(ArrayReadFlag || (BVCONST == rtterm.GetKind()));
        return rtterm;
      }
      else if (ITE == arrName.GetKind()) // READ over an ITE
      {
        // The "then" and "else" branch are arrays.
        ASTNode indexVal = TermToConstTermUsingModel(index, ArrayReadFlag);

        ASTNode condcompute =
            ComputeFormulaUsingModel(arrName[0]); // Get the truth value.
        unsigned int wid = arrName.GetValueWidth();
        if (ASTTrue == condcompute)
        {
          const ASTNode& result = TermToConstTermUsingModel(
              bm->CreateTerm(READ, wid, arrName[1], indexVal), ArrayReadFlag);
          assert(ArrayReadFlag || (BVCONST == result.GetKind()));
          return result;
        }
        else if (ASTFalse == condcompute)
        {
          const ASTNode& result = TermToConstTermUsingModel(
              bm->CreateTerm(READ, wid, arrName[2], indexVal), ArrayReadFlag);
          assert(ArrayReadFlag || (BVCONST == result.GetKind()));
          return result;
        }
        else
        {
          FatalError(" TermToConstTermUsingModel: termITE: "
                     "cannot compute ITE conditional against model: ",
                     term);
        }
      }

      ASTNode modelentry;
      if (CounterExampleMap.find(index) != CounterExampleMap.end())
      {
        // index has a const value in the CounterExampleMap. Copied out of the
        // map for the reason given at the lookup at the top of this function.
        const ASTNode indexEntry = CounterExampleMap[index];
        ASTNode indexVal = TermToConstTermUsingModel(indexEntry, ArrayReadFlag);
        modelentry =
            bm->CreateTerm(READ, arrName.GetValueWidth(), arrName, indexVal);
      }
      else
      {
        // index does not have a const value in the
        // CounterExampleMap. compute it.
        ASTNode indexconstval = TermToConstTermUsingModel(index, ArrayReadFlag);
        // update model with value of the index
        // CounterExampleMap[index] = indexconstval;
        modelentry = bm->CreateTerm(READ, arrName.GetValueWidth(), arrName,
                                    indexconstval);
      }
      // modelentry is now an arrayread over a constant index
      BVTypeCheck(modelentry);

      // if a value exists in the CounterExampleMap then return it. Copied out
      // of the map for the reason given at the lookup at the top of this
      // function.
      if (CounterExampleMap.find(modelentry) != CounterExampleMap.end())
      {
        const ASTNode modelentryValue = CounterExampleMap[modelentry];
        output = TermToConstTermUsingModel(modelentryValue, ArrayReadFlag);
      }
      else if (ArrayReadFlag)
      {
        // return the array read over a constantindex
        output = modelentry;
      }
      else if (bm->UserFlags.enable_array_equality)
      {
        // Has been simplified out, so any value will do -- but only one
        // value agrees with the model that is published. With array
        // equality enabled the model surface prints a total
        // interpretation per array, and this is a cell of it that no
        // observation covers, so it is the completion or nothing.
        // Inventing something else makes evaluation disagree with every
        // other reader: an array equality evaluates false through its
        // lowering's reads while the printed arrays are identical, which
        // is the disagreement the post-solve audit trips on -- and,
        // unaudited, a (get-model) that falsifies the query it answered
        // sat. Both of this arm's former answers were such an invention:
        // all-ones for a bitvector cell the printer filled with zero,
        // and RNE for a RoundingMode cell that ReadUsingModel and the
        // checker were still completing with all-zero bits.
        //
        // Memoising the invented value instead cannot close that gap.
        // Model queries run inside a scope that restores the
        // counterexample map afterwards, so the entry is rolled back
        // and the next reader invents the value again against a model
        // that never recorded it. Agreeing with the completion the rest
        // of the model already uses needs no bookkeeping at all.
        //
        // Gated on the option: with it off the counterexample map, and
        // so vc_getCounterExampleArray, must stay exactly as before.
        output = defaultCellValue(arrName);
      }
      else
      {
        // Has been simplified out and can take any value. Keep the historical
        // all-one completion for ordinary bitvectors, but not for
        // RoundingMode: 0b11111 is not one of that sort's five values and can
        // make SymFPU exhibit a non-IEEE sixth rounding behaviour.
        output = bm->isRoundingModeSortedTerm(modelentry)
                     ? bm->CreateBVConst(
                           5, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN)
                     : bm->CreateMaxConst(modelentry.GetValueWidth());
      }
      break;
    }
    case ITE:
    {
      ASTNode condcompute = ComputeFormulaUsingModel(term[0]);
      if (ASTTrue == condcompute)
      {
        output = TermToConstTermUsingModel(term[1], ArrayReadFlag);
      }
      else if (ASTFalse == condcompute)
      {
        output = TermToConstTermUsingModel(term[2], ArrayReadFlag);
      }
      else
      {
        FatalError(" TermToConstTermUsingModel: termITE: cannot "
                   "compute ITE conditional against model: ",
                   term);
      }
      break;
    }
    default:
    {
      const ASTChildren c = term.GetChildren();
      ASTVec o;
      o.reserve(c.size());
      for (auto it = c.begin(), itend = c.end(); it != itend;
           it++)
      {
        ASTNode ff = TermToConstTermUsingModel(*it, ArrayReadFlag);
        // NonMemberBVConstEvaluator below needs every child to be a constant.
        // With ArrayReadFlag set, a read with no value in the model comes back
        // as a symbolic READ over the array (case 2 above) rather than a
        // constant -- this happens for the unconstrained array that totalising
        // introduces for an out-of-range to_ubv/to_sbv, reached here when the
        // enclosing ITE selects the unspecified branch and it feeds an ordinary
        // bit-vector operation. Its value is genuinely arbitrary, so resolve it
        // to a concrete constant rather than hand a non-constant to the
        // evaluator (which cannot read arrays and would abort on the array
        // symbol).
        if (BVCONST != ff.GetKind())
          ff = TermToConstTermUsingModel(*it, false);
        // A floating-point operand comes back as a bare bit-vector:
        // TermToConstTermUsingModel strips the format off every result it
        // returns. NonMemberBVConstEvaluator lowers through FloatBlast,
        // which reads each operand's format off its source sort, so restore
        // each float operand's own format here -- the same reattachment the
        // FP-predicate arm of ComputeFormulaUsingModel makes before rebuilding
        // a predicate. Non-float operands (bit-vectors, rounding modes) keep
        // their bare form.
        if (it->GetType() == FLOATINGPOINT_TYPE)
          ff = FloatBlaster::withFormat(bm, ff, it->GetExpWidth(),
                                        it->GetSigWidth());
        o.push_back(ff);
      }

      output = NonMemberBVConstEvaluator(bm, k, o, term.GetValueWidth());
      break;
    }
  }

  assert(ArrayReadFlag || (BVCONST == output.GetKind()));

  // when this flag is false, we should compute the arrayread to a
  // constant. this constant is stored in the counter_example
  // datastructure
  // if (!ArrayReadFlag)
  {
    // Don't memoise a read as its own value. With ArrayReadFlag true, a read
    // with no value in the model is returned unchanged (case 2 above) -- this
    // happens for an unconstrained read, such as the array that totalising
    // introduces for an out-of-range to_ubv/to_sbv. Caching term -> term would
    // put the term in its own value slot, violating the invariant the lookups
    // rely on: a later lookup then trips the "stored as-is" fatal error, or
    // leaves the read unresolved and non-constant. Skipping the self-entry lets
    // that later lookup fall through to the documented arbitrary completion.
    if (term != output)
      CounterExampleMap[term] = output;
  }

  // cerr << "Output to TermToConstTermUsingModel: " << output << endl;
  return output;
}

// Expands read-over-write by evaluating (readIndex=writeIndex) for
// every writeindex until, either it evaluates to TRUE or all
//(readIndex=writeIndex) evaluate to FALSE
ASTNode
AbsRefine_CounterExample::Expand_ReadOverWrite_UsingModel(const ASTNode& term,
                                                          bool arrayread_flag)
{
  if (READ != term.GetKind() || WRITE != term[0].GetKind())
  {
    FatalError("RemovesWrites: Input must be a READ over a WRITE", term);
  }

  ASTNode output;
  ASTNodeMap::iterator it1;
  if ((it1 = CounterExampleMap.find(term)) != CounterExampleMap.end())
  {
    // Copied out of the map for the reason given at the lookup at the top of
    // TermToConstTermUsingModel_inner.
    const ASTNode val = it1->second;
    if (BVCONST != val.GetKind())
    {
      // recursion is fine here. There are two maps that are checked
      // here. One is the substitutionmap. We garuntee that the value
      // of a key in the substitutionmap is always a constant.
      if (term == val)
      {
        FatalError("TermToConstTermUsingModel: The input term is "
                   "stored as-is "
                   "in the CounterExample: Not ok: ",
                   term);
      }
      return TermToConstTermUsingModel(val, arrayread_flag);
    }
    else
    {
      return val;
    }
  }

  ASTNode newRead = term;
  const ASTNode readIndex = TermToConstTermUsingModel(newRead[1], false);
  // iteratively expand read-over-write, and evaluate against the
  // model at every iteration
  ASTNode write = newRead[0];
  do
  {
    ASTNode writeIndex = TermToConstTermUsingModel(write[1], false);

    if (writeIndex == readIndex)
    {
      // found the write-value. return it
      output = TermToConstTermUsingModel(write[2], false);
      CounterExampleMap[term] = output;
      return output;
    }

    write = write[0];
  } while (WRITE == write.GetKind());

  const unsigned int width = term.GetValueWidth();
  newRead = bm->CreateTerm(READ, width, write, readIndex);
  output = TermToConstTermUsingModel(newRead, arrayread_flag);

  // memoize
  CounterExampleMap[term] = output;
  return output;
} // Expand_ReadOverWrite_UsingModel()

/* FUNCTION: accepts a non-constant formula, and checks if the
 * formula is ASTTrue or ASTFalse w.r.t to a model
 */
ASTNode AbsRefine_CounterExample::ComputeFormulaUsingModel(const ASTNode& form)
{
  const Kind k = form.GetKind();
  if (!(is_Form_kind(k) && BOOLEAN_TYPE == form.GetType()))
  {
    FatalError(" ComputeConstFormUsingModel: "
               "The input is a non-formula: ",
               form);
  }

  // cerr << "Input to ComputeFormulaUsingModel:" << form << endl;
  ASTNodeMap::const_iterator it1;
  if ((it1 = ComputeFormulaMap.find(form)) != ComputeFormulaMap.end())
  {
    const ASTNode& res = it1->second;
    if (ASTTrue == res || ASTFalse == res)
    {
      return res;
    }
    else
    {
      FatalError("ComputeFormulaUsingModel: "
                 "The value of a formula must be TRUE or FALSE:",
                 form);
    }
  }

  // Unlike the term arm (TermToConstTermUsingModel), floating-point *predicates*
  // are not routed through encodeForModel. Encoding the whole predicate and
  // re-entering the evaluator runs the recursion at fpEncodedEvaluationDepth > 0,
  // where the term arm's own encode step is switched off -- so any float operand
  // reached inside the encoded predicate would fall through to the term switch's
  // default. Instead the FP_* predicate cases below resolve each operand to a
  // constant at depth 0 (where the term arm does encode floats correctly) and
  // fold the predicate over those constants.

  ASTNode output = ASTUndefined;
  switch (k)
  {
    case TRUE:
    case FALSE:
      output = form;
      break;
    case SYMBOL:
      if (BOOLEAN_TYPE != form.GetType())
        FatalError(" ComputeFormulaUsingModel: "
                   "Non-Boolean variables are not formulas",
                   form);
      if (CounterExampleMap.find(form) != CounterExampleMap.end())
      {
        ASTNode counterexample_val = CounterExampleMap[form];
        if (!bm->VarSeenInTerm(form, counterexample_val))
        {
          output = ComputeFormulaUsingModel(counterexample_val);
        }
        else
        {
          output = counterexample_val;
        }
      }
      else
      {
        // Has been simplified out. Can take any value.
        output = ASTFalse;
      }
      break;
    case ARRAY_EQ:
    {
      ExtensionalityContext* ext = bm->getExtensionalityIfAny();
      ASTNode lowered;
      if (ext != NULL && ext->getCurrentLowering(form, lowered))
      {
        // This solve decided the equality; its lowering is the answer.
        output = ComputeFormulaUsingModel(lowered);
      }
      else
      {
        // It did not: either the equality belongs to an earlier query,
        // or lowering discarded it -- an equality nested in a conjunct
        // that solving a write chain against its own base dropped as
        // shadowed. There is no abstraction variable to consult, and
        // the one that used to be consulted here had never been
        // assigned, so it read false while the model gave the two
        // arrays identical contents.
        //
        // Ask the model instead. It is the same model the caller is
        // about to print, so the answer agrees with it by construction,
        // which is the property the abstraction variable could not
        // offer.
        if (!arrayEqualityIsModelDecidable(form[0]) ||
            !arrayEqualityIsModelDecidable(form[1]))
          FatalError("array-equality: cannot evaluate an opaque equality "
                     "over float-indexed arrays that was not reachable in "
                     "the most recent solve",
                     form);
        output = ArraysEqualUsingModel(form[0], form[1]) ? ASTTrue : ASTFalse;
      }
      break;
    }
    case BOOLEXTRACT:
    {
      ASTNode t0 = TermToConstTermUsingModel(form[0]);
      output = simp->BVConstEvaluator(bm->CreateNode(BOOLEXTRACT, t0, form[1]));
      break;
    }
    case EQ:
    case BVLT:
    case BVLE:
    case BVGT:
    case BVGE:
    case BVSLT:
    case BVSLE:
    case BVSGT:
    case BVSGE:
    case BVUADDO:
    case BVSADDO:
    case BVUMULO:
    case BVSMULO:
    case BVUSUBO:
    case BVSSUBO:
    {
      ASTVec children;
      children.reserve(form.Degree());

      for (auto it = form.begin(), itend = form.end();
           it != itend; it++)
      {
        children.push_back(TermToConstTermUsingModel(*it, false));
      }

      output = NonMemberBVConstEvaluator(bm, k, children, form.GetValueWidth());
    }
    break;

    case NAND:
    case NOR:
    case NOT:
    case AND:
    case XOR:
    case IFF:
    case IMPLIES:
    case OR:
    {
      ASTVec children;
      children.reserve(form.Degree());

      for (auto it = form.begin(), itend = form.end();
           it != itend; it++)
      {
        children.push_back(ComputeFormulaUsingModel(*it));
      }

      output = NonMemberBVConstEvaluator(bm, k, children, form.GetValueWidth());
    }
    break;

    case ITE:
    {
      ASTNode t0 = ComputeFormulaUsingModel(form[0]);
      if (ASTTrue == t0)
        output = ComputeFormulaUsingModel(form[1]);
      else if (ASTFalse == t0)
        output = ComputeFormulaUsingModel(form[2]);
      else
        FatalError("ComputeFormulaUsingModel: ITE: "
                   "something is wrong with the formula: ",
                   form);
    }
    break;
    case FP_LEQ:
    case FP_LT:
    case FP_GEQ:
    case FP_GT:
    case FP_EQ:
    case FP_ISNORMAL:
    case FP_ISSUBNORMAL:
    case FP_ISZERO:
    case FP_ISINFINITE:
    case FP_ISNAN:
    case FP_ISNEGATIVE:
    case FP_ISPOSITIVE:
    case FP_SMT_EQ:
    {
      // Rebuild at the node's real arity: the comparisons are binary but the
      // classification predicates are unary.
      ASTVec operands;
      operands.reserve(form.Degree());

      for (unsigned int i = 0; i < form.Degree(); i++)
      {
        ASTNode simp(TermToConstTermUsingModel(form[i]));
        // An operand must resolve to a constant, as in the float arm of
        // TermToConstTermUsingModel: the read-tolerant flag is on inside the
        // walk, so a float-element array read the solve never constrained
        // comes back as the symbolic READ (case 2 there) rather than a
        // value. Rebuilding the predicate over it is not evaluation -- the
        // blaster would carry the read along, and the same-operand folds
        // below can hand the bare READ back. The read is genuinely
        // unconstrained here, so resolve it to a concrete value.
        if (BVCONST != simp.GetKind())
          simp = TermToConstTermUsingModel(form[i], false);
        assert(simp.GetKind() == BVCONST);
        operands.push_back(FloatBlaster::withFormat(
            bm, simp, form[i].GetExpWidth(), form[i].GetSigWidth()));
      }

      ASTNode temp(bm->CreateNode(k, operands));

      // Rebuilding through the simplifying factory may rewrite the predicate
      // rather than return it: constant operands fold to true/false outright,
      // and the same-operand rules fire here because interned constants
      // compare pointer-equal -- fp.leq of a value with itself comes back as
      // (not (fp.isNaN ...)). Whatever came back that is not this operation
      // is a formula; evaluate it, never blast it.
      if (temp.GetKind() != k)
      {
        output = ComputeFormulaUsingModel(temp);
        break;
      }

      // One table, the same one the solver's lowering pass uses. temp's
      // operands were re-stamped with their formats above, so it is a
      // well-formed source node and its own sorts say what the formats are.
      ASTNode blasted(FloatBlast::lowerOperation(bm, temp));

      assert(blasted != temp);
      assert(blasted != form);

      output = ComputeFormulaUsingModel(blasted);
      break;
    }
    default:
      cerr << _kind_names[k];
      FatalError(" ComputeFormulaUsingModel: "
                 "the kind has not been implemented",
                 ASTUndefined);
      break;
  }

  assert(ASTUndefined != output);
  assert(output.isConstant());
  ComputeFormulaMap[form] = output;
  return output;
}

void AbsRefine_CounterExample::CheckCounterExample(
    bool t, const ASTNode& checked_input)
{
  // input is valid, no counterexample to check
  if (bm->ValidFlag)
    return;

  // t is true if SAT solver generated a counterexample, else it is false
  if (!t)
    FatalError("CheckCounterExample: "
               "No CounterExample to check",
               ASTUndefined);
  // Check the exact semantic root used by this solve. TopLevelSTP has already
  // totalised its floating-point operations and CallSAT_ResultCheck has kept
  // this root aligned with solve-boundary array-equality lowering; rebuilding
  // the check from the manager's parsed assertions would lose both facts.
  if (bm->UserFlags.stats_flag)
    printf("checking counterexample\n");

  if (debug_counterexample)
    cerr << "checking " << checked_input;

  // Drop the formula memo first. Its entries were produced while the
  // model was still being assembled -- before the array-equality
  // consistency check published its certified observations, in an
  // active solve -- and reusing them would let this check confirm the
  // answer with the very values it is supposed to be re-deriving. What
  // is deliberately kept is CounterExampleMap: that is the model, not a
  // cache of conclusions about it.
  ClearComputeFormulaMap();

  if (ASTFalse == ComputeFormulaUsingModel(checked_input))
    FatalError("CheckCounterExample:counterexample bogus: "
               "the submitted query evaluates to FALSE under the "
               "counterexample: NOT OK",
               checked_input);

  // The walk above resolves each opaque array equality through its
  // recorded lowering, so it re-derives the Boolean skeleton but takes
  // the equalities themselves on trust. Ask the other half of the
  // question here: does the model that is about to be printed give the
  // equalities the values the solver assigned them?
  // Deliberately not gated on active(): an equality lowering solved
  // outright -- a write chain against its own base, or a reflexive fold
  // -- mints no record, so there is nothing active to gate on, and it
  // is exactly the case with no consistency checker behind it.
  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  if (ext != NULL && ext->enabled())
  {
    const char* reason = ext->recheckCertifiedEqualities(this);
    if (reason != NULL)
      FatalError(reason);
  }
}

// Asking the model a question must not change it. Evaluation memoises,
// and where it cannot account for a read it invents a value and records
// it -- so a question would otherwise leave cells behind that the model
// printer and vc_getCounterExampleArray then report as part of the
// answer. Both public query entry points roll the model back to what it
// was; the invented values are deterministic, so anything that needs
// one again gets the same one.
namespace
{
class ModelQuery
{
  ASTNodeMap& cells;
  ASTNodeMap& formulas;
  const ASTNodeMap savedCells;
  const ASTNodeMap savedFormulas;

public:
  ModelQuery(ASTNodeMap& c, ASTNodeMap& f)
      : cells(c), formulas(f), savedCells(c), savedFormulas(f)
  {
  }
  ~ModelQuery()
  {
    cells = savedCells;
    formulas = savedFormulas;
  }
  ModelQuery(const ModelQuery&) = delete;
  ModelQuery& operator=(const ModelQuery&) = delete;
};
} // namespace

// See the header.
void AbsRefine_CounterExample::CollectArrayNodes(const ASTNode& arrayTerm,
                                                 ASTNodeSet& out) const
{
  ASTVec pending(1, arrayTerm);
  while (!pending.empty())
  {
    const ASTNode n = pending.back();
    pending.pop_back();
    if (!out.insert(n).second)
      continue;
    if (WRITE == n.GetKind())
      pending.push_back(n[0]);
    else if (ITE == n.GetKind() && ARRAY_TYPE == n.GetType())
    {
      pending.push_back(n[1]);
      pending.push_back(n[2]);
    }
    else if (SYMBOL == n.GetKind())
    {
      // A substituted-away symbol's cells live against its definition.
      const ASTNodeMap::const_iterator sub = CounterExampleMap.find(n);
      if (sub != CounterExampleMap.end() &&
          ARRAY_TYPE == sub->second.GetType())
        pending.push_back(sub->second);
    }
  }
}

// See the header. Zero bits is +0.0 for a float element and a perfectly
// ordinary bitvector otherwise, so the only sort needing its own answer
// is RoundingMode, whose one-hot encoding leaves all-zero denoting
// nothing at all. RNE is the mode published for such a cell -- the same
// choice cvc5 makes, and IEEE 754's default rounding direction; the
// value is a don't-care, so what matters is that every site takes it
// from here and none of them invents its own.
ASTNode
AbsRefine_CounterExample::defaultCellValue(const ASTNode& arrayTerm) const
{
  if (bm->arrayHasRmElement(arrayTerm))
    return bm->CreateBVConst(5, symbolic_fp::ROUND_NEAREST_TIES_TO_EVEN);
  return bm->CreateZeroConst(arrayTerm.GetValueWidth());
}

// See the header. This is the walk the read path already performs for
// an array the extensionality checker owns, lifted out so that it can
// be asked about any array term, including one from a solve that never
// owned anything.
void AbsRefine_CounterExample::CollectModelCells(const ASTNodeSet& arrays,
                                                 ModelCells& out)
{
  for (ASTNodeMap::const_iterator it = CounterExampleMap.begin();
       it != CounterExampleMap.end(); ++it)
  {
    if (READ != it->first.GetKind() || !it->first[1].isConstant() ||
        arrays.find(it->first[0]) == arrays.end())
      continue;
    const std::pair<ASTNode, ASTNode> key(
        it->first[0], plainBitVectorConstant(bm, it->first[1]));
    // One cell recorded under both spellings of its index must not
    // become two entries; the records agree, being the same cell.
    if (out.find(key) == out.end())
      out[key] = it->second;
  }
}

ASTNode AbsRefine_CounterExample::ReadUsingModel(const ASTNode& arrayTerm,
                                                 const ASTNode& concreteIndex,
                                                 const ModelCells& cells)
{
  ASTNode level = arrayTerm;
  while (true)
  {
    const ModelCells::const_iterator recorded =
        cells.find(std::make_pair(level, concreteIndex));
    if (recorded != cells.end())
      return BVCONST == recorded->second.GetKind()
                 ? recorded->second
                 : TermToConstTermUsingModel(recorded->second, false);

    if (WRITE == level.GetKind())
    {
      // Stepping over the write is a claim that the two indexes address
      // different cells, so it is asked on bits.
      if (!constantsDenoteDifferentValues(
              TermToConstTermUsingModel(level[1], false), concreteIndex))
        return TermToConstTermUsingModel(level[2], false);
      level = level[0];
      continue;
    }

    if (ITE == level.GetKind() && ARRAY_TYPE == level.GetType())
    {
      const ASTNode cond = ComputeFormulaUsingModel(level[0]);
      if (ASTTrue == cond)
        level = level[1];
      else if (ASTFalse == cond)
        level = level[2];
      else
        FatalError("ReadUsingModel: an array if-then-else condition has no "
                   "truth value in the model",
                   level[0]);
      continue;
    }

    // A symbol equality propagation substituted away holds exactly what
    // its definition holds.
    if (SYMBOL == level.GetKind())
    {
      const ASTNodeMap::const_iterator sub = CounterExampleMap.find(level);
      if (sub != CounterExampleMap.end() &&
          ARRAY_TYPE == sub->second.GetType())
      {
        level = sub->second;
        continue;
      }
    }

    // A base array the model records nothing for at this index. It
    // holds what the printer fills it with.
    return defaultCellValue(level);
  }
}

// See the header. The one restriction, in one place.
//
// A float-indexed array is answerable, but only through the solve's own
// encoding context: the solve canonicalises float indexes and records
// the model against the lowered carrier access, so the operands must be
// lowered the same way before the walk can find a cell. Without that
// context -- outside a solve, or in a unit fixture that never made one
// -- the question cannot be put.
bool AbsRefine_CounterExample::arrayEqualityIsModelDecidable(
    const ASTNode& arrayTerm) const
{
  const SourceSort sort = arrayTerm.GetSourceSort();
  return sort.kind() != SourceSort::Kind::Array ||
         !sort.index().usesFloatingPointTheory() || fpEncodingContext != NULL;
}

bool AbsRefine_CounterExample::ArraysEqualUsingModel(const ASTNode& left,
                                                     const ASTNode& right)
{
  if (left == right)
    return true;

  ModelQuery unchanged(CounterExampleMap, ComputeFormulaMap);

  // Two floating-point sorts, two independent problems; an array can
  // have either, both, or neither.
  //
  // A float *element* changes only the comparison: cells are compared
  // for the same value rather than the same bits, because NaN is one
  // value with many packings. The walk is unaffected.
  //
  // A float *index* changes where the cells are. The solve canonicalises
  // those indexes and records the model against the lowered carrier
  // access, so the operands have to be lowered the same way before a
  // cell can be found at all. Stay in encoded mode from there for the
  // reason the term evaluator gives where it does the same: the lowered
  // DAG keeps its source-sort metadata, and a nested access would
  // otherwise be taken for a fresh source boundary and canonicalised
  // again.
  SourceSort elementSort = SourceSort::unknown();
  bool encode = false;
  {
    const SourceSort arraySort = left.GetSourceSort();
    if (arraySort.kind() == SourceSort::Kind::Array)
    {
      elementSort = arraySort.element();
      encode = fpEncodingContext != NULL && fpEncodedEvaluationDepth == 0 &&
               arraySort.index().usesFloatingPointTheory();
    }
  }
  const ASTNode lowered_left =
      encode ? requireFpEncodingContext().encodeForModel(left) : left;
  const ASTNode lowered_right =
      encode ? requireFpEncodingContext().encodeForModel(right) : right;
  std::unique_ptr<ScopedFpEncodedEvaluation> evaluating;
  if (encode)
    evaluating.reset(new ScopedFpEncodedEvaluation(fpEncodedEvaluationDepth));
  if (lowered_left == lowered_right)
    return true;

  ASTNodeSet arrays;
  CollectArrayNodes(lowered_left, arrays);
  CollectArrayNodes(lowered_right, arrays);
  ModelCells cells;
  CollectModelCells(arrays, cells);

  // Every cell the model records against one of those arrays, plus every
  // index a write in either term writes to -- a write's own cell need
  // not be recorded, and stepping over it is exactly what makes the
  // array above it differ from the one below.
  //
  // Both sources are already normalised, and both have to be: an index
  // is a value, and two spellings of one value would be two candidates,
  // the one that does not match the recorded cell finding nothing and
  // completing to zero. The cell keys are normalised where they are
  // built; a written index is whatever the term evaluator returns, and
  // that is documented to be a plain constant for this very reason.
  std::set<ASTNode> indexes;
  for (ModelCells::const_iterator it = cells.begin(); it != cells.end(); ++it)
    indexes.insert(it->first.second);
  for (ASTNodeSet::const_iterator it = arrays.begin(); it != arrays.end();
       ++it)
    if (WRITE == it->GetKind())
      indexes.insert(TermToConstTermUsingModel((*it)[1], false));

  // By value at the element's sort, never by node identity: a
  // float-element cell holds a floating-point constant, which interns
  // apart from the plain constant with the same bits -- and the zero an
  // unobserved cell completes to is exactly such a plain constant.
  for (std::set<ASTNode>::const_iterator it = indexes.begin();
       it != indexes.end(); ++it)
    if (constantsDenoteDifferentSourceValues(
            ReadUsingModel(lowered_left, *it, cells),
            ReadUsingModel(lowered_right, *it, cells), elementSort))
      return false;
  return true;
}

// See the header.
ASTNode AbsRefine_CounterExample::QueryFormulaAgainstModel(const ASTNode& form)
{
  ModelQuery unchanged(CounterExampleMap, ComputeFormulaMap);
  return ComputeFormulaUsingModel(form);
}

/* FUNCTION: queries the value of expr given the current counterexample.
 */
ASTNode AbsRefine_CounterExample::GetCounterExample(const ASTNode& expr)
{
  // input is valid, no counterexample to get
  if (bm->ValidFlag)
    return ASTUndefined;

  if (BOOLEAN_TYPE == expr.GetType())
  {
    return ComputeFormulaUsingModel(expr);
  }

  // Model evaluation works in plain bit-vector constants throughout (see
  // TermToConstTermUsingModel, which strips the format off every result it
  // returns), but this is where a value crosses back out to the caller. A
  // float-sorted term's value has to be float-sorted again here: handed a
  // bare bit-vector, asserting (= term value) builds a float/bit-vector mix
  // that does not typecheck, so STP rejects its own model. Found by murxla's
  // -C model check, which re-asserts every reported value.
  return bm->LiftSourceValue(TermToConstTermUsingModel(expr, false),
                             expr.GetSourceSort());
}

// The observed (index, value) entries of one array symbol, evaluated to
// constants, one entry per concrete index, in ascending unsigned index
// order -- so the programmatic model API is deterministic and agrees
// with the printed model. The CounterExampleMap is keyed by hash-consed
// READ(array, index) nodes, so one index can only carry one entry;
// conflicting duplicates would mean a broken model and fail loudly.
vector<std::pair<ASTNode, ASTNode>>
AbsRefine_CounterExample::GetSortedArrayModelEntries(const ASTNode& arraySym)
{
  vector<std::pair<ASTNode, ASTNode>> entries;

  // A symbol equality propagation substituted away has no reads of its
  // own in the model; it holds exactly what its definition holds. Derive
  // its entries from the definition: every cell the model records
  // against the definition's base arrays, plus every index one of its
  // writes covers. Equality propagation only substitutes plain
  // bitvector-sorted arrays, so indexes and cells are plain constants
  // here.
  {
    const ASTNodeMap::const_iterator sub = CounterExampleMap.find(arraySym);
    if (sub != CounterExampleMap.end() &&
        ARRAY_TYPE == sub->second.GetType())
    {
      const ASTNode definition = sub->second;
      ASTNodeSet arrays;
      CollectArrayNodes(definition, arrays);
      ModelCells cells;
      CollectModelCells(arrays, cells);

      std::set<ASTNode> indexes;
      for (ModelCells::const_iterator it = cells.begin(); it != cells.end();
           ++it)
        indexes.insert(it->first.second);
      for (ASTNodeSet::const_iterator it = arrays.begin();
           it != arrays.end(); ++it)
        if (WRITE == it->GetKind())
          indexes.insert(TermToConstTermUsingModel((*it)[1], false));

      for (std::set<ASTNode>::const_iterator it = indexes.begin();
           it != indexes.end(); ++it)
        entries.push_back(
            std::make_pair(*it, ReadUsingModel(definition, *it, cells)));

      std::sort(entries.begin(), entries.end(),
                [](const std::pair<ASTNode, ASTNode>& x,
                   const std::pair<ASTNode, ASTNode>& y) {
                  return CONSTANTBV::BitVector_Lexicompare(
                             x.first.GetBVConst(), y.first.GetBVConst()) < 0;
                });
      return entries;
    }
  }

  // Take a copy of the counterexample map, 'cause TermToConstTermUsingModel
  // changes it. Which breaks the iterator otherwise.
  const ASTNodeMap c(CounterExampleMap);

  // The element sort decides when two recorded values for one cell are
  // really two values: NaN has many packings and one meaning.
  const SourceSort arraySort = arraySym.GetSourceSort();
  const SourceSort elementSort =
      arraySort.kind() == SourceSort::Kind::Array ? arraySort.element()
                                                  : SourceSort::unknown();

  std::map<ASTNode, ASTNode> byIndex;
  for (const auto& e : c)
  {
    const ASTNode& f = e.first;
    if (f.GetKind() == READ && f[0] == arraySym && f[1].GetKind() == BVCONST)
    {
      ASTNode rhs;
      if (BITVECTOR_TYPE == e.second.GetType() ||
          FLOATINGPOINT_TYPE == e.second.GetType())
      {
        rhs = TermToConstTermUsingModel(e.second, false);
      }
      else
      {
        rhs = ComputeFormulaUsingModel(e.second);
      }
      assert(rhs.isConstant());
      // Key on the plain spelling of the index, not on the node. A
      // rounding-mode or float constant interns apart from the plain
      // constant with its bits, so one cell can be recorded under two
      // index nodes -- and keying on the node makes that one cell two
      // entries, which the printer then emits as two stores of the same
      // value to the same index.
      auto ins = byIndex.insert(
          std::make_pair(plainBitVectorConstant(bm, f[1]), rhs));
      if (!ins.second && constantsDenoteDifferentSourceValues(
                             ins.first->second, rhs, elementSort))
        FatalError("GetSortedArrayModelEntries: conflicting model values "
                   "for one concrete array index",
                   f);
    }
  }

  entries.assign(byIndex.begin(), byIndex.end());
  std::sort(entries.begin(), entries.end(),
            [](const std::pair<ASTNode, ASTNode>& x,
               const std::pair<ASTNode, ASTNode>& y) {
              return CONSTANTBV::BitVector_Lexicompare(
                         x.first.GetBVConst(), y.first.GetBVConst()) < 0;
            });
  return entries;
}

// FUNCTION: queries the counterexample, and returns the number of array
// locations for e
vector<std::pair<ASTNode, ASTNode>>
AbsRefine_CounterExample::GetCounterExampleArray(bool t, const ASTNode& e)
{
  vector<std::pair<ASTNode, ASTNode>> entries;

  // input is valid, no counterexample to print
  if (bm->ValidFlag)
  {
    return entries;
  }

  // t is true if SAT solver generated a counterexample, else it is
  // false
  if (!t)
  {
    return entries;
  }

  // With array equality disabled, keep the pre-extension extraction
  // path -- including its unordered traversal -- byte for byte. The
  // deterministic sorted path below applies only when the extension is
  // enabled.
  if (!bm->UserFlags.enable_array_equality)
  {
    // Take a copy of the counterexample map, 'cause TermToConstTermUsingModel
    // changes it. Which breaks the iterator otherwise.
    const ASTNodeMap c(CounterExampleMap);

    ASTNodeMap::const_iterator it = c.begin();
    ASTNodeMap::const_iterator itend = c.end();
    for (; it != itend; it++)
    {
      const ASTNode& f = it->first;
      const ASTNode& se = it->second;

      if (ARRAY_TYPE == se.GetType())
      {
        FatalError("TermToConstTermUsingModel: "
                   "entry in counterexample is an arraytype. bogus:",
                   se);
      }

      // skip over introduced variables, and over the reads of an introduced
      // array -- those entries are keyed on the read, not on the array
      if (bm->isIntroducedCounterExampleEntry(f))
      {
        continue;
      }
      if (f.GetKind() == READ && f[0] == e && f[0].GetKind() == SYMBOL &&
          f[1].GetKind() == BVCONST)
      {
        ASTNode rhs;
        if (BITVECTOR_TYPE == se.GetType() || FLOATINGPOINT_TYPE == se.GetType())
        {
          rhs = TermToConstTermUsingModel(se, false);
        }
        else
        {
          rhs = ComputeFormulaUsingModel(se);
        }
        assert(rhs.isConstant());
        entries.push_back(std::make_pair(f[1], rhs));
      }
    }
  }
  else if (e.GetKind() == SYMBOL)
  {
    entries = GetSortedArrayModelEntries(e);
  }

  // Hand the pairs back at the array's declared sorts, for the reason
  // GetCounterExample re-stamps its result: an index that is a bare
  // bit-vector is not accepted back as an index of a float-indexed array,
  // and a bare element cannot be equated with a read of a float-element
  // one. Done here rather than in either extraction path, so the model
  // printer keeps seeing GetSortedArrayModelEntries' raw constants.
  const SourceSort array_sort = e.GetSourceSort();
  assert(array_sort.kind() == SourceSort::Kind::Array);
  for (std::pair<ASTNode, ASTNode>& entry : entries)
  {
    entry.first = bm->LiftSourceValue(entry.first, array_sort.index());
    entry.second = bm->LiftSourceValue(entry.second, array_sort.element());
  }

  return entries;
}

// TODO printing of expressions.
// TODO move to printer file.
void AbsRefine_CounterExample::PrintSMTLIB2(std::ostream& os, const ASTNode& n)
{
  if (n.GetKind() == SYMBOL)
  {
    os << "( ";

    os << "|";
    n.nodeprint(os);
    os << "| ";

    if (bm->isRoundingModeSymbol(n))
    {
      // A RoundingMode value must print as a mode name -- a legal term of
      // the sort -- not as its raw 5-bit carrier. The declaration pinned the
      // symbol one-hot, so the model value always names a mode; anything
      // else would be a bug, but print the bits rather than crash.
      const ASTNode v = TermToConstTermUsingModel(n, false);
      const char* name = printer::roundingModeName(v.GetUnsignedConst());
      if (name != NULL)
        os << name;
      else
        printer::outputBitVecSMTLIB2(v, os);
    }
    else if (n.GetType() == stp::FLOATINGPOINT_TYPE)
      // A floating-point value must be printed in floating-point syntax
      // (fp #bS #bE #bM), not as the raw packed bit-vector -- the get-model
      // path (outputLine) does this; get-value must match, or it hands back a
      // bit-vector literal where an operand of floating-point sort is expected.
      printer::outputFloatingPointSMTLIB2(TermToConstTermUsingModel(n, false),
                                          os, n);
    else if (n.GetType() == stp::BITVECTOR_TYPE)
      printer::outputBitVecSMTLIB2(TermToConstTermUsingModel(n, false), os);
    else
    {
      if (ASTTrue == ComputeFormulaUsingModel(n))
        os << "true";
      else
        os << "false";
    }
    os << " )";
  }
}

//todo does it need to be member?
void AbsRefine_CounterExample::outputLine(std::ostream& os, const ASTNode &f, ASTNode se)
{
    if (ARRAY_TYPE == se.GetType())
    {
      // A definitional alias installed by equality propagation (array
      // symbol := array term), not a cell of the model. The cells are
      // recorded against the definition's base arrays and print there.
      return;
    }

    // skip over introduced variables, and over the reads of an introduced
    // array -- those entries are keyed on the read, not on the array
    if (bm->isIntroducedCounterExampleEntry(f))
    {
      return;
    }

    if (f.GetKind() == SYMBOL)
    {
      os << "(define-fun ";
      os << "|";
      f.nodeprint(os);
      os << "|";

      if (bm->isRoundingModeSymbol(f))
      {
        // As in PrintSMTLIB2: the sort and value are RoundingMode, not the
        // 5-bit carrier.
        os << " () RoundingMode ";
        const ASTNode v = TermToConstTermUsingModel(se, false);
        const char* name = printer::roundingModeName(v.GetUnsignedConst());
        if (name != NULL)
          os << name;
        else
          printer::outputBitVecSMTLIB2(v, os);
      }
      else if (f.GetType() == stp::BITVECTOR_TYPE)
      {
        os << " () (";
        os << "_ BitVec " << f.GetValueWidth() << ")";
        printer::outputBitVecSMTLIB2(TermToConstTermUsingModel(se, false), os);
      }
      else if (f.GetType() == stp::BOOLEAN_TYPE)
      {
        se = ComputeFormulaUsingModel(f);
        assert (se == bm->ASTTrue || se == bm->ASTFalse);
        os << " () Bool " << ((se == bm->ASTTrue) ? "true" : "false");
      }
      else if (f.GetType() == stp::FLOATINGPOINT_TYPE)
      {
        os << " () (";
        os << "_ FloatingPoint " << f.GetExpWidth() << " " << f.GetSigWidth()
           << ") ";
        printer::outputFloatingPointSMTLIB2(
            TermToConstTermUsingModel(se, false), os, f);
      }
      else
      {
        FatalError("Wrong Type");
      }

      os << ")" << std::endl;
    }

    //TODO completely the wrong format.
    if ((f.GetKind() == READ && f[0].GetKind() == SYMBOL &&
         f[1].GetKind() == BVCONST))
    {
      const ASTNode& array = f[0];

      // The true sorts, so the line replays against the original
      // declaration: a float element's format is on the array node, while
      // a float index format and RoundingMode on either side come from the
      // manager's array registries.
      unsigned int idx_exp = 0;
      unsigned int idx_sig = 0;
      const bool fp_index = bm->arrayHasFpIndex(array, idx_exp, idx_sig);
      const bool rm_index = bm->arrayHasRmIndex(array);
      const bool rm_element = bm->arrayHasRmElement(array);
      const bool fp_element = array.GetExpWidth() != 0;

      os << "(define-fun ";

      os << "|";
      array.nodeprint(os);
      // No trailing space: the sorts and values below each supply their own
      // leading one, exactly as in the scalar branch above.
      os << "|";

      if (fp_index)
        os << " (_ FloatingPoint " << idx_exp << " " << idx_sig << ")";
      else if (rm_index)
        os << " RoundingMode";
      else
        os << " (_ BitVec " << array.GetIndexWidth() << ")";

      if (fp_element)
        os << " (_ FloatingPoint " << array.GetExpWidth() << " "
           << array.GetSigWidth() << ")";
      else if (rm_element)
        os << " RoundingMode";
      else
        os << " (_ BitVec " << array.GetValueWidth() << ")";

      // A RoundingMode cell or index prints by mode name when the bits name
      // one (they always should; print the bits rather than crash), a float
      // as an (fp ...) literal, exactly as scalar values of those sorts do.
      const ASTNode index = TermToConstTermUsingModel(f[1], false);
      if (fp_index)
      {
        os << " ";
        printer::outputFloatingPointSMTLIB2(index, os, idx_exp, idx_sig);
      }
      else if (rm_index)
      {
        const char* name = printer::roundingModeName(index.GetUnsignedConst());
        os << " ";
        if (name != NULL)
          os << name;
        else
          printer::outputBitVecSMTLIB2(index, os);
      }
      else
        printer::outputBitVecSMTLIB2(index, os);

      const ASTNode value = TermToConstTermUsingModel(se, false);
      if (fp_element)
      {
        os << " ";
        printer::outputFloatingPointSMTLIB2(value, os, array.GetExpWidth(),
                                            array.GetSigWidth());
      }
      else if (rm_element)
      {
        const char* name = printer::roundingModeName(value.GetUnsignedConst());
        os << " ";
        if (name != NULL)
          os << name;
        else
          printer::outputBitVecSMTLIB2(value, os);
      }
      else
        printer::outputBitVecSMTLIB2(value, os);

      os << ")" << endl;
    }

}

/*
 SMTLIB2 models are supposed to contain all variables.
 So we can't just use the counterexample - because some might have been eliminated from the problem
 before SAT solving.
*/
void AbsRefine_CounterExample::PrintFullCounterExampleSMTLIB2(std::ostream& os)
{
  const ASTNodeSet symbols = bm->getSymbols();

  // With array equality disabled, follow the pre-extension output
  // path byte for byte, legacy array format and all. The repaired
  // printer below applies only when the extension is enabled.
  if (!bm->UserFlags.enable_array_equality)
  {
    for (ASTNode f: symbols)
    {
        if (ARRAY_TYPE != f.GetType())
          outputLine(os, f, f); // Can't do arrays because we need the reads.
    }

    ASTNodeMap c; // believe we need a copy because iterator gets invalidated?
    for (const auto& e: CounterExampleMap)
    {
      if (READ == e.first.GetKind())
          c.insert(e);
    }

    // The map iterates in an order that follows interning history, which
    // varies across configurations of the solver. Sort the observed reads
    // by array name and then by index, so one query prints one model text
    // everywhere. Solver-map entries can carry a read at a symbolic index
    // next to the concrete observations, so indexes are only compared as
    // bits when both are constants; symbolic ones sort after, by name
    // when possible.
    const auto nodeBefore = [](const ASTNode& a, const ASTNode& b) {
      if (a.GetKind() == SYMBOL && b.GetKind() == SYMBOL)
        return strcmp(a.GetName(), b.GetName()) < 0;
      return a.GetNodeNum() < b.GetNodeNum();
    };
    std::vector<std::pair<ASTNode, ASTNode>> reads(c.begin(), c.end());
    std::sort(reads.begin(), reads.end(),
              [&nodeBefore](const std::pair<ASTNode, ASTNode>& x,
                            const std::pair<ASTNode, ASTNode>& y) {
                const ASTNode& ax = x.first[0];
                const ASTNode& ay = y.first[0];
                if (ax != ay)
                  return nodeBefore(ax, ay);
                const ASTNode& ix = x.first[1];
                const ASTNode& iy = y.first[1];
                const bool cx = ix.isConstant();
                const bool cy = iy.isConstant();
                if (cx && cy)
                  return CONSTANTBV::BitVector_Lexicompare(ix.GetBVConst(),
                                                           iy.GetBVConst()) < 0;
                if (cx != cy)
                  return cx;
                return nodeBefore(ix, iy);
              });

    for (const auto& e : reads)
    {
      outputLine(os, e.first, e.second);
    }
    os.flush();
    return;
  }

  for (ASTNode f: symbols)
  {
      if (ARRAY_TYPE != f.GetType())
        outputLine(os, f, f); // Arrays are printed below, from the reads.
  }

  // Arrays: emit one valid nullary define-fun per array symbol whose
  // body is the constant defaultCellValue array with every observed
  // (index, value) pair stored on top, in ascending concrete-index
  // order. The printed model replays in a conforming SMT-LIB2 solver.
  // This is the surface every other completion site has to match: what
  // is printed here is what the model says about a cell nothing
  // observed.
  vector<ASTNode> arrays;
  for (ASTNode f : symbols)
    if (ARRAY_TYPE == f.GetType() && !bm->FoundIntroducedSymbolSet(f))
      arrays.push_back(f);
  std::sort(arrays.begin(), arrays.end(),
            [](const ASTNode& x, const ASTNode& y) {
              return strcmp(x.GetName(), y.GetName()) < 0;
            });

  for (const ASTNode& array : arrays)
  {
    // Shared with GetCounterExampleArray, so the text and programmatic
    // model surfaces expose identical deterministic observations.
    vector<std::pair<ASTNode, ASTNode>> entries =
        GetSortedArrayModelEntries(array);

    const unsigned iw = array.GetIndexWidth();
    const unsigned vw = array.GetValueWidth();

    // The define-fun prints the array's true sorts -- the element float
    // format lives on the symbol, a float index format and RoundingMode
    // on either side in the manager's registries -- with (fp ...)
    // literals for float cells and indexes and mode names for
    // RoundingMode ones, so it replays against the original
    // declaration.
    const unsigned eb = array.GetExpWidth();
    const unsigned sb = array.GetSigWidth();
    unsigned ieb = 0, isb = 0;
    const bool fpIndex = bm->arrayHasFpIndex(array, ieb, isb);
    const bool rmIndex = bm->arrayHasRmIndex(array);
    const bool rmElement = bm->arrayHasRmElement(array);

    std::ostringstream sortText;
    sortText << "(Array ";
    if (fpIndex)
      sortText << "(_ FloatingPoint " << ieb << " " << isb << ")";
    else if (rmIndex)
      sortText << "RoundingMode";
    else
      sortText << "(_ BitVec " << iw << ")";
    sortText << " ";
    if (eb != 0)
      sortText << "(_ FloatingPoint " << eb << " " << sb << ")";
    else if (rmElement)
      sortText << "RoundingMode";
    else
      sortText << "(_ BitVec " << vw << ")";
    sortText << ")";

    const auto printCell = [&](const ASTNode& cell) {
      if (eb != 0)
      {
        os << " ";
        printer::outputFloatingPointSMTLIB2(cell, os, eb, sb);
        return;
      }
      if (rmElement)
      {
        const char* name = printer::roundingModeName(cell.GetUnsignedConst());
        if (name == NULL)
          FatalError("array-equality: a RoundingMode cell of the model "
                     "is not one of the five modes",
                     cell);
        os << " " << name;
        return;
      }
      printer::outputBitVecSMTLIB2(cell, os);
    };
    const auto printIndex = [&](const ASTNode& index) {
      if (fpIndex)
      {
        os << " ";
        printer::outputFloatingPointSMTLIB2(index, os, ieb, isb);
        return;
      }
      if (rmIndex)
      {
        const char* name = printer::roundingModeName(index.GetUnsignedConst());
        if (name == NULL)
          FatalError("array-equality: a RoundingMode index of the model "
                     "is not one of the five modes",
                     index);
        os << " " << name;
        return;
      }
      printer::outputBitVecSMTLIB2(index, os);
    };

    os << "(define-fun |";
    array.nodeprint(os);
    os << "| () " << sortText.str();
    for (size_t i = 0; i < entries.size(); i++)
      os << " (store";
    os << " ((as const " << sortText.str() << ")";
    // The unobserved cells' value, printed through the same cell
    // printer as an observed one, so that what is published here is
    // demonstrably the value every other reader completes with rather
    // than text that happens to match it.
    printCell(defaultCellValue(array));
    os << ")";
    for (size_t i = 0; i < entries.size(); i++)
    {
      printIndex(entries[i].first);
      printCell(entries[i].second);
      os << ")";
    }
    os << ")" << std::endl;
  }

  os.flush();
}

// Just uses the symbols from the counter example, might not be every symbol defined in the problem.
void AbsRefine_CounterExample::PrintCounterExampleSMTLIB2(std::ostream& os)
{
  // Take a copy of the counterexample map, 'cause TermToConstTermUsingModel
  // changes it. Which breaks the iterator otherwise.
  const ASTNodeMap c(CounterExampleMap);

  ASTNodeMap::const_iterator it = c.begin();
  ASTNodeMap::const_iterator itend = c.end();
  for (; it != itend; it++)
  {
    const ASTNode& f = it->first;
    const ASTNode& se = it->second;
    outputLine(os, f,se);

  }
  os.flush();
}

// FUNCTION: prints a counterexample for INVALID inputs.  iterate
// through the CounterExampleMap data structure and print it to
// stdout
void AbsRefine_CounterExample::PrintCounterExample(bool t, std::ostream& os)
{
  // input is valid, no counterexample to print
  if (bm->ValidFlag)
  {
    return;
  }

  // if this option is true then print the way dawson wants using a
  // different printer. do not use this printer.
  if (bm->UserFlags.print_arrayval_declaredorder_flag)
  {
    return;
  }

  // t is true if SAT solver generated a counterexample, else it is
  // false
  if (!t)
  {
    os << "PrintCounterExample: No CounterExample to print: " << endl;
    return;
  }

  bm->PLPrintNodeSet.clear();
  bm->NodeLetVarMap.clear();
  bm->NodeLetVarVec.clear();
  bm->NodeLetVarMap1.clear();

  // Take a copy of the counterexample map, 'cause TermToConstTermUsingModel
  // changes it. Which breaks the iterator otherwise.
  const ASTNodeMap c(CounterExampleMap);

  ASTNodeMap::const_iterator it = c.begin();
  ASTNodeMap::const_iterator itend = c.end();
  for (; it != itend; it++)
  {
    const ASTNode& f = it->first;
    const ASTNode& se = it->second;

    if (ARRAY_TYPE == se.GetType())
    {
      // A definitional alias installed by equality propagation (array
      // symbol := array term), not a cell of the model. The cells are
      // recorded against the definition's base arrays and print there.
      continue;
    }

    // skip over introduced variables, and over the reads of an introduced
    // array -- those entries are keyed on the read, not on the array
    if (bm->isIntroducedCounterExampleEntry(f))
    {
      continue;
    }
    if (f.GetKind() == SYMBOL ||
        (f.GetKind() == READ && f[0].GetKind() == SYMBOL &&
         f[1].GetKind() == BVCONST))
    {

      os << "ASSERT( ";

      printer::PL_Print1(os, f, 0, false, bm);
      if (BOOLEAN_TYPE == f.GetType())
      {
        os << "<=>";
      }
      else
      {
        os << " = ";
      }

      ASTNode rhs;
      if (BITVECTOR_TYPE == se.GetType() || FLOATINGPOINT_TYPE == se.GetType())
      {
        rhs = TermToConstTermUsingModel(se, false);
      }
      else
      {
        rhs = ComputeFormulaUsingModel(se);
      }
      assert(rhs.isConstant());
      printer::PL_Print1(os, rhs, 0, false, bm);

      os << " );" << endl;
    }
  }
}

/* iterate through the CounterExampleMap data structure and print it
 * to stdout. this function prints only the declared array variables
 * IN the ORDER in which they were declared. It also assumes that
 * the variables are of the form 'varname_number'. otherwise it will
 * not print anything. This function was specifically written for
 * Dawson Engler's group (bug finding research group at Stanford)
 */
void AbsRefine_CounterExample::PrintCounterExample_InOrder(bool t)
{
  // global command-line option to print counterexample. we do not
  // want both counterexample printers to print at the sametime.
  // FIXME: This should always print the counterexample.  If you want
  // to turn it off, check the switch at the point of call.
  if (bm->UserFlags.print_counterexample_flag)
    return;

  // input is valid, no counterexample to print
  if (bm->ValidFlag)
    return;

  // print if the commandline option is '-q'. allows printing the
  // counterexample in order.
  if (!bm->UserFlags.print_arrayval_declaredorder_flag)
    return;

  // t is true if SAT solver generated a counterexample, else it is
  // false
  if (!t)
  {
    cerr << "PrintCounterExample: No CounterExample to print: " << endl;
    return;
  }

  // vector to store the integer values
  vector<int> out_int;
  cout << "% ";
  for (ASTVec::iterator it = bm->ListOfDeclaredVars.begin(),
                        itend = bm->ListOfDeclaredVars.end();
       it != itend; it++)
  {
    if (ARRAY_TYPE == it->GetType())
    {
      // get the name of the variable
      const char* c = it->GetName();
      std::string ss(c);
      if (!(0 == strncmp(ss.c_str(), "ini_", 4)))
        continue;
      reverse(ss.begin(), ss.end());

      // cout << "debugging: " << ss;
      size_t pos = ss.find('_', 0);
      if (!((0 < pos) && (pos < ss.size())))
        continue;

      // get the associated length
      std::string sss = ss.substr(0, pos);
      reverse(sss.begin(), sss.end());
      int n = atoi(sss.c_str());

      it->PL_Print(cout, bm, 2);
      for (int j = 0; j < n; j++)
      {
        ASTNode index = bm->CreateBVConst(it->GetIndexWidth(), j);
        ASTNode readexpr =
            bm->CreateTerm(READ, it->GetValueWidth(), *it, index);
        ASTNode val = GetCounterExample(readexpr);
        // cout << "ASSERT( ";
        // cout << " = ";
        out_int.push_back(val.GetUnsignedConst());
        // cout << "\n";
      }
    }
  }
  cout << endl;
  for (unsigned int jj = 0; jj < out_int.size(); jj++)
    cout << out_int[jj] << endl;
  cout << endl;
}

// Prints Satisfying assignment directly, for debugging.
void AbsRefine_CounterExample::PrintSATModel(SATSolver& newS,
                                             ToSATBase::ASTNodeToSATVar& m)
{
  if (!newS.okay())
    FatalError("PrintSATModel: NO COUNTEREXAMPLE TO PRINT", ASTUndefined);
  if (!(bm->UserFlags.stats_flag && bm->UserFlags.print_nodes_flag))
    return;

  cout << "Satisfying assignment: " << endl;
  for (ToSATBase::ASTNodeToSATVar::const_iterator it = m.begin(); it != m.end();
       it++)
  {
    ASTNode symbol = it->first;
    vector<unsigned> v = it->second;

    for (size_t i = 0; i < v.size(); i++)
    {
      if (v[i] == ~((unsigned)0)) // nb. special value.
        continue;

      if (newS.modelValue(v[i]) == newS.true_literal())
      {
        it->first.nodeprint(cout);
        cout << " {" << i << "}" << endl;
      }
      else if (newS.modelValue(v[i]) == newS.false_literal())
      {
        cout << "NOT ";
        it->first.nodeprint(cout);
        cout << " {" << i << "}" << endl;
      }
    }
  }
}

// FUNCTION: this function accepts a boolvector and returns a BVConst
ASTNode AbsRefine_CounterExample::BoolVectoBVConst(const vector<bool>* w,
                                                   const unsigned int l)
{
  assert(l == (unsigned)w->size());

  CBV cc = CONSTANTBV::BitVector_Create(l, true);
  for (unsigned int jj = 0; jj < l; jj++)
  {
    if ((*w)[jj] == true)
      CONSTANTBV::BitVector_Bit_On(cc, l - 1 - jj);
  }

  return bm->CreateBVConst(cc, l);
}

void AbsRefine_CounterExample::CopySolverMap_To_CounterExample(void)
{

  if (!simp->Return_SolverMap()->empty())
  {
    CounterExampleMap.insert(simp->Return_SolverMap()->begin(),
                             simp->Return_SolverMap()->end());
  }
}

SOLVER_RETURN_TYPE
AbsRefine_CounterExample::CallSAT_ResultCheck(SATSolver& SatSolver,
                                              const ASTNode& modified_input,
                                              const ASTNode& original_input,
                                              const ASTNode& submitted_input,
                                              ToSATBase* tosat, bool refinement)
{
  bool sat = tosat->CallSAT(SatSolver, modified_input, refinement);

  if (bm->soft_timeout_expired)
    return SOLVER_TIMEOUT;

  if (!sat)
  {
    return SOLVER_VALID;
  }
  else if (SatSolver.okay())
  {
    if (!bm->UserFlags.construct_counterexample_flag)
      return SOLVER_INVALID;

    bm->GetRunTimes()->start(RunTimes::CounterExampleGeneration);
    CounterExampleMap.clear();
    ComputeFormulaMap.clear();

    ToSATBase::ASTNodeToSATVar satVarToSymbol = tosat->SATVar_to_SymbolIndexMap();
    ConstructCounterExample(SatSolver, satVarToSymbol);
    if (bm->UserFlags.stats_flag && bm->UserFlags.print_nodes_flag)
    {
      ToSATBase::ASTNodeToSATVar m = tosat->SATVar_to_SymbolIndexMap();
      PrintSATModel(SatSolver, m);
    }
    // Array equality: the consistency checker runs on every candidate
    // whenever the current solve has an active lowered equality -- even when
    // STP's ordinary model evaluation already failed -- and an array
    // conflict takes priority. In an active solve every read belongs to
    // this checker, so only its array lemmas can rule such a candidate
    // out; skipping an ordinary-false candidate could therefore loop
    // without progress.
    // A candidate is reported satisfiable only when both checks pass
    // on the same assignment. Any active satisfiable candidate is
    // required below to have a fully bound graph.
    //
    // The checker runs before the ordinary evaluation so that its
    // conflict-free fixed point can be published into the model first:
    // an owned read that was simplified out of the transformed formula
    // is evaluated from the certified array contents, which must agree
    // with every observation the propagation derived (e.g. a read
    // observing a value across a true array equality). Publication and
    // the verification of the scalar names against the completed model
    // happen inside checkCandidate.
    ExtensionalityContext* ext = bm->getExtensionalityIfAny();
    const bool extRegistered = ext != NULL && ext->active();
    if (extRegistered && !ext->checkerReady())
      FatalError("array-equality: a SAT candidate reached model checking "
                 "before the complete array graph was bound");
    const bool extActive = extRegistered;
    ExtensionalityContext::CandidateOutcome extOutcome =
        ExtensionalityContext::EXT_SKIPPED;
    if (extActive)
      extOutcome = ext->checkCandidate(this);

    // A conflicting candidate has no certified array model. Its complete
    // checker certificate is already pending, so do not run ordinary model
    // evaluation: that path is allowed to fill defaults and caches for a
    // completed model, which this candidate deliberately is not.
    if (extOutcome == ExtensionalityContext::EXT_CONFLICT)
    {
      if (!ext->hasPendingLemma())
        FatalError("array-equality: a checker conflict has no pending lemma");
      bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);
      return SOLVER_UNDECIDED;
    }
    if (extActive && extOutcome != ExtensionalityContext::EXT_CONSISTENT)
      FatalError("array-equality: the checker could neither certify nor "
                 "refute a materialized candidate");

    // check if the counterexample is good or not
    ASTNode orig_result = ComputeFormulaUsingModel(original_input);
    if (!(ASTTrue == orig_result || ASTFalse == orig_result))
      FatalError("TopLevelSat: Original input must compute to "
                 "true or false against model");
    bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

    switch (ExtensionalityContext::decideCertification(
        ASTTrue == orig_result, extActive, extOutcome))
    {
      case ExtensionalityContext::ADD_EXT_LEMMA:
        // the pending certificate is retained; the extensionality refinement
        // driver installs its clause and re-solves
        return SOLVER_UNDECIDED;

      case ExtensionalityContext::INTERNAL_ERROR:
        FatalError("CallSAT_ResultCheck: the complete array checker and "
                   "the bit-blasted/model-evaluation path disagree on the "
                   "same candidate -- the array-equality integration is "
                   "broken");
        return SOLVER_ERROR; // unreachable

      case ExtensionalityContext::RETURN_SAT:
      {
        if (bm->UserFlags.check_counterexample_flag)
        {
          CheckCounterExample(SatSolver.okay(), submitted_input);
        }

        if ((bm->UserFlags.stats_flag ||
             bm->UserFlags.print_counterexample_flag) &&
            (!bm->UserFlags.smtlib2_parser_flag))
        {
          PrintCounterExample(SatSolver.okay());
          PrintCounterExample_InOrder(SatSolver.okay());
        }
        return SOLVER_INVALID;
      }

      case ExtensionalityContext::RUN_HOST_REFINEMENT:
      default:
      {
        // counterexample is bogus: flag it
        if (bm->UserFlags.stats_flag && bm->UserFlags.print_nodes_flag)
        {
          cout << "Supposedly bogus one: \n";
          PrintCounterExample(true);
        }

        return SOLVER_UNDECIDED;
      }
    }
  }
  else
  {
    // Control should never reach here
    // PrintOutput(true);
    return SOLVER_ERROR;
  }
}
}
