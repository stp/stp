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
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/FpTotalise.h"
#include "stp/Printer/printers.h"
#include "stp/ToSat/ToSATAIG.h"

const bool debug_counterexample = false;

namespace stp
{
using std::cout;

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
      ASTNode key =
          bm->CreateTerm(READ, array.GetValueWidth(), array, arrayread_index);

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
// 4. doesn't have a value in the counterexample then return 0 as the
// 4. value of the arrayread.
ASTNode AbsRefine_CounterExample::TermToConstTermUsingModel(const ASTNode& term,
                                                            bool ArrayReadFlag)
{
  const ASTNode r = TermToConstTermUsingModel_inner(term, ArrayReadFlag);
  // The plain twin of a float constant: same bits, the flavour every
  // identity comparison in model evaluation expects.
  if (r.GetKind() == BVCONST && r.GetExpWidth() != 0)
    return bm->CreateBVConst(CONSTANTBV::BitVector_Clone(r.GetBVConst()),
                             r.GetValueWidth());
  return r;
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

  ASTNodeMap::const_iterator it1;
  if ((it1 = CounterExampleMap.find(term)) != CounterExampleMap.end())
  {
    const ASTNode& val = it1->second;
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
        // Has been simplified out. Can take any value; all-zero bits, which
        // for a float denotes +0.0.
        output = bm->CreateZeroConst(term.GetValueWidth());
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
        // index has a const value in the CounterExampleMap
        // ASTNode indexVal = CounterExampleMap[index];
        ASTNode indexVal =
            TermToConstTermUsingModel(CounterExampleMap[index], ArrayReadFlag);
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

      // if a value exists in the CounterExampleMap then return it
      if (CounterExampleMap.find(modelentry) != CounterExampleMap.end())
      {
        output = TermToConstTermUsingModel(CounterExampleMap[modelentry],
                                           ArrayReadFlag);
      }
      else if (ArrayReadFlag)
      {
        // return the array read over a constantindex
        output = modelentry;
      }
      else
      {
        // Has been simplified out. Can take any value.
        output = bm->CreateMaxConst(modelentry.GetValueWidth());
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
    case FP_ABS:
    case FP_NEG:
    case FP_ADD:
    case FP_SUB:
    case FP_MUL:
    case FP_DIV:
    case FP_FMA:
    case FP_SQRT:
    case FP_REM:
    case FP_ROUNDTOINTEGRAL:
    case FP_MIN:
    case FP_MAX:
    case FP_TOFP:
    case FP_TOFP_UNSIGNED:
    case FP_TO_UBV:
    case FP_TO_SBV:
    case FP_TO_IEEE_BV:
    {
      // Evaluate the float operands against the model and rebuild the node
      // with the same kind and arity. Non-float children are often already
      // constant -- the rounding mode of the arithmetic operations and to_fp's
      // format arguments -- and are carried through unchanged. But some are
      // not: the bit-vector a to_fp reinterprets can be an array read or other
      // term, and the array read that totalising adds to to_ubv/to_sbv/min/max
      // is likewise non-constant. Resolve those against the model too, else the
      // rebuilt node stays non-constant and cannot be evaluated.
      ASTVec children;
      children.reserve(term.Degree());

      for (unsigned int i = 0; i < term.Degree(); i++)
      {
        const ASTNode& child = term[i];

        if (child.GetType() != FLOATINGPOINT_TYPE)
        {
          if (child.isConstant())
            children.push_back(child);
          else
            children.push_back(TermToConstTermUsingModel(child, ArrayReadFlag));
          continue;
        }

        ASTNode simp(TermToConstTermUsingModel(child));
        // A float operand must resolve to a constant, like the bit-vector
        // operands in the default case below: with ArrayReadFlag set, a
        // read with no value in the model comes back as the symbolic READ
        // (case 2 above), and rebuilding the operation over it is not
        // evaluation. The blaster would mostly carry the read along, but an
        // identity fold in the rebuild (x * 1.0 is x) can hand the bare
        // READ back as the whole term, and the blaster has no case for
        // that. The read is genuinely unconstrained here, so resolve it to
        // a concrete value.
        if (BVCONST != simp.GetKind())
          simp = TermToConstTermUsingModel(child, false);
        assert(simp.GetKind() == BVCONST);
        children.push_back(FloatBlaster::withFormat(
            bm, simp, child.GetExpWidth(), child.GetSigWidth()));
      }

      ASTNode temp(bm->CreateTerm(k, term.GetValueWidth(), children));
      temp = FloatBlaster::withFormat(bm, temp, term.GetExpWidth(),
                                      term.GetSigWidth());

      // The factory may have folded the rebuilt operation to a constant once
      // its children were resolved: abs/neg of a constant is a sign-bit edit,
      // and x*1.0 / x/1.0 fold to x. That constant is the value -- blasting it
      // would hand a constant to the blaster, which only handles operations.
      // (This also subsumes the old expectation that rebuilding with resolved
      // children always changes the node, which folding can break.)
      if (temp.isConstant())
      {
        output = FloatBlaster::withFormat(bm, temp, term.GetExpWidth(),
                                          term.GetSigWidth());
        break;
      }

      // Totalise the partial operations (min/max and to_ubv/to_sbv) so the
      // blaster sees the extra child they carry once made total. This is
      // idempotent and a no-op for the total operations. A partial op reaches
      // here un-totalised when it is evaluated directly rather than as part of
      // the solved formula -- e.g. a term handed to get-value or built through
      // the API -- since the totalising pass only runs over the assertions.
      FpTotalise totalise(bm);
      temp = totalise.topLevel(temp);

      ASTNode blasted(FloatBlaster::BlastNode_TopLevel(bm, temp));

      assert(blasted != temp);
      assert(blasted != term);

      // Carry the format out with the result. Evaluating the blasted node
      // yields a bare BVCONST, and an enclosing floating-point operation
      // would then take it as an operand of format (0, 0) and compute the
      // wrong bits rather than fail.
      output = FloatBlaster::withFormat(
          bm, TermToConstTermUsingModel(blasted, ArrayReadFlag),
          term.GetExpWidth(), term.GetSigWidth());
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
    // that later lookup fall through to the documented "no value -> return 0".
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
    const ASTNode& val = it1->second;
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
    case PARAMBOOL:
      output = bm->NewParameterized_BooleanVar(form[0], form[1]);
      output = ComputeFormulaUsingModel(output);
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

      ASTNode blasted(FloatBlaster::BlastNode_TopLevel(bm, temp));

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

void AbsRefine_CounterExample::CheckCounterExample(bool t)
{
  // input is valid, no counterexample to check
  if (bm->ValidFlag)
    return;

  // t is true if SAT solver generated a counterexample, else it is false
  if (!t)
    FatalError("CheckCounterExample: "
               "No CounterExample to check",
               ASTUndefined);
  // The manager's assertions are a separate copy from the formula the solve
  // ran on, and they arrive here as parsed -- so the partial floating-point
  // operations still lack the child supplying their unspecified results.
  // Totalise them the same way. The arrays are shared (their identity is
  // their name), so the check sees exactly the operations the solve did.
  ASTVec c;
  {
    FpTotalise totalise(bm);
    const ASTVec stored = bm->GetAsserts();
    c.reserve(stored.size());
    for (size_t i = 0; i < stored.size(); i++)
      c.push_back(totalise.topLevel(stored[i]));
  }

  if (bm->UserFlags.stats_flag)
    printf("checking counterexample\n");

  for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend;
       it++)
  {
    if (debug_counterexample)
      cerr << "checking" << *it;

    if (ASTFalse == ComputeFormulaUsingModel(*it))
      FatalError("CheckCounterExample:counterexample bogus:"
                 "assert evaluates to FALSE under counterexample: "
                 "NOT OK",
                 *it);
  }

  // The smtlib ones don't have a query defined.
  if ((bm->GetQuery() != ASTUndefined) &&
      ASTTrue == ComputeFormulaUsingModel(bm->GetQuery()))
    FatalError("CheckCounterExample:counterexample bogus:"
               "query evaluates to TRUE under counterexample: "
               "NOT OK",
               bm->GetQuery());
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
  return FloatBlaster::withFormat(bm, TermToConstTermUsingModel(expr, false),
                                  expr.GetExpWidth(), expr.GetSigWidth());
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

    // skip over introduced variables
    if (f.GetKind() == SYMBOL && (bm->FoundIntroducedSymbolSet(f)))
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

      // Hand the pair back at the array's declared sorts, for the reason
      // GetCounterExample re-stamps its result: an index that is a bare
      // bit-vector is not accepted back as an index of a float-indexed
      // array, and a bare element cannot be equated with a read of a
      // float-element one.
      unsigned index_exp = 0;
      unsigned index_sig = 0;
      // Stays (0, 0) unless the array is float-indexed, which withFormat
      // reads as "no format to apply". The element format is the array's own.
      bm->arrayHasFpIndex(e, index_exp, index_sig);
      entries.push_back(std::make_pair(
          FloatBlaster::withFormat(bm, f[1], index_exp, index_sig),
          FloatBlaster::withFormat(bm, rhs, e.GetExpWidth(), e.GetSigWidth())));
    }
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
      FatalError("PrintCounterExampleSMTLIB2: "
                 "entry in counterexample is an arraytype. bogus:",
                 se);
    }

    // skip over introduced variables
    if (f.GetKind() == SYMBOL && (bm->FoundIntroducedSymbolSet(f)))
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

      os << "( define-fun ";

      os << "|";
      array.nodeprint(os);
      os << "| ";

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

      os << " )" << endl;
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
      FatalError("TermToConstTermUsingModel: "
                 "entry in counterexample is an arraytype. bogus:",
                 se);
    }

    // skip over introduced variables
    if (f.GetKind() == SYMBOL && (bm->FoundIntroducedSymbolSet(f)))
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
    // check if the counterexample is good or not
    ASTNode orig_result = ComputeFormulaUsingModel(original_input);
    if (!(ASTTrue == orig_result || ASTFalse == orig_result))
      FatalError("TopLevelSat: Original input must compute to "
                 "true or false against model");
    bm->GetRunTimes()->stop(RunTimes::CounterExampleGeneration);

    // if the counterexample is indeed a good one, then return
    // invalid
    if (ASTTrue == orig_result)
    {
      if (bm->UserFlags.check_counterexample_flag)
      {
        CheckCounterExample(SatSolver.okay());
      }

      if ((bm->UserFlags.stats_flag || bm->UserFlags.print_counterexample_flag) && (!bm->UserFlags.smtlib2_parser_flag))
      {
        PrintCounterExample(SatSolver.okay());
        PrintCounterExample_InOrder(SatSolver.okay());
      }
      return SOLVER_INVALID;
    }
    // counterexample is bogus: flag it
    else
    {
      if (bm->UserFlags.stats_flag && bm->UserFlags.print_nodes_flag)
      {
        cout << "Supposedly bogus one: \n";
        PrintCounterExample(true);
      }

      return SOLVER_UNDECIDED;
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
