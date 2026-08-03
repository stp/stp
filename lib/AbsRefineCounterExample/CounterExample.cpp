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
      if (symbol.GetType() == BITVECTOR_TYPE)
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

    if (symbol.GetType() == BITVECTOR_TYPE)
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
      if (!simp->InsideSubstitutionMap(key))
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

      // Has been simplified out. Can take any value.
      output = bm->CreateZeroConst(term.GetValueWidth());
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
            // base array with no observation: unobserved indices
            // default to zero
            val = bm->CreateZeroConst(term.GetValueWidth());
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

        // ... but having handed a value out, stand by it. The result is
        // memoised below under "term", whose index may be symbolic;
        // with array equality enabled the model surface prints a total
        // interpretation per array built from the concrete-index READ
        // keys alone, and fills every index it finds no key for with
        // zero. Without this the printer would commit the cell to zero
        // while the rest of the model was computed from the value
        // invented here, and (get-model) could return an
        // interpretation that falsifies the query it answered sat.
        // Gated on the option: with it off the counterexample map, and
        // so vc_getCounterExampleArray, must stay exactly as before.
        if (bm->UserFlags.enable_array_equality &&
            CounterExampleMap.find(modelentry) == CounterExampleMap.end())
          CounterExampleMap[modelentry] = output;
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
    case ARRAY_EQ:
    {
      ExtensionalityContext* ext = bm->getExtensionalityIfAny();
      ASTNode lowered;
      if (ext == NULL || !ext->getCurrentLowering(form, lowered))
        FatalError("array-equality: cannot evaluate an opaque equality that "
                   "was not reachable in the most recent solve",
                   form);
      output = ComputeFormulaUsingModel(lowered);
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
  ExtensionalityContext* ext = bm->getExtensionalityIfAny();
  if (ext != NULL && ext->active())
  {
    const char* reason = ext->recheckCertifiedEqualities(this);
    if (reason != NULL)
      FatalError(reason);
  }
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

  return TermToConstTermUsingModel(expr, false);
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

  // Take a copy of the counterexample map, 'cause TermToConstTermUsingModel
  // changes it. Which breaks the iterator otherwise.
  const ASTNodeMap c(CounterExampleMap);

  std::map<ASTNode, ASTNode> byIndex;
  for (const auto& e : c)
  {
    const ASTNode& f = e.first;
    if (f.GetKind() == READ && f[0] == arraySym && f[1].GetKind() == BVCONST)
    {
      ASTNode rhs;
      if (BITVECTOR_TYPE == e.second.GetType())
      {
        rhs = TermToConstTermUsingModel(e.second, false);
      }
      else
      {
        rhs = ComputeFormulaUsingModel(e.second);
      }
      assert(rhs.isConstant());
      auto ins = byIndex.insert(std::make_pair(f[1], rhs));
      if (!ins.second && ins.first->second != rhs)
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

      // skip over introduced variables
      if (f.GetKind() == SYMBOL && (bm->FoundIntroducedSymbolSet(f)))
      {
        continue;
      }
      if (f.GetKind() == READ && f[0] == e && f[0].GetKind() == SYMBOL &&
          f[1].GetKind() == BVCONST)
      {
        ASTNode rhs;
        if (BITVECTOR_TYPE == se.GetType())
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

    return entries;
  }

  if (e.GetKind() != SYMBOL)
  {
    return entries;
  }

  return GetSortedArrayModelEntries(e);
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

    if (n.GetType() == stp::BITVECTOR_TYPE)
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
      os << "( define-fun ";
      os << "|";
      f.nodeprint(os);
      os << "|";

      if (f.GetType() == stp::BITVECTOR_TYPE)
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
      else
      {
        FatalError("Wrong Type");
      }

      os << " )" << std::endl;
    }

    //TODO completely the wrong format.
    if ((f.GetKind() == READ && f[0].GetKind() == SYMBOL &&
         f[1].GetKind() == BVCONST))
    {

      os << "( define-fun ";

      os << "|";
      f[0].nodeprint(os);
      os << "| ";

      os << " (";
      os << "_ BitVec " << f[0].GetIndexWidth() << ")";

      os << " (";
      os << "_ BitVec " << f[0].GetValueWidth() << ")";

      printer::outputBitVecSMTLIB2(TermToConstTermUsingModel(f[1], false), os);

      printer::outputBitVecSMTLIB2(TermToConstTermUsingModel(se, false), os);
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

    for (const auto& e: c)
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
  // body is a constant-zero array with every observed (index, value)
  // pair stored on top, in ascending concrete-index order. The printed
  // model replays in a conforming SMT-LIB2 solver.
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
    os << "( define-fun |";
    array.nodeprint(os);
    os << "| () (Array (_ BitVec " << iw << ") (_ BitVec " << vw << "))";
    for (size_t i = 0; i < entries.size(); i++)
      os << " (store";
    os << " ((as const (Array (_ BitVec " << iw << ") (_ BitVec " << vw
       << ")))";
    printer::outputBitVecSMTLIB2(bm->CreateZeroConst(vw), os);
    os << " )";
    for (size_t i = 0; i < entries.size(); i++)
    {
      printer::outputBitVecSMTLIB2(entries[i].first, os);
      printer::outputBitVecSMTLIB2(entries[i].second, os);
      os << " )";
    }
    os << " )" << std::endl;
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
      if (BITVECTOR_TYPE == se.GetType())
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
