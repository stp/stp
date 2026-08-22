/********************************************************************
 * AUTHORS: Andrew Teylu
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

#include "stp/UninterpretedFunctions/UFLowering.h"
#include "stp/Globals/Globals.h"
#include "stp/STPManager/STPManager.h"
#include "stp/UninterpretedFunctions/UFContext.h"
#include "stp/Util/DagWalk.h"
#include <string>

namespace stp
{

namespace
{

bool isLeafActual(const ASTNode& actual)
{
  return actual.GetKind() == SYMBOL || actual.isConstant();
}

ASTNode rebuildWithChildren(const ASTNode& original,
                            const ASTVec& loweredChildren, STPMgr* manager)
{
  assert(original.Degree() == loweredChildren.size());
  bool changed = false;
  for (size_t i = 0; i < loweredChildren.size(); ++i)
    changed = changed || loweredChildren[i] != original[i];
  if (!changed)
    return original;

  NodeFactory* const factory = manager->defaultNodeFactory;
  ASTNode rebuilt;
  if (original.GetValueWidth() == 0)
    rebuilt = factory->CreateNode(original.GetKind(), loweredChildren);
  else
    // Mirror SubstitutionMap's rebuild funnel: CreateArrayTerm preserves both
    // widths for arrays and is also the width-preserving CreateTerm path for
    // non-Boolean bit-vector terms when the index width is zero.
    rebuilt =
        factory->CreateArrayTerm(original.GetKind(), original.GetIndexWidth(),
                                 original.GetValueWidth(), loweredChildren);

  if (rebuilt.GetSourceSort() != original.GetSourceSort())
    FatalError("UF lowering rebuilt a node at the wrong SourceSort", rebuilt);
  return rebuilt;
}

} // namespace

ASTNode
LoweredApplicationView::semanticRootWithDefinitions(STPMgr* manager) const
{
  assert(manager != NULL);
  if (namingDefinitions.empty() && sortConstraints.empty())
    return semanticRoot;
  ASTVec conjuncts;
  conjuncts.reserve(namingDefinitions.size() + sortConstraints.size() + 1);
  conjuncts.push_back(semanticRoot);
  conjuncts.insert(conjuncts.end(), namingDefinitions.begin(),
                   namingDefinitions.end());
  conjuncts.insert(conjuncts.end(), sortConstraints.begin(),
                   sortConstraints.end());
  return manager->defaultNodeFactory->CreateNode(AND, conjuncts);
}

UFLowering::UFLowering(STPMgr* manager) : manager_(manager)
{
  assert(manager_ != NULL);
}

LoweredApplicationView
UFLowering::lowerCompletedRoot(const ASTNode& publicRoot,
                               const UFSolveScope& scope) const
{
  if (publicRoot.IsNull() || !publicRoot.IsOwnedBy(manager_))
    FatalError("UF lowering requires a completed root owned by its context");

  LoweredApplicationView view;
  view.scope = scope;
  view.publicRoot = publicRoot;
  view.semanticRoot = publicRoot;

  UFContext* context = manager_->getUFContextIfAny();
  if (!manager_->UserFlags.enable_uninterpreted_functions)
  {
    if (context != NULL)
      context->releaseSolveProtection();
    return view;
  }

  if (context == NULL)
  {
    if (containsKind(publicRoot, UF_APPLY))
      FatalError("UF lowering found UF_APPLY without a manager context",
                 publicRoot);
    return view;
  }
  context->beginSolveProtection();

  // A name is canonical per lowered expression, matching the reference
  // oracle. This both avoids redundant definitions and makes an identical
  // persistent block reconstruct the identical semantic root.
  ASTNodeMap scalarNames;

  // Pin every RoundingMode scalar this lowering makes the checker's authority
  // for -- introduced results, introduced argument names, and the leaf
  // symbols it registers as solve scalars in their own right. The sort has
  // five values and its carrier thirty-two, so an unpinned one lets a model
  // name no mode at all: the generated define-fun would print a term of no
  // sort, and model evaluation could hand an illegal mode to an enclosing
  // floating-point operation as a constant operand.
  //
  // FpTotalise pins the same symbols out of the semantic root when it runs,
  // and an OR of five equalities is idempotent, so at worst this adds a
  // duplicate conjunct. What it buys is that the pin arrives with the symbol
  // instead of with a later pass: the persistent path decides whether to run
  // that pass from the *raw* block, and reset-assertions can retract a
  // declaration's own pin while keeping the declaration.
  //
  // Pins are appended in walk order rather than collected from
  // view.solveScalars, so that an identical block rebuilds an identical
  // conjunction without depending on a hash set's iteration order.
  ASTNodeSet pinnedRoundingModes;
  const auto pinIfRoundingMode = [&](const ASTNode& scalar) {
    if (!manager_->isRoundingModeSymbol(scalar) ||
        !pinnedRoundingModes.insert(scalar).second)
      return;
    view.sortConstraints.push_back(
        manager_->roundingModeValidConstraint(scalar));
  };

  // An actual, as the checker will compare it. Only a float moves: it becomes
  // its canonical packed bits, which is the sort's own equality rather than
  // the carrier's, so two NaNs of different payloads compare equal and the
  // two zeros stay apart. A constant takes the same boundary as everything
  // else -- it needs no special case, because a float constant is already
  // interned canonically (STPMgr::CreateFPConst quotients NaN) and the
  // boundary folds over it rather than building a circuit.
  const auto canonicalActual = [&](const ASTNode& lowered,
                                   const SourceSort& declared) -> ASTNode {
    if (declared.kind() != SourceSort::Kind::FloatingPoint)
      return lowered;
    return manager_->defaultNodeFactory->CreateTerm(
        FP_TO_IEEE_BV, declared.packedWidth(), lowered);
  };

  // A result, as the formula that replaces the application will see it. The
  // exact inverse of canonicalActual: the three-child to_fp reinterprets the
  // solved bits at the declared format.
  const auto theoryResult = [&](const ASTNode& result,
                                const SourceSort& declared) -> ASTNode {
    if (declared.kind() != SourceSort::Kind::FloatingPoint)
      return result;
    const ASTNode reinterpreted = manager_->defaultNodeFactory->CreateTerm(
        FP_TOFP, declared.packedWidth(),
        manager_->CreateBVConst(32, declared.exponentWidth()),
        manager_->CreateBVConst(32, declared.significandWidth()), result);
    if (reinterpreted.GetSourceSort() != declared)
      FatalError("UF lowering rebuilt a float result at the wrong SourceSort",
                 reinterpreted);
    return reinterpreted;
  };

  // A compound actual cannot be named while the walk is running: whether the
  // name is needed depends on how many applications its declaration turns out
  // to have, and the last of them may not have been reached yet. Each one is
  // parked here against the slot it will fill.
  struct PendingName
  {
    size_t record;
    size_t argument;
    ASTNode lowered;
    SourceSort sort;
  };
  std::vector<PendingName> pendingNames;

  // Rewrite the completed root once, bottom-up. The explicit walk keeps its
  // frames on the heap (input controls AST depth), visits each shared DAG node
  // once, and guarantees that a nested UF application has become its scalar
  // result before an enclosing application's actual is recorded.
  DenseNodeMap rewritten;
  view.semanticRoot = postOrderRebuild(
      publicRoot, rewritten,
      [&](const ASTNode& application, const ASTVec& loweredChildren) -> ASTNode
      {
        if (application.GetKind() != UF_APPLY)
          return rebuildWithChildren(application, loweredChildren, manager_);

        std::string diagnostic;
        if (!context->isRegisteredApplication(application) ||
            !context->validateApplicationChildren(application.GetChildren(),
                                                  &diagnostic))
          FatalError(("UF lowering rejected a malformed durable application: " +
                      diagnostic)
                         .c_str(),
                     application);
        if (!context->isActiveApplication(application))
          FatalError("UF lowering rejected a stale or inactive durable "
                     "application",
                     application);

        const UFDecl* declaration = context->lookupIdentity(application[0]);
        if (declaration == NULL)
          FatalError("UF lowering could not recover declaration identity",
                     application);
        if (loweredChildren.size() != application.Degree() ||
            loweredChildren.empty() || loweredChildren[0] != application[0])
          FatalError("UF lowering rewrote a declaration identity", application);

        LoweredApplicationRecord record;
        record.durableHandle = application;
        record.declaration = declaration;
        record.scope = scope;
        record.stableOrder = view.applications.size();
        record.loweredActuals.reserve(application.Degree() - 1);
        record.namedActuals.reserve(application.Degree() - 1);

        for (size_t i = 1; i < loweredChildren.size(); ++i)
        {
          const ASTNode& lowered = loweredChildren[i];
          const SourceSort& expected = declaration->signature().domain()[i - 1];
          if (application[i].GetSourceSort() != expected ||
              lowered.GetSourceSort() != expected)
            FatalError("UF lowering crossed a SourceSort boundary",
                       application);

          // From here down the record speaks the lowering sort. For every
          // sort but FloatingPoint that is the declared sort unchanged; a
          // float crosses into its canonical packed carrier here and does not
          // cross back until the model boundary.
          const SourceSort solved = UFSignature::loweringSort(expected);
          const ASTNode scalar = canonicalActual(lowered, expected);
          if (scalar.GetSourceSort() != solved)
            FatalError("UF lowering produced an actual at the wrong lowering "
                       "sort",
                       scalar);
          record.loweredActuals.push_back(scalar);

          if (isLeafActual(scalar))
          {
            record.namedActuals.push_back(scalar);
            // A source symbol is already its own canonical scalar name, but it
            // still participates in future direct-CNF lemmas. Protect/register it
            // exactly like an introduced name so ordinary preprocessing cannot
            // substitute it away and leave the lemma talking about an unlinked
            // fresh SAT value. Constants need no mapping or protection.
            if (scalar.GetKind() == SYMBOL)
            {
              view.protectedSymbols.insert(scalar);
              view.solveScalars.insert(scalar);
              pinIfRoundingMode(scalar);
            }
            continue;
          }

          PendingName pending;
          pending.record = record.stableOrder;
          pending.argument = record.namedActuals.size();
          pending.lowered = scalar;
          pending.sort = solved;
          pendingNames.push_back(pending);
          record.namedActuals.push_back(ASTNode());
        }

        const SourceSort& codomain = declaration->signature().codomain();
        if (application.GetSourceSort() != codomain)
          FatalError("UF lowering found a durable result with the wrong "
                     "SourceSort",
                     application);
        SourceSort solvedCodomain = UFSignature::loweringSort(codomain);
        std::string resultPrefix = "uf_result";
        record.resultSymbol = manager_->CreateDeterministicSourceVariable(
            solvedCodomain, resultPrefix, application);
        if (record.resultSymbol.GetSourceSort() != solvedCodomain)
          FatalError("UF lowering allocated a result at the wrong SourceSort",
                     record.resultSymbol);
        view.protectedSymbols.insert(record.resultSymbol);
        view.solveScalars.insert(record.resultSymbol);
        pinIfRoundingMode(record.resultSymbol);
        view.handleToResult.insert(
            std::make_pair(application, record.resultSymbol));
        view.applications.push_back(record);
        // A float result is solved as a packed bit-vector but the formula it
        // replaces expects a float, so it goes back in through the exact
        // inverse of the boundary its arguments came through: the three-child
        // "reinterpret these bits" to_fp. Every other sort is returned as
        // itself.
        return theoryResult(record.resultSymbol, codomain);
      });

  // Only a declaration with two or more lowered applications can ever produce
  // a congruence lemma, and a name for a compound actual exists solely so that
  // such a lemma has a scalar to equate. Naming one for a lone application
  // costs a protected symbol and a defining equality that drag the whole
  // argument expression into the bit-blast, where nothing can observe it.
  //
  // Two rounds, so that the decision does not depend on the order the walk
  // reached things: every name a comparable record needs is created first, and
  // a lone application sharing one of those terms then reuses it and stays
  // readable for free. Only an actual left without a name after both rounds
  // makes its record unobservable.
  std::map<const UFDecl*, size_t> applicationsPerDeclaration;
  for (const LoweredApplicationRecord& record : view.applications)
    applicationsPerDeclaration[record.declaration]++;

  const auto comparable = [&](const PendingName& pending) {
    return applicationsPerDeclaration[view.applications[pending.record]
                                          .declaration] > 1;
  };

  for (const PendingName& pending : pendingNames)
  {
    if (!comparable(pending))
      continue;
    ASTNode name;
    const ASTNodeMap::const_iterator found = scalarNames.find(pending.lowered);
    if (found != scalarNames.end())
      name = found->second;
    else
    {
      name = manager_->CreateDeterministicSourceVariable(pending.sort, "uf_arg",
                                                         pending.lowered);
      if (name.GetSourceSort() != pending.sort)
        FatalError("UF lowering allocated an argument name at the wrong "
                   "SourceSort",
                   name);
      scalarNames.insert(std::make_pair(pending.lowered, name));
      view.nameToTerm.insert(std::make_pair(name, pending.lowered));
      view.protectedSymbols.insert(name);
      view.solveScalars.insert(name);
      pinIfRoundingMode(name);
      view.namingDefinitions.push_back(
          manager_->defaultNodeFactory->CreateNode(
              pending.sort.kind() == SourceSort::Kind::Bool ? IFF : EQ, name,
              pending.lowered));
    }
    view.applications[pending.record].namedActuals[pending.argument] = name;
  }

  for (const PendingName& pending : pendingNames)
  {
    if (comparable(pending))
      continue;
    LoweredApplicationRecord& record = view.applications[pending.record];
    const ASTNodeMap::const_iterator found = scalarNames.find(pending.lowered);
    if (found != scalarNames.end())
      record.namedActuals[pending.argument] = found->second;
    else
      record.observableArguments = false;
  }

  // An unobservable record keeps its durable handle, its result symbol and its
  // lowered actuals; what it does not keep is a half-filled scalar tuple that
  // no checker round may read.
  for (LoweredApplicationRecord& record : view.applications)
    if (!record.observableArguments)
      record.namedActuals.clear();

  // This checks the whole barrier once, including the naming definitions.
  // Scanning every progressively larger actual separately would turn a
  // linear post-order rewrite back into a quadratic algorithm on shared
  // nested DAGs.
  if (containsKind(view.semanticRootWithDefinitions(manager_), UF_APPLY))
    FatalError("UF_APPLY crossed the completed-root lowering barrier",
               view.semanticRoot);

  context->installSolveProtection(view.protectedSymbols, view.solveScalars);
  return view;
}

} // namespace stp
