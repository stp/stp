/***********
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

#include "stp/Simplifier/SkeletonPreproc.h"
#include "stp/Sat/SATSolverFactory.h"

#include <iostream>
#include <memory>
#include <unordered_set>

namespace stp
{

namespace
{

// Literals in the solver's own 2*var+sign encoding, so that nothing here
// has to translate at the point of use.
inline int mkLit(unsigned var, bool negated)
{
  return (int)(2 * var + (negated ? 1 : 0));
}

inline int negate(int lit)
{
  return lit ^ 1;
}

inline unsigned varOf(int lit)
{
  return (unsigned)(lit >> 1);
}

void addClause(SATSolver& s, const std::vector<int>& lits)
{
  SATSolver::vec_literals cl;
  for (int l : lits)
    cl.push(SATSolver::mkLit(varOf(l), (l & 1) != 0));
  s.addClause(cl);
}

} // namespace

bool SkeletonPreproc::isConnective(const ASTNode& n)
{
  switch (n.GetKind())
  {
    case AND:
    case OR:
    case NOT:
    case XOR:
    case IFF:
    case IMPLIES:
    case NAND:
    case NOR:
      break;

    case ITE:
      // An ITE over terms is a term; only the Boolean one is structure.
      if (n.GetType() != BOOLEAN_TYPE)
        return false;
      break;

    default:
      return false;
  }

  // A connective whose children are not all Boolean is not something this
  // can descend into -- which is what makes a predicate over bit-vectors an
  // atom rather than structure.
  for (const ASTNode& c : n.GetChildren())
    if (c.GetType() != BOOLEAN_TYPE)
      return false;

  return true;
}

ASTVec SkeletonPreproc::derive(const ASTNode& input, bool& unsat)
{
  unsat = false;
  atomToVar.clear();
  varToAtom.clear();
  varToConnective.clear();
  litOf.clear();

  std::unique_ptr<SATSolver> solver(createSATSolver(bm->UserFlags));
  if (solver == NULL)
    return ASTVec();

  // Everything below reads what the backend fixed at the root. A backend
  // that cannot report that would be handed a CNF, asked to simplify it and
  // then asked nothing it can answer, so it is not handed one at all. The
  // pass is a no-op there rather than a waste, and a no-op is sound: what
  // it reports is only ever additional, never required.
  if (!solver->reportsRootFixed())
    return ASTVec();

  const ASTNode ASTTrue = bm->CreateNode(TRUE);
  const ASTNode ASTFalse = bm->CreateNode(FALSE);

  // A variable pinned true, so that a constant has a literal like anything
  // else and the walk below needs no special case for it.
  const unsigned trueVar = solver->newVar();
  solver->setFrozen(trueVar);
  addClause(*solver, {mkLit(trueVar, false)});
  const int trueLit = mkLit(trueVar, false);

  // Iterative post-order, because a query's Boolean structure is as deep as
  // its assertions are nested and this must not be the thing that overflows
  // a stack the rest of the pipeline survives.
  std::vector<std::pair<ASTNode, bool>> work;
  work.push_back(std::make_pair(input, false));

  while (!work.empty())
  {
    const ASTNode node = work.back().first;
    const bool expanded = work.back().second;
    work.pop_back();

    if (litOf.find(node) != litOf.end())
      continue;

    if (node == ASTTrue)
    {
      litOf[node] = trueLit;
      continue;
    }
    if (node == ASTFalse)
    {
      litOf[node] = negate(trueLit);
      continue;
    }

    if (!isConnective(node))
    {
      // An atom. One variable per distinct node, which is what lets a
      // repeated predicate be recognised as the same fact.
      auto it = atomToVar.find(node);
      if (it == atomToVar.end())
      {
        const unsigned v = solver->newVar();
        solver->setFrozen(v);
        atomToVar[node] = v;
        varToAtom.resize(v + 1);
        varToAtom[v] = node;
        litOf[node] = mkLit(v, false);
      }
      else
        litOf[node] = mkLit(it->second, false);
      continue;
    }

    if (!expanded)
    {
      work.push_back(std::make_pair(node, true));
      for (const ASTNode& c : node.GetChildren())
        if (litOf.find(c) == litOf.end())
          work.push_back(std::make_pair(c, false));
      continue;
    }

    // Every child has a literal by now.
    std::vector<int> ch;
    ch.reserve(node.Degree());
    for (const ASTNode& c : node.GetChildren())
      ch.push_back(litOf[c]);

    const Kind k = node.GetKind();

    if (k == NOT)
    {
      litOf[node] = negate(ch[0]);
      continue;
    }

    const unsigned out = solver->newVar();
    solver->setFrozen(out);
    const int o = mkLit(out, false);
    varToConnective.resize(out + 1);
    varToConnective[out] = node;

    switch (k)
    {
      case AND:
      case NAND:
      {
        const int res = (k == AND) ? o : negate(o);
        // res -> each child, and all children -> res.
        std::vector<int> big;
        big.push_back(res);
        for (int c : ch)
        {
          addClause(*solver, {negate(res), c});
          big.push_back(negate(c));
        }
        addClause(*solver, big);
        break;
      }

      case OR:
      case NOR:
      {
        const int res = (k == OR) ? o : negate(o);
        std::vector<int> big;
        big.push_back(negate(res));
        for (int c : ch)
        {
          addClause(*solver, {res, negate(c)});
          big.push_back(c);
        }
        addClause(*solver, big);
        break;
      }

      case IMPLIES:
      {
        // o <-> (!a | b)
        const int a = ch[0], b = ch[1];
        addClause(*solver, {negate(o), negate(a), b});
        addClause(*solver, {o, a});
        addClause(*solver, {o, negate(b)});
        break;
      }

      case XOR:
      case IFF:
      {
        // Folded pairwise; STP allows these n-ary.
        int acc = ch[0];
        for (size_t i = 1; i < ch.size(); i++)
        {
          const unsigned t = solver->newVar();
          solver->setFrozen(t);
          const int r = mkLit(t, false);
          const int b = ch[i];
          // r <-> acc XOR b
          addClause(*solver, {negate(r), acc, b});
          addClause(*solver, {negate(r), negate(acc), negate(b)});
          addClause(*solver, {r, negate(acc), b});
          addClause(*solver, {r, acc, negate(b)});
          acc = r;
        }
        // IFF of two is the negation of XOR; for more than two STP reads
        // IFF as the same left fold, so the negation applies once at the
        // end either way.
        const int res = (k == XOR) ? acc : negate(acc);
        addClause(*solver, {negate(o), res});
        addClause(*solver, {o, negate(res)});
        break;
      }

      case ITE:
      {
        const int c = ch[0], t = ch[1], e = ch[2];
        addClause(*solver, {negate(o), negate(c), t});
        addClause(*solver, {negate(o), c, e});
        addClause(*solver, {o, negate(c), negate(t)});
        addClause(*solver, {o, c, negate(e)});
        break;
      }

      default:
        // isConnective admitted it, so this cannot happen; leaving the
        // output unconstrained would be unsound rather than merely weak.
        FatalError("SkeletonPreproc: unhandled connective");
        break;
    }

    litOf[node] = o;
  }

  // The query holds, so its skeleton does.
  addClause(*solver, {litOf[input]});

  // 20 is CaDiCaL's "unsatisfiable". The skeleton is weaker than the query,
  // so its having no model settles the query too -- the one direction that
  // runs this way round.
  if (solver->simplifyOnly() == 20)
  {
    unsat = true;
    return ASTVec();
  }

  ASTVec facts;
  for (unsigned v = 0; v < varToAtom.size(); v++)
  {
    if (varToAtom[v].IsNull())
      continue;
    const int fixed = solver->rootFixed(v);
    if (fixed == 0)
      continue;
    facts.push_back(fixed > 0 ? varToAtom[v]
                              : bm->CreateNode(NOT, varToAtom[v]));
  }
  const size_t atomFacts = facts.size();

  // The connectives the same simplification fixed. Not every one of them is
  // news: a conjunct of the query is already at the top level, and so is
  // whatever sits under a chain of its negations (a NOT has no variable of
  // its own -- its literal is its child's, negated -- so the fixed node is
  // the child); and an output that its fixed inputs settle by the truth
  // table is implied by the facts above. What is left is a fact the query
  // implies but never states: a disjunction fixed true through an
  // equivalence whose other side was forced, a conjunction fixed false
  // through a conditional, and the like.
  std::unordered_set<ASTNode, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
      topLevel;
  {
    std::vector<ASTNode> walk;
    walk.push_back(input);
    while (!walk.empty())
    {
      const ASTNode n = walk.back();
      walk.pop_back();
      if (!topLevel.insert(n).second)
        continue;
      if (n.GetKind() == AND || n.GetKind() == NOT)
        for (const ASTNode& c : n.GetChildren())
          walk.push_back(c);
    }
  }
  for (unsigned v = 0; v < varToConnective.size(); v++)
  {
    const ASTNode& node = varToConnective[v];
    if (node.IsNull() || topLevel.count(node))
      continue;
    const int fixed = solver->rootFixed(v);
    if (fixed == 0)
      continue;
    const int settled = settledByInputs(*solver, node);
    // Inputs that settle the output settle it to the value the backend
    // fixed: both read the same clauses, and the formula has a model.
    assert(settled == 0 || settled == fixed);
    if (settled != 0)
      continue;
    facts.push_back(fixed > 0 ? node : bm->CreateNode(NOT, node));
  }

  // One line, because the numbers together are what says whether the pass
  // earned its SAT call: how much structure there was, how much of it was a
  // distinct predicate, how many atoms the solver settled, and how many
  // facts about the structure itself it found on top of them.
  if (bm->UserFlags.stats_flag)
    std::cerr << "Skeleton preprocessing: " << litOf.size() << " nodes, "
              << atomToVar.size() << " atoms, " << atomFacts << " forced, "
              << facts.size() - atomFacts << " connectives" << std::endl;

  return facts;
}

int SkeletonPreproc::valueOf(SATSolver& solver, int lit) const
{
  const int fixed = solver.rootFixed(varOf(lit));
  return (lit & 1) ? -fixed : fixed;
}

int SkeletonPreproc::settledByInputs(SATSolver& solver,
                                     const ASTNode& node) const
{
  std::vector<int> in;
  in.reserve(node.Degree());
  for (const ASTNode& c : node.GetChildren())
  {
    const auto it = litOf.find(c);
    assert(it != litOf.end());
    in.push_back(valueOf(solver, it->second));
  }

  // AND is false on any false input and true only on all true; OR the
  // other way about. NAND and NOR are their negations.
  const auto conjunction = [&]() {
    bool allTrue = true;
    for (int x : in)
    {
      if (x < 0)
        return -1;
      allTrue = allTrue && x > 0;
    }
    return allTrue ? 1 : 0;
  };
  const auto disjunction = [&]() {
    bool allFalse = true;
    for (int x : in)
    {
      if (x > 0)
        return 1;
      allFalse = allFalse && x < 0;
    }
    return allFalse ? -1 : 0;
  };

  switch (node.GetKind())
  {
    case AND:
      return conjunction();
    case NAND:
      return -conjunction();
    case OR:
      return disjunction();
    case NOR:
      return -disjunction();

    case IMPLIES:
      if (in[0] < 0 || in[1] > 0)
        return 1;
      if (in[0] > 0 && in[1] < 0)
        return -1;
      return 0;

    case XOR:
    case IFF:
    {
      // The same left fold derive() encodes: XOR is the parity of the
      // inputs, and IFF is its negation applied once at the end. Any open
      // input leaves the parity open.
      int parity = -1;
      for (int x : in)
      {
        if (x == 0)
          return 0;
        if (x > 0)
          parity = -parity;
      }
      return node.GetKind() == XOR ? parity : -parity;
    }

    case ITE:
      if (in[0] > 0)
        return in[1];
      if (in[0] < 0)
        return in[2];
      // An open condition still settles the output when both branches
      // agree.
      return (in[1] != 0 && in[1] == in[2]) ? in[1] : 0;

    default:
      // isConnective admitted it, and NOT never reaches here: it has no
      // output variable of its own.
      assert(false && "settledByInputs: not a connective with an output");
      return 0;
  }
}

} // namespace stp
