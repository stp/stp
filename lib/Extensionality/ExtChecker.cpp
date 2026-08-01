/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: July, 2026
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

// The consistency checking and lemma generation algorithm of
// Brummayer & Biere, "Lemmas on Demand for the Extensional Theory of
// Arrays", JSAT 6 (2010), sections 7 and 8. See ExtChecker.h for an
// overview of the rules and data model.

#include "stp/Extensionality/ExtChecker.h"
#include <algorithm>
#include <deque>

namespace stp
{

namespace
{

struct PathRecord
{
  ASTNode destination;
  size_t access;
  std::vector<ExtGuard> guards;
  const char* rule;
};

typedef std::pair<ASTNode, size_t> PairKey;

struct CheckerState
{
  const ExtGraph& graph;
  ExtModelView& model;
  const bool recordEvents;

  std::map<PairKey, PathRecord> paths;
  // rho, split per section 11.2: one representative access per
  // concrete index of each array, keyed by the index value so a
  // congruence lookup is a single probe; plus the representatives in
  // insertion order, for the observed-contents export.
  std::map<ASTNode, std::map<ASTNode, size_t>> rhoByIndex;
  std::map<ASTNode, std::vector<size_t>> rho; // insertion order preserved
  std::deque<PairKey> worklist;
  ExtCheckResult result;
  int seq;

  CheckerState(const ExtGraph& g, ExtModelView& m, bool ev)
      : graph(g), model(m), recordEvents(ev), seq(0)
  {
  }

  ASTNode accessIndex(size_t id)
  {
    return model.bvValue(graph.accesses[id].indexName);
  }

  ASTNode accessValue(size_t id)
  {
    return model.bvValue(graph.accesses[id].valueName);
  }

  void event(ExtEvent::Kind kind, const char* rule, const ASTNode& source,
             const ASTNode& destination, size_t access,
             const ASTNode& indexValue, const ASTNode& accessValue)
  {
    if (!recordEvents)
    {
      seq++;
      return;
    }
    ExtEvent e;
    e.seq = seq++;
    e.kind = kind;
    e.rule = rule;
    e.source = source;
    e.destination = destination;
    e.access = access;
    e.indexValue = indexValue;
    e.accessValue = accessValue;
    result.events.push_back(e);
  }

  // Congruence checking (rule C) runs on the fly, at insertion time,
  // against the one representative access per concrete index that rho
  // keeps for each array (section 11.2); insertion is
  // first-path-wins, so each (array, access) pair is processed once.
  // An access matching its representative in both concrete index and
  // concrete value is dropped without insertion or further
  // propagation: the representative reaches every array the duplicate
  // could reach, carrying the same value (see ExtChecker.h).
  // A conflict is appended to result.conflicts (without the lemmas,
  // which buildLemmas adds) and the fixed point carries on, so one pass
  // collects every independent conflict rather than only the earliest.
  void insert(const ASTNode& destination, size_t accessId,
              const std::vector<ExtGuard>& guards, const char* rule,
              const ASTNode& source)
  {
    const PairKey key(destination, accessId);
    if (paths.find(key) != paths.end())
    {
      result.stats["skipped_seen"]++;
      event(ExtEvent::SKIP_SEEN, rule, source, destination, accessId,
            ASTNode(), ASTNode());
      return;
    }

    const ASTNode idx = accessIndex(accessId);
    const ASTNode val = accessValue(accessId);

    std::map<ASTNode, size_t>& byIndex = rhoByIndex[destination];
    const std::map<ASTNode, size_t>::const_iterator hit = byIndex.find(idx);
    if (hit != byIndex.end())
    {
      const size_t otherId = hit->second;
      if (accessValue(otherId) != val)
      {
        ExtConflict c;
        c.commonArray = destination;
        c.leftAccess = otherId;
        c.rightAccess = accessId;
        c.indexValue = idx;
        c.leftValue = accessValue(otherId);
        c.rightValue = val;
        c.leftGuards = paths[PairKey(destination, otherId)].guards;
        c.rightGuards = guards;
        result.stats["conflicts"]++;
        event(ExtEvent::CONFLICT, rule, source, destination, accessId, idx,
              val);
        result.conflicts.push_back(c);

        // Record the pair as visited so a later path to it cannot report
        // the same conflict twice, but keep the arriving access out of
        // rho -- its value disagrees with the representative already
        // there -- and out of the work list, so nothing propagates
        // onward from a conflicting arrival. The representative keeps
        // the array's slot for this index, exactly as when the pass
        // stopped here.
        PathRecord pr;
        pr.destination = destination;
        pr.access = accessId;
        pr.guards = guards;
        pr.rule = rule;
        paths[key] = pr;
        return;
      }
      result.stats["skipped_represented"]++;
      event(ExtEvent::SKIP_REPRESENTED, rule, source, destination, accessId,
            idx, val);
      return;
    }

    PathRecord pr;
    pr.destination = destination;
    pr.access = accessId;
    pr.guards = guards;
    pr.rule = rule;
    paths[key] = pr;
    byIndex[idx] = accessId;
    rho[destination].push_back(accessId);
    worklist.push_back(key);
    result.stats["insertions"]++;

    ExtEvent::Kind kind;
    if (rule[0] == 'I' && rule[1] == '_')
    {
      result.stats["seeds"]++;
      kind = ExtEvent::SEED;
    }
    else
    {
      result.stats["propagations"]++;
      result.stats[std::string("rule_") + rule]++;
      kind = ExtEvent::PROPAGATE;
    }
    event(kind, rule, source, destination, accessId, idx, val);
  }
};

// Deterministic total order for premise atoms: rank by atom op
// (bv_eq < bv_ne < array_eq < bool_lit), then by operand node numbers.
bool atomLess(const ExtLemmaAtom& x, const ExtLemmaAtom& y)
{
  if (x.op != y.op)
    return x.op < y.op;
  unsigned xa = x.a.IsNull() ? 0 : x.a.GetNodeNum();
  unsigned ya = y.a.IsNull() ? 0 : y.a.GetNodeNum();
  if (xa != ya)
    return xa < ya;
  unsigned xb = x.b.IsNull() ? 0 : x.b.GetNodeNum();
  unsigned yb = y.b.IsNull() ? 0 : y.b.GetNodeNum();
  if (xb != yb)
    return xb < yb;
  unsigned xt = x.boolTerm.IsNull() ? 0 : x.boolTerm.GetNodeNum();
  unsigned yt = y.boolTerm.IsNull() ? 0 : y.boolTerm.GetNodeNum();
  return xt < yt;
}

// Canonicalize a premise: drop reflexive equalities (an index compared
// with itself contributes nothing), drop exact duplicate atoms, and
// sort deterministically. The guard paths feeding this are already
// shortest (section 11.1, a property of the FIFO work list); beyond
// that only exact duplicates are removed, no semantic subsumption.
std::vector<ExtLemmaAtom> canonicalAtoms(const std::vector<ExtLemmaAtom>& in)
{
  std::vector<ExtLemmaAtom> out;
  for (size_t i = 0; i < in.size(); i++)
  {
    const ExtLemmaAtom& a = in[i];
    if (a.op == ExtLemmaAtom::BV_EQ && a.a == a.b)
      continue;
    bool dup = false;
    for (size_t j = 0; j < out.size(); j++)
      if (out[j] == a)
      {
        dup = true;
        break;
      }
    if (!dup)
      out.push_back(a);
  }
  std::sort(out.begin(), out.end(), atomLess);
  return out;
}

void guardsToAtoms(const std::vector<ExtGuard>& guards, bool abstractLayer,
                   std::vector<ExtLemmaAtom>& out)
{
  for (size_t i = 0; i < guards.size(); i++)
  {
    const ExtGuard& g = guards[i];
    ExtLemmaAtom a;
    if (g.kind == ExtGuard::INDEX_NE)
    {
      a.op = ExtLemmaAtom::BV_NE;
      a.a = abstractLayer ? g.absA : g.theoryA;
      a.b = abstractLayer ? g.absB : g.theoryB;
      a.eqRecord = 0;
    }
    else if (g.kind == ExtGuard::ITE_COND_POS ||
             g.kind == ExtGuard::ITE_COND_NEG)
    {
      // The condition with the polarity sigma gave it. Unlike an array
      // equality, an if-then-else guard can be either way round: both
      // branches are selectable, and the rule fired on whichever one
      // sigma selected.
      a.op = g.kind == ExtGuard::ITE_COND_POS ? ExtLemmaAtom::BOOL_LIT
                                              : ExtLemmaAtom::BOOL_LIT_NEG;
      a.boolTerm = abstractLayer ? g.absA : g.theoryA;
      a.eqRecord = 0;
    }
    else if (abstractLayer)
    {
      a.op = ExtLemmaAtom::BOOL_LIT;
      a.boolTerm = g.absA;
      a.eqRecord = g.eqRecord;
    }
    else
    {
      a.op = ExtLemmaAtom::ARRAY_EQ;
      a.a = g.theoryA;
      a.b = g.theoryB;
      a.eqRecord = g.eqRecord;
    }
    out.push_back(a);
  }
}

// Self-check: a lemma is only worth adding if the candidate that
// produced it falsifies it — every premise atom must be true and the
// conclusion false under sigma. Otherwise adding it could not rule the
// candidate out and refinement might not terminate; abort loudly.
void validateAbstractLemma(const ExtConflict& c, ExtModelView& model)
{
  for (size_t i = 0; i < c.abstractPremise.size(); i++)
  {
    const ExtLemmaAtom& a = c.abstractPremise[i];
    bool holds;
    if (a.op == ExtLemmaAtom::BV_EQ)
      holds = model.bvValue(a.a) == model.bvValue(a.b);
    else if (a.op == ExtLemmaAtom::BV_NE)
      holds = model.bvValue(a.a) != model.bvValue(a.b);
    else if (a.op == ExtLemmaAtom::BOOL_LIT)
      holds = model.boolValue(a.boolTerm);
    else if (a.op == ExtLemmaAtom::BOOL_LIT_NEG)
      holds = !model.boolValue(a.boolTerm);
    else
      holds = false; // ARRAY_EQ can't appear in the abstract lemma
    if (!holds)
      FatalError("array-equality: generated lemma premise is not true "
                 "in the candidate assignment that produced it");
  }
  if (model.bvValue(c.abstractConclusionA) ==
      model.bvValue(c.abstractConclusionB))
    FatalError("array-equality: generated lemma is not false in the "
               "candidate assignment that produced it");
}

// Build the lemma of paper section 8 for a conflict between accesses
// x and y at common array d:
//
//   index(x) = index(y)
//     and the write-index disequalities of both propagation paths
//     and the array equalities crossed by both paths
//   =>  value(x) = value(y)
//
// built once over the original terms (the theory lemma) and once over
// abstraction variables and scalar names (the refinement actually
// encoded into the SAT solver).
void buildLemmas(ExtConflict& c, const ExtGraph& graph, ExtModelView& model)
{
  const ExtAccess& left = graph.accesses[c.leftAccess];
  const ExtAccess& right = graph.accesses[c.rightAccess];

  {
    std::vector<ExtLemmaAtom> atoms;
    ExtLemmaAtom indexEq;
    indexEq.op = ExtLemmaAtom::BV_EQ;
    indexEq.a = left.indexName;
    indexEq.b = right.indexName;
    indexEq.eqRecord = 0;
    atoms.push_back(indexEq);
    guardsToAtoms(c.leftGuards, true, atoms);
    guardsToAtoms(c.rightGuards, true, atoms);
    c.abstractPremise = canonicalAtoms(atoms);
    c.abstractConclusionA = left.valueName;
    c.abstractConclusionB = right.valueName;
  }

  {
    std::vector<ExtLemmaAtom> atoms;
    ExtLemmaAtom indexEq;
    indexEq.op = ExtLemmaAtom::BV_EQ;
    indexEq.a = left.indexTerm;
    indexEq.b = right.indexTerm;
    indexEq.eqRecord = 0;
    atoms.push_back(indexEq);
    guardsToAtoms(c.leftGuards, false, atoms);
    guardsToAtoms(c.rightGuards, false, atoms);
    c.theoryPremise = canonicalAtoms(atoms);
    c.theoryConclusionA = left.valueTerm;
    c.theoryConclusionB = right.valueTerm;
  }

  validateAbstractLemma(c, model);
}

} // namespace

ExtCheckResult ExtChecker::check(const ExtGraph& graph, ExtModelView& model,
                                 bool recordEvents)
{
  CheckerState st(graph, model, recordEvents);

  // Rule I: seed every access at its own array, with an empty
  // propagation path, in the stable access order.
  for (size_t i = 0; i < graph.accesses.size(); i++)
  {
    const ExtAccess& a = graph.accesses[i];
    const char* rule = a.isWrite ? "I_WRITE" : "I_READ";
    st.insert(a.site, a.id, std::vector<ExtGuard>(), rule, ASTNode());
  }

  // Fixed-point computation over a FIFO work list (the "working queue
  // that manages future read propagations" of section 7.3); for each
  // pair the edges fire in the order D, U, then R/L.
  //
  // The FIFO discipline is load-bearing: with every access seeded
  // before the fixed point starts, discovery is breadth-first per
  // access, so an access's recorded path to any array -- and in
  // particular the arrival that fires a conflict -- is a shortest
  // propagation path. That is the lemma minimization of section 11.1,
  // obtained without the separate post-conflict search a depth-first
  // (stack) working list would need. Pinned by the
  // ConflictPremiseUsesShortestPaths unit test; do not replace the
  // deque with a stack.
  while (!st.worklist.empty())
  {
    const PairKey cur = st.worklist.front();
    st.worklist.pop_front();
    const ASTNode source = cur.first;
    const size_t accessId = cur.second;
    // A copy, not a reference: st.insert adds entries to st.paths
    // while this record's edges are explored. A std::map keeps
    // existing elements stable, so a reference would work today; the
    // copy keeps the loop correct under any container choice.
    const PathRecord sourcePath = st.paths[cur];
    const ASTNode accessIdxVal = st.accessIndex(accessId);

    // Every rule fires for every pair: a conflict on one edge no longer
    // cuts the remaining edges short, so the pass collects the
    // independent conflicts an early return would have hidden.

    // Rule D: propagate down through a write whose index differs
    // from the access index under sigma (axiom A3).
    std::map<ASTNode, ExtWriteNode>::const_iterator wit =
        graph.writes.find(source);
    if (wit != graph.writes.end())
    {
      const ExtWriteNode& w = wit->second;
      if (accessIdxVal != model.bvValue(w.indexName))
      {
        ExtGuard g;
        g.kind = ExtGuard::INDEX_NE;
        g.theoryA = graph.accesses[accessId].indexTerm;
        g.theoryB = w.indexTerm;
        g.absA = graph.accesses[accessId].indexName;
        g.absB = w.indexName;
        g.eqRecord = 0;
        std::vector<ExtGuard> chi2 = sourcePath.guards;
        chi2.push_back(g);
        st.insert(w.base, accessId, chi2, "D_WRITE", source);
      }
    }

    // Rule U: propagate up over every write on top of this array
    // whose index differs from the access index under sigma. Upward
    // propagation is what makes extensional reasoning complete
    // (section 7.3).
    {
      std::map<ASTNode, std::vector<ASTNode>>::const_iterator pit =
          graph.writeParents.find(source);
      if (pit != graph.writeParents.end())
      {
        const std::vector<ASTNode>& parents = pit->second;
        for (size_t i = 0; i < parents.size(); i++)
        {
          const ExtWriteNode& w = graph.writes.find(parents[i])->second;
          if (accessIdxVal != model.bvValue(w.indexName))
          {
            ExtGuard g;
            g.kind = ExtGuard::INDEX_NE;
            g.theoryA = graph.accesses[accessId].indexTerm;
            g.theoryB = w.indexTerm;
            g.absA = graph.accesses[accessId].indexName;
            g.absB = w.indexName;
            g.eqRecord = 0;
            std::vector<ExtGuard> chi2 = sourcePath.guards;
            chi2.push_back(g);
            st.insert(w.write, accessId, chi2, "U_WRITE", source);
          }
        }
      }
    }

    // Rules R and L: propagate across array equalities, in both
    // directions, but only when sigma assigns the equality's Boolean
    // abstraction variable true.
    {
      std::map<ASTNode, std::vector<size_t>>::const_iterator eit =
          graph.eqAdjacency.find(source);
      if (eit != graph.eqAdjacency.end())
      {
        const std::vector<size_t>& adj = eit->second;
        for (size_t i = 0; i < adj.size(); i++)
        {
          const ExtEqEdge& e = graph.eqEdges[adj[i]];
          if (!model.boolValue(e.proxy))
            continue;
          const bool fromLeft = (e.left == source);
          const ASTNode destination = fromLeft ? e.right : e.left;
          const char* rule = fromLeft ? "R_EQ" : "L_EQ";
          ExtGuard g;
          g.kind = ExtGuard::EQ_PROXY;
          g.theoryA = e.left;
          g.theoryB = e.right;
          g.absA = e.proxy;
          g.eqRecord = e.record;
          std::vector<ExtGuard> chi2 = sourcePath.guards;
          chi2.push_back(g);
          st.insert(destination, accessId, chi2, rule, source);
        }
      }
    }

    // Rules T-down and T-up: propagate across an array-valued
    // if-then-else, in both directions, between it and whichever branch
    // sigma selects. These are R and L with the equality proxy replaced
    // by the condition literal and the destination chosen by sigma
    // rather than fixed by the edge. Exactly one of the two branches is
    // live per candidate, so unlike an equality there is no proxy left
    // over for the solver to guess.
    //
    // The condition is read through its reified name, never re-evaluated
    // from the counterexample: the value the rule branches on has to be
    // the one the bit-blasted circuit took, or the wrong edge is live
    // and a conflict-free fixed point certifies a model that does not
    // satisfy the if-then-else axiom.
    {
      // T-down: source is the if-then-else, destination its branch.
      std::map<ASTNode, ExtIteNode>::const_iterator dit =
          graph.ites.find(source);
      if (dit != graph.ites.end())
      {
        const ExtIteNode& t = dit->second;
        const bool cond = model.boolValue(t.condName);
        ExtGuard g;
        g.kind = cond ? ExtGuard::ITE_COND_POS : ExtGuard::ITE_COND_NEG;
        g.theoryA = t.condTerm;
        g.absA = t.condName;
        std::vector<ExtGuard> chi2 = sourcePath.guards;
        chi2.push_back(g);
        st.insert(cond ? t.thn : t.els, accessId, chi2, "T_DOWN", source);
      }

      // T-up: source is a branch, destination every if-then-else that
      // selects it.
      std::map<ASTNode, std::vector<ASTNode>>::const_iterator uit =
          graph.iteParents.find(source);
      if (uit != graph.iteParents.end())
      {
        const std::vector<ASTNode>& above = uit->second;
        for (size_t i = 0; i < above.size(); i++)
        {
          const ExtIteNode& t = graph.ites.find(above[i])->second;
          const bool cond = model.boolValue(t.condName);
          // Only from the selected branch. A branch can be both, in
          // which case either polarity carries the access up and the
          // first match is taken.
          if (!((cond && t.thn == source) || (!cond && t.els == source)))
            continue;
          ExtGuard g;
          g.kind = cond ? ExtGuard::ITE_COND_POS : ExtGuard::ITE_COND_NEG;
          g.theoryA = t.condTerm;
          g.absA = t.condName;
          std::vector<ExtGuard> chi2 = sourcePath.guards;
          chi2.push_back(g);
          st.insert(t.ite, accessId, chi2, "T_UP", source);
        }
      }
    }
  }

  // The fixed point ran to completion, so report every conflict it
  // found. Each is a lemma in its own right: its premise holds and its
  // conclusion fails under the one candidate sigma this pass ran
  // against, which does not change while the pass runs, so a conflict
  // found late is neither weakened nor invalidated by an earlier one.
  if (!st.result.conflicts.empty())
  {
    for (size_t i = 0; i < st.result.conflicts.size(); i++)
      buildLemmas(st.result.conflicts[i], graph, model);
    st.result.conflict = st.result.conflicts[0];
    st.result.status = ExtCheckResult::CONFLICT;
    return st.result;
  }

  // Verify the witnesses of preprocessing step 1, in record order: a
  // false array equality must differ at its witness index lambda.
  for (size_t i = 0; i < graph.witnesses.size(); i++)
  {
    const ExtWitness& w = graph.witnesses[i];
    const bool proxyVal = model.boolValue(w.proxy);
    const ASTNode leftVal = model.bvValue(w.leftValue);
    const ASTNode rightVal = model.bvValue(w.rightValue);
    st.event(ExtEvent::WITNESS_CHECK, "WITNESS", ASTNode(), ASTNode(),
             w.record, model.bvValue(w.index), leftVal);
    st.result.stats["witness_checks"]++;
    if (!proxyVal && leftVal == rightVal)
    {
      st.result.status = ExtCheckResult::WITNESS_VIOLATION;
      st.result.violatedRecord = w.record;
      return st.result;
    }
  }

  // Conflict-free: export the observed (index, value) pairs of every
  // array; rho's fixed point defines the completed array contents
  // (unobserved indices default to zero when a model is printed).
  for (std::map<ASTNode, std::vector<size_t>>::const_iterator it =
           st.rho.begin();
       it != st.rho.end(); ++it)
  {
    std::vector<std::pair<ASTNode, ASTNode>>& obs =
        st.result.observed[it->first];
    for (size_t i = 0; i < it->second.size(); i++)
    {
      const size_t id = it->second[i];
      obs.push_back(std::make_pair(st.accessIndex(id), st.accessValue(id)));
    }
  }

  st.result.status = ExtCheckResult::CONSISTENT;
  return st.result;
}

} // namespace stp
