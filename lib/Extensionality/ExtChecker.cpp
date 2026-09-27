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
#include "stp/STPManager/STPManager.h"
#include <algorithm>
#include <deque>
#include <set>
#include <unordered_map>
#include <utility>

namespace stp
{

namespace
{

typedef std::pair<ASTNode, size_t> PairKey;

typedef std::unordered_map<ASTNode, size_t, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    RhoIndexMap;

// One predecessor-linked shortest-path entry. A propagation stores exactly
// one incoming guard and a key for its predecessor; complete guard vectors are
// materialized only for the two paths of an emitted conflict. This preserves
// the FIFO/first-arrival shortest-path proof while making fixed-point storage
// linear in the number of reached (array, access) pairs.
struct PathRecord
{
  bool hasPredecessor = false;
  PairKey predecessor;
  ExtGuard incomingGuard;
};

struct CheckerState
{
  const ExtGraph& graph;
  ExtModelView& model;
  const bool recordEvents;

  std::map<PairKey, PathRecord> paths;
  // rho, split per section 11.2: one representative access per
  // concrete index of each array, keyed by the index value so a
  // congruence lookup is a single probe; plus the representatives in
  // insertion order, for the observed-contents export. rhoByIndex is
  // lookup-only: propagation, conflict, and model order must continue
  // to come from the deterministic graph/work-list order and rho vectors.
  std::map<ASTNode, RhoIndexMap> rhoByIndex;
  std::map<ASTNode, std::vector<size_t>> rho; // insertion order preserved
  std::deque<PairKey> worklist;
  ExtCheckResult result;
  size_t materializedGuardCount;
  // The accesses rule I mints for a constant array over a tiny index
  // sort (see check); numbered after the graph's own, and never part of
  // the frozen graph.
  std::vector<ExtAccess> synthetic;

  const ExtAccess& access(size_t id) const
  {
    return id < graph.accesses.size()
               ? graph.accesses[id]
               : synthetic[id - graph.accesses.size()];
  }

  CheckerState(const ExtGraph& g, ExtModelView& m, bool ev)
      : graph(g), model(m), recordEvents(ev), materializedGuardCount(0)
  {
  }

  ASTNode accessIndex(size_t id)
  {
    return model.bvValue(access(id).indexName);
  }

  ASTNode accessValue(size_t id)
  {
    return model.bvValue(access(id).valueName);
  }

  void event(ExtEvent::Kind kind, const char* rule, const ASTNode& source,
             const ASTNode& destination, size_t access)
  {
    if (!recordEvents)
      return;
    ExtEvent e;
    e.kind = kind;
    e.rule = rule;
    e.source = source;
    e.destination = destination;
    e.access = access;
    result.events.push_back(e);
  }

  // Walk one predecessor chain back to its seed, turning the stored
  // one-guard-per-link entries into the complete path a conflict
  // certificate reports.
  std::vector<ExtGuard> materializeGuards(const PathRecord& tail)
  {
    std::vector<ExtGuard> reversed;
    const PathRecord* current = &tail;
    while (current->hasPredecessor)
    {
      reversed.push_back(current->incomingGuard);
      materializedGuardCount++;
      const std::map<PairKey, PathRecord>::const_iterator predecessor =
          paths.find(current->predecessor);
      if (predecessor == paths.end())
        FatalError("array-equality: a proof path lost its predecessor");
      current = &predecessor->second;
    }
    std::reverse(reversed.begin(), reversed.end());
    return reversed;
  }

  void finishProofDiagnostics()
  {
    result.proofPathEntries = paths.size();
    result.materializedGuardCount = materializedGuardCount;
  }

  // Bring one access to one array, and run congruence (rule C) on the
  // spot, against the single representative rho keeps for that array
  // and concrete index (section 11.2).
  //
  // Three outcomes. An arrival at a pair already recorded is skipped:
  // insertion is first-path-wins and the recorded path stays. An
  // arrival matching the representative in both concrete index and
  // concrete value is dropped without insertion or propagation --
  // complete because no rule can tell members of a concrete
  // (index, value) class apart; see ExtChecker.h for why that is not
  // the same claim as "the representative reaches everything this
  // access would". Note that this one records nothing, so the same
  // access arriving again by another route repeats the test; the
  // counters below therefore count arrivals, not pairs. Otherwise the
  // access is inserted, becomes the representative if the index was
  // free, and is queued.
  //
  // A representative already there with a different concrete value is a
  // conflict: it is appended to result.conflicts (without the lemma,
  // which buildLemmas adds afterwards) and the pass carries on, so it
  // collects further independent conflicts instead of stopping at the
  // earliest. It does not enumerate every disagreeing pair in the
  // candidate -- a conflicting arrival is not queued, so pairs that
  // could only meet beyond it are left to a later refinement round.
  void insert(const ASTNode& destination, size_t accessId,
              const ExtGuard* incomingGuard, const char* rule,
              const ASTNode& source)
  {
    const PairKey key(destination, accessId);
    if (paths.find(key) != paths.end())
    {
      result.stats["skipped_seen"]++;
      event(ExtEvent::SKIP_SEEN, rule, source, destination, accessId);
      return;
    }

    PathRecord candidatePath;
    if (incomingGuard != NULL)
    {
      if (source.IsNull())
        FatalError("array-equality: a guarded proof step has no source");
      candidatePath.hasPredecessor = true;
      candidatePath.predecessor = PairKey(source, accessId);
      candidatePath.incomingGuard = *incomingGuard;
    }
    else if (!source.IsNull())
    {
      FatalError("array-equality: a non-seed proof step has no guard", source);
    }

    const ASTNode idx = accessIndex(accessId);
    const ASTNode val = accessValue(accessId);

    // Rule K: every cell of a constant array holds its default, so an
    // access arriving there must carry it. A disagreement is a conflict
    // whose lemma is the arriving path's guards implying that the access
    // value equals the default; as with rule C, the arrival is recorded
    // as seen and goes no further. An agreeing arrival is inserted as
    // usual, so rule C compares later arrivals at this index against a
    // representative that holds the default.
    {
      const std::map<ASTNode, ExtConstArray>::const_iterator kit =
          graph.constArrays.find(destination);
      if (kit != graph.constArrays.end() &&
          model.bvValue(kit->second.defaultName) != val)
      {
        ExtConflict c;
        c.shape = ExtConflict::CONST_DEFAULT;
        c.commonArray = destination;
        c.leftAccess = accessId;
        c.rightAccess = accessId;
        c.indexValue = idx;
        c.leftValue = model.bvValue(kit->second.defaultName);
        c.rightValue = val;
        c.rightGuards = materializeGuards(candidatePath);
        c.constTermA = kit->second.defaultTerm;
        c.constNameA = kit->second.defaultName;
        result.stats["conflicts"]++;
        result.stats["rule_K"]++;
        event(ExtEvent::CONFLICT, rule, source, destination, accessId);
        result.conflicts.push_back(std::move(c));
        paths[key] = candidatePath;
        return;
      }
    }

    RhoIndexMap& byIndex = rhoByIndex[destination];
    const std::pair<RhoIndexMap::iterator, bool> representative =
        byIndex.emplace(idx, accessId);
    if (!representative.second)
    {
      const size_t otherId = representative.first->second;
      if (accessValue(otherId) != val)
      {
        ExtConflict c;
        c.commonArray = destination;
        c.leftAccess = otherId;
        c.rightAccess = accessId;
        c.indexValue = idx;
        c.leftValue = accessValue(otherId);
        c.rightValue = val;
        const std::map<PairKey, PathRecord>::const_iterator otherPath =
            paths.find(PairKey(destination, otherId));
        if (otherPath == paths.end())
          FatalError("array-equality: rho representative has no proof path",
                     destination);
        c.leftGuards = materializeGuards(otherPath->second);
        c.rightGuards = materializeGuards(candidatePath);
        result.stats["conflicts"]++;
        event(ExtEvent::CONFLICT, rule, source, destination, accessId);
        result.conflicts.push_back(std::move(c));

        // Record the pair as visited so a later path to it cannot report
        // the same conflict twice, but keep the arriving access out of
        // rho -- its value disagrees with the representative already
        // there -- and out of the work list, so nothing propagates
        // onward from a conflicting arrival. The representative keeps
        // the array's slot for this index, exactly as when the pass
        // stopped here.
        //
        // This is what bounds the section 11.1 minimization to the
        // first conflict: the access's search tree ends here, so a
        // later conflict involving it uses whatever route remains, and
        // a pair that could only have met through this array is left
        // for a later refinement round. Queueing it instead would
        // restore exact minimization at the cost of an unbounded number
        // of further conflicts per pass, all derived from an already
        // refuted candidate.
        paths[key] = candidatePath;
        return;
      }
      result.stats["skipped_represented"]++;
      event(ExtEvent::SKIP_REPRESENTED, rule, source, destination,
            accessId);
      return;
    }

    paths[key] = candidatePath;
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
    event(kind, rule, source, destination, accessId);
  }
};

// Deterministic total order for premise atoms: rank by atom op
// (bv_eq < bv_ne < array_eq < bool_lit), then by operand node numbers.
bool atomLess(const ExtLemmaAtom& x, const ExtLemmaAtom& y)
{
  if (x.op != y.op)
    return x.op < y.op;
  uint64_t xa = x.a.IsNull() ? 0 : x.a.GetNodeNum();
  uint64_t ya = y.a.IsNull() ? 0 : y.a.GetNodeNum();
  if (xa != ya)
    return xa < ya;
  uint64_t xb = x.b.IsNull() ? 0 : x.b.GetNodeNum();
  uint64_t yb = y.b.IsNull() ? 0 : y.b.GetNodeNum();
  if (xb != yb)
    return xb < yb;
  uint64_t xt = x.boolTerm.IsNull() ? 0 : x.boolTerm.GetNodeNum();
  uint64_t yt = y.boolTerm.IsNull() ? 0 : y.boolTerm.GetNodeNum();
  return xt < yt;
}

// Canonicalize a premise: drop reflexive equalities (an index compared
// with itself contributes nothing), drop exact duplicate atoms, and
// sort deterministically. The guard paths feeding this are as short as
// the pass could make them (section 11.1, a property of the FIFO work
// list -- exactly shortest for the first conflict, and shortest among
// the routes still open for a later one; see ExtChecker.h); beyond
// that only exact duplicates are removed, no semantic subsumption.
std::vector<ExtLemmaAtom> canonicalAtoms(const std::vector<ExtLemmaAtom>& in)
{
  std::vector<ExtLemmaAtom> out;
  out.reserve(in.size());
  for (size_t i = 0; i < in.size(); i++)
  {
    const ExtLemmaAtom& a = in[i];
    if (a.op == ExtLemmaAtom::BV_EQ && a.a == a.b)
      continue;
    out.push_back(a);
  }
  // Preserve which input occurrence survives when two logical atoms
  // compare equal. ExtLemmaAtom carries proof metadata outside atomLess
  // and operator==, so an unstable sort would make that choice incidental.
  std::stable_sort(out.begin(), out.end(), atomLess);
  out.erase(std::unique(out.begin(), out.end()), out.end());
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
// The two constant-array shapes (see ExtConflict::Shape) have no index
// equality and one path: rule K's lemma is the arriving path's guards
// implying value(access) = default; rule K''s is the connecting path's
// guards implying default = default.
void buildLemmas(ExtConflict& c, const ExtGraph& graph,
                 const std::vector<ExtAccess>& synthetic, ExtModelView& model)
{
  const auto access = [&](size_t id) -> const ExtAccess& {
    return id < graph.accesses.size() ? graph.accesses[id]
                                      : synthetic[id - graph.accesses.size()];
  };

  if (c.shape == ExtConflict::CONST_DEFAULT)
  {
    const ExtAccess& right = access(c.rightAccess);
    std::vector<ExtLemmaAtom> atoms;
    guardsToAtoms(c.rightGuards, true, atoms);
    c.abstractPremise = canonicalAtoms(atoms);
    c.abstractConclusionA = right.valueName;
    c.abstractConclusionB = c.constNameA;
    atoms.clear();
    guardsToAtoms(c.rightGuards, false, atoms);
    c.theoryPremise = canonicalAtoms(atoms);
    c.theoryConclusionA = right.valueTerm;
    c.theoryConclusionB = c.constTermA;
    validateAbstractLemma(c, model);
    return;
  }
  if (c.shape == ExtConflict::CONST_PAIR)
  {
    std::vector<ExtLemmaAtom> atoms;
    guardsToAtoms(c.leftGuards, true, atoms);
    c.abstractPremise = canonicalAtoms(atoms);
    c.abstractConclusionA = c.constNameA;
    c.abstractConclusionB = c.constNameB;
    atoms.clear();
    guardsToAtoms(c.leftGuards, false, atoms);
    c.theoryPremise = canonicalAtoms(atoms);
    c.theoryConclusionA = c.constTermA;
    c.theoryConclusionB = c.constTermB;
    validateAbstractLemma(c, model);
    return;
  }

  const ExtAccess& left = access(c.leftAccess);
  const ExtAccess& right = access(c.rightAccess);

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

// An index sort with no more values than the graph has writes: a path
// between two constant arrays could then address every cell, so rule K'
// (which needs an index no write on the path touches) does not apply, and
// the cells of such an array are made explicit instead.
bool tinyIndexDomain(unsigned indexWidth, size_t writeCount)
{
  return indexWidth < 64 && (uint64_t(1) << indexWidth) <= writeCount;
}

// The arrays a candidate connects, for rule K' and the completion: a
// write and its base agree everywhere but at the write's index, the two
// sides of an equality sigma assigns true everywhere, an if-then-else and
// the branch sigma selects everywhere. Edges carry the guard a lemma
// premise states for crossing them (none for a write) and whether they
// cross a write.
struct ComponentEdge
{
  ASTNode to;
  bool guarded = false;
  bool crossesWrite = false;
  ExtGuard guard;
};

struct ComponentGraph
{
  std::map<ASTNode, std::vector<ComponentEdge>> adjacency;

  ComponentGraph(const ExtGraph& graph, ExtModelView& model)
  {
    for (std::map<ASTNode, ExtWriteNode>::const_iterator it =
             graph.writes.begin();
         it != graph.writes.end(); ++it)
    {
      ComponentEdge down, up;
      down.to = it->second.base;
      down.crossesWrite = true;
      up.to = it->second.write;
      up.crossesWrite = true;
      adjacency[it->second.write].push_back(down);
      adjacency[it->second.base].push_back(up);
    }
    for (size_t i = 0; i < graph.eqEdges.size(); i++)
    {
      const ExtEqEdge& e = graph.eqEdges[i];
      if (!model.boolValue(e.proxy))
        continue;
      ComponentEdge edge;
      edge.guarded = true;
      edge.guard.kind = ExtGuard::EQ_PROXY;
      edge.guard.theoryA = e.left;
      edge.guard.theoryB = e.right;
      edge.guard.absA = e.proxy;
      edge.guard.eqRecord = e.record;
      edge.to = e.right;
      adjacency[e.left].push_back(edge);
      edge.to = e.left;
      adjacency[e.right].push_back(edge);
    }
    for (std::map<ASTNode, ExtIteNode>::const_iterator it = graph.ites.begin();
         it != graph.ites.end(); ++it)
    {
      const ExtIteNode& t = it->second;
      const bool cond = model.boolValue(t.condName);
      ComponentEdge edge;
      edge.guarded = true;
      edge.guard.kind = cond ? ExtGuard::ITE_COND_POS : ExtGuard::ITE_COND_NEG;
      edge.guard.theoryA = t.condTerm;
      edge.guard.absA = t.condName;
      const ASTNode branch = cond ? t.thn : t.els;
      edge.to = branch;
      adjacency[t.ite].push_back(edge);
      edge.to = t.ite;
      adjacency[branch].push_back(edge);
    }
  }

  // Breadth-first from `from`, in adjacency order: every node reached,
  // and for each the edge it was reached through, keyed by the node.
  void component(const ASTNode& from, std::vector<ASTNode>& reached,
                 std::map<ASTNode, std::pair<ASTNode, ComponentEdge>>& via)
  {
    reached.clear();
    via.clear();
    std::deque<ASTNode> queue;
    std::set<ASTNode> seen;
    queue.push_back(from);
    seen.insert(from);
    while (!queue.empty())
    {
      const ASTNode current = queue.front();
      queue.pop_front();
      reached.push_back(current);
      const std::map<ASTNode, std::vector<ComponentEdge>>::const_iterator
          it = adjacency.find(current);
      if (it == adjacency.end())
        continue;
      for (size_t i = 0; i < it->second.size(); i++)
      {
        const ComponentEdge& e = it->second[i];
        if (!seen.insert(e.to).second)
          continue;
        via[e.to] = std::make_pair(current, e);
        queue.push_back(e.to);
      }
    }
  }

  // The guards of the path `via` recorded from the search's origin to
  // `to`, origin first, and the number of writes it crosses.
  static void pathGuards(
      const std::map<ASTNode, std::pair<ASTNode, ComponentEdge>>& via,
      const ASTNode& to, std::vector<ExtGuard>& guards, size_t& writes)
  {
    guards.clear();
    writes = 0;
    ASTNode current = to;
    while (true)
    {
      const std::map<ASTNode, std::pair<ASTNode, ComponentEdge>>::
          const_iterator it = via.find(current);
      if (it == via.end())
        break;
      if (it->second.second.guarded)
        guards.push_back(it->second.second.guard);
      if (it->second.second.crossesWrite)
        writes++;
      current = it->second.first;
    }
    std::reverse(guards.begin(), guards.end());
  }
};

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
    st.insert(a.site, a.id, NULL, rule, ASTNode());
  }

  // Rule I for a constant array over a tiny index sort (see
  // tinyIndexDomain): one synthetic access per index value, carrying the
  // default, seeded at the array. Every cell of such an array is then an
  // ordinary access the other rules propagate, so rules K and C decide
  // between two constant arrays what rule K' below decides for the
  // larger sorts. The index terms are the plain constants, which the
  // model view answers directly; minting them in the host manager
  // creates no term of the query.
  for (std::map<ASTNode, ExtConstArray>::const_iterator it =
           graph.constArrays.begin();
       it != graph.constArrays.end(); ++it)
  {
    const unsigned w = it->second.array.GetIndexWidth();
    if (!tinyIndexDomain(w, graph.writes.size()))
      continue;
    STPMgr* bm = it->second.array.GetNodeManager();
    const uint64_t count = uint64_t(1) << w;
    for (uint64_t k = 0; k < count; k++)
    {
      ExtAccess a;
      a.id = graph.accesses.size() + st.synthetic.size();
      a.isWrite = false;
      a.site = it->second.array;
      a.indexTerm = bm->CreateBVConst(w, k);
      a.indexName = a.indexTerm;
      a.valueTerm = it->second.defaultTerm;
      a.valueName = it->second.defaultName;
      st.synthetic.push_back(a);
      st.insert(it->second.array, a.id, NULL, "I_CONST", ASTNode());
    }
  }

  // Fixed-point computation over a FIFO work list (the "working queue
  // that manages future read propagations" of section 7.3); for each
  // pair the edges fire in the order D, U, R/L, then the T rules.
  //
  // The FIFO discipline is load-bearing: with every access seeded
  // before the fixed point starts, discovery is breadth-first per
  // access, so an access's recorded path to any array is a shortest
  // propagation path among the routes still open to it. That is the
  // lemma minimization of section 11.1, obtained without the separate
  // post-conflict search a depth-first (stack) working list would need.
  //
  // "Still open" because a conflicting arrival is not queued (see
  // insert), so an access stops at an array it conflicted at. The first
  // conflict of a pass is unaffected -- nothing has been truncated when
  // it fires -- but a later one can carry a longer premise than an
  // exhaustive search would give it. Pinned at both ends by the
  // ConflictPremiseUsesShortestPaths and
  // ConflictingArrivalStopsAtTheConflictArray unit tests; do not
  // replace the deque with a stack.
  while (!st.worklist.empty())
  {
    const PairKey cur = st.worklist.front();
    st.worklist.pop_front();
    const ASTNode source = cur.first;
    const size_t accessId = cur.second;
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
        g.theoryA = st.access(accessId).indexTerm;
        g.theoryB = w.indexTerm;
        g.absA = st.access(accessId).indexName;
        g.absB = w.indexName;
        g.eqRecord = 0;
        st.insert(w.base, accessId, &g, "D_WRITE", source);
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
            g.theoryA = st.access(accessId).indexTerm;
            g.theoryB = w.indexTerm;
            g.absA = st.access(accessId).indexName;
            g.absB = w.indexName;
            g.eqRecord = 0;
            st.insert(w.write, accessId, &g, "U_WRITE", source);
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
          st.insert(destination, accessId, &g, rule, source);
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
        st.insert(cond ? t.thn : t.els, accessId, &g, "T_DOWN", source);
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
          st.insert(t.ite, accessId, &g, "T_UP", source);
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
      buildLemmas(st.result.conflicts[i], graph, st.synthetic, model);
    st.result.conflict = st.result.conflicts[0];
    st.result.status = ExtCheckResult::CONFLICT;
    st.finishProofDiagnostics();
    return std::move(st.result);
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
             w.record);
    st.result.stats["witness_checks"]++;
    if (!proxyVal && leftVal == rightVal)
    {
      st.result.status = ExtCheckResult::WITNESS_VIOLATION;
      st.result.violatedRecord = w.record;
      st.finishProofDiagnostics();
      return std::move(st.result);
    }
  }

  // Rule K' and the completion. The arrays the candidate connects (see
  // ComponentGraph) hold one value at every cell no access observes. Two
  // constant arrays in one component with different defaults contradict
  // that: they agree at every index no write on the path between them
  // addresses, and an index sort with more values than the graph has
  // writes always has such an index (the others were made explicit
  // above), so the path's guards imply the two defaults are equal -- a
  // lemma the candidate falsifies. A component with one default hands it
  // to every array in it as the value of its unobserved cells: the
  // completion the model publishes, without which an array equated with
  // a constant array would print with the ordinary zero fill and the
  // printed model would not satisfy the equality.
  if (!graph.constArrays.empty())
  {
    ComponentGraph components(graph, model);
    std::set<ASTNode> placed;
    std::vector<ASTNode> reached;
    std::map<ASTNode, std::pair<ASTNode, ComponentEdge>> via;
    for (std::map<ASTNode, ExtConstArray>::const_iterator it =
             graph.constArrays.begin();
         it != graph.constArrays.end(); ++it)
    {
      if (placed.find(it->first) != placed.end())
        continue;
      components.component(it->first, reached, via);
      const ASTNode origin = model.bvValue(it->second.defaultName);
      const unsigned w = it->second.array.GetIndexWidth();
      const bool explicitCells = tinyIndexDomain(w, graph.writes.size());
      for (size_t i = 0; i < reached.size(); i++)
      {
        const std::map<ASTNode, ExtConstArray>::const_iterator other =
            graph.constArrays.find(reached[i]);
        if (other == graph.constArrays.end())
          continue;
        placed.insert(reached[i]);
        if (explicitCells || reached[i] == it->first ||
            model.bvValue(other->second.defaultName) == origin)
          continue;
        ExtConflict c;
        c.shape = ExtConflict::CONST_PAIR;
        c.commonArray = reached[i];
        c.leftAccess = 0;
        c.rightAccess = 0;
        c.leftValue = origin;
        c.rightValue = model.bvValue(other->second.defaultName);
        size_t writesCrossed = 0;
        ComponentGraph::pathGuards(via, reached[i], c.leftGuards,
                                   writesCrossed);
        if (tinyIndexDomain(w, writesCrossed))
          FatalError("array-equality: rule K' met a path with more writes "
                     "than the index sort has values",
                     reached[i]);
        c.constTermA = it->second.defaultTerm;
        c.constNameA = it->second.defaultName;
        c.constTermB = other->second.defaultTerm;
        c.constNameB = other->second.defaultName;
        st.result.stats["conflicts"]++;
        st.result.stats["rule_K_prime"]++;
        st.event(ExtEvent::CONFLICT, "K_PRIME", it->first, reached[i], 0);
        st.result.conflicts.push_back(std::move(c));
      }
      if (st.result.conflicts.empty())
        for (size_t i = 0; i < reached.size(); i++)
          st.result.completion[reached[i]] = origin;
    }
    if (!st.result.conflicts.empty())
    {
      for (size_t i = 0; i < st.result.conflicts.size(); i++)
        buildLemmas(st.result.conflicts[i], graph, st.synthetic, model);
      st.result.conflict = st.result.conflicts[0];
      st.result.status = ExtCheckResult::CONFLICT;
      st.result.completion.clear();
      st.finishProofDiagnostics();
      return std::move(st.result);
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
  st.finishProofDiagnostics();
  return std::move(st.result);
}

} // namespace stp
