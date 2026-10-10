/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: October, 2026
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

#include "stp/Simplifier/MutableGraph.h"
#include "stp/AST/ASTInterior.h"
#include <algorithm>
#include <climits>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <string>

namespace stp
{

static const char* matReason_ = "api";

// Public operations nest (a patch can merge, a merge patches parents).
// Settling stale children waits for the outermost one to finish.
struct MutableGraphNest
{
  MutableGraph& g;
  explicit MutableGraphNest(MutableGraph& graph) : g(graph) { g.depth_++; }
  ~MutableGraphNest()
  {
    if (--g.depth_ == 0)
      g.settle();
  }
};

namespace
{
bool anyMutable(ASTChildren children)
{
  for (const ASTNode& c : children)
    if (c.isMutableInterior())
      return true;
  return false;
}

// The order the hashing factory gives commutative children, so that two
// nodes with the same children in different orders are the same key.
void sortCommutative(Kind kind, ASTVec& kids)
{
  if (kids.size() <= 1 || !isCommutative(kind))
    return;
  if (is_Form_kind(kind))
    SortByExprNum(kids);
  else
    SortByArith(kids);
}

// Create through the manager's hashing factory with the sort a node of this
// type carries.
ASTNode hashCons(STPMgr& bm, Kind kind, unsigned index, unsigned width,
                 unsigned exp, unsigned sig, const ASTVec& children)
{
  ASTNode r;
  if (index > 0)
    r = bm.hashingNodeFactory->CreateArrayTerm(kind, index, width, children);
  else if (width > 0)
    r = bm.hashingNodeFactory->CreateTerm(kind, width, children);
  else
    r = bm.hashingNodeFactory->CreateNode(kind, children);
  // A float format is stamped only where a node can hold one (a leaf, a
  // float operation, an array); elsewhere it is derived from the children,
  // and the copy carried the derived value.
  if ((exp > 0 || sig > 0) && r.canStoreFPFormat())
  {
    r.SetExpWidth(exp);
    r.SetSigWidth(sig);
  }
  return r;
}
} // namespace

// ---------------------------------------------------------------- factory

// Sorting and NOT handling mirror HashingNodeFactory. A structure that
// already exists as a mutable node is that node, whether or not its
// children are mutable; only a structure the graph does not hold goes to
// the manager, and only when none of its children is mutable.

ASTNode MutableNodeFactory::CreateNode(Kind kind, ASTChildren given)
{
  ASTVec kids;
  graph.normalise(given, kids);
  if (kind == NOT && kids[0].GetKind() == NOT)
    return kids[0][0];
  if (kids.size() > 1 && isCommutative(kind))
    SortByExprNum(kids);
  return graph.lookupOrCreate(kind, 0, 0, ASTChildren(kids.data(), kids.size()));
}

ASTNode MutableNodeFactory::CreateTerm(Kind kind, unsigned int width,
                                       ASTChildren given)
{
  ASTVec kids;
  graph.normalise(given, kids);
  if (kids.size() > 1 && isCommutative(kind))
    SortByArith(kids);
  return graph.lookupOrCreate(kind, 0, width, ASTChildren(kids.data(), kids.size()));
}

ASTNode MutableNodeFactory::CreateArrayTerm(Kind kind, unsigned int index,
                                            unsigned int width,
                                            ASTChildren given)
{
  ASTVec kids;
  graph.normalise(given, kids);
  return graph.lookupOrCreate(kind, index, width,
                              ASTChildren(kids.data(), kids.size()));
}

// ------------------------------------------------------------------ table

size_t MutableGraph::Hasher::operator()(const MutableInterior* n) const
{
  return operator()(Probe{n->GetKind(), n->GetChildren()});
}

size_t MutableGraph::Hasher::operator()(const Probe& p) const
{
  size_t h = static_cast<size_t>(p.kind) * 0x9E3779B97F4A7C15ULL;
  for (const ASTNode& c : p.children)
    h = (h ^ identity(c)) * 0x100000001B3ULL;
  return h;
}

bool MutableGraph::Equal::operator()(const MutableInterior* a,
                                     const MutableInterior* b) const
{
  return a->GetKind() == b->GetKind() && a->GetChildren() == b->GetChildren();
}

bool MutableGraph::Equal::operator()(const Probe& p,
                                     const MutableInterior* n) const
{
  return p.kind == n->GetKind() && p.children == n->GetChildren();
}

// Erase by identity. The table is keyed by structure, and a node that has
// already left the table (an enclosing patch took it out) may have a live
// twin with the same structure in it; a plain erase would take the twin.
bool MutableGraph::eraseFromTable(MutableInterior* m)
{
  // A wide node is never in the table, and hashing one costs its width:
  // a 100,000-way conjunction patched once per eliminated conjunct would
  // be quadratic through the probe alone.
  if (m->wide_)
    return false;
  const auto it = table_.find(m);
  if (it == table_.end() || *it != m)
    return false;
  table_.erase(it);
  return true;
}

// ------------------------------------------------------------- lifecycle

MutableGraph::MutableGraph(STPMgr& bm_)
    : bm(bm_), trace_(std::getenv("MUTABLEGRAPH_TRACE") != NULL),
      raw_(bm_, *this), simplifying_(raw_, bm_),
      normalising_(bm_, *this, simplifying_)
{
}

ASTNode NormalisingNodeFactory::CreateNode(Kind kind, ASTChildren given)
{
  ASTVec kids;
  graph.normalise(given, kids);
  return inner.CreateNode(kind, ASTChildren(kids.data(), kids.size()));
}

ASTNode NormalisingNodeFactory::CreateTerm(Kind kind, unsigned int width,
                                           ASTChildren given)
{
  ASTVec kids;
  graph.normalise(given, kids);
  return inner.CreateTerm(kind, width, ASTChildren(kids.data(), kids.size()));
}

ASTNode NormalisingNodeFactory::CreateArrayTerm(Kind kind, unsigned int index,
                                                unsigned int width,
                                                ASTChildren given)
{
  ASTVec kids;
  graph.normalise(given, kids);
  return inner.CreateArrayTerm(kind, index, width,
                               ASTChildren(kids.data(), kids.size()));
}

#define MG_TRACE(x)                                                            \
  do                                                                           \
  {                                                                            \
    if (trace_)                                                                \
      std::cerr << "  [graph] " << x << std::endl;                             \
  } while (0)

MutableGraph::~MutableGraph()
{
  tearingDown_ = true;
  table_.clear();
  for (const ASTNode& n : owned_)
    asMutable(n)->graph_ = NULL;
  // Children handles hold the nodes they point at, so releasing in creation
  // order frees each node after everything it was built from is already
  // unreferenced by the graph: no node is freed while a child vector that
  // mentions it still exists.
  owned_.clear();
}

void MutableGraph::released(MutableInterior*)
{
  // owned_ holds a handle on every node for the graph's lifetime, so the
  // last handle only goes during teardown, after graph_ is cleared. Nothing
  // to do here; the hook exists so a node knows it may free itself.
}

MutableInterior* MutableGraph::asMutable(const ASTNode& n)
{
  if (!n.isMutableInterior())
    return NULL;
  return static_cast<MutableInterior*>(n._int_node_ptr);
}

// ----------------------------------------------------------------- import

void MutableGraph::import(const ASTNode& root)
{
  assert(owned_.empty()); // one import per graph
  root_ = root;

  // Every node reachable from the root, each once, with every parent edge
  // (a child used twice by one parent is two edges).
  std::vector<std::pair<uint32_t, uint32_t>> edges; // (child, parent)
  std::vector<ASTNode> stack;
  stack.push_back(root);
  indexOf(root);
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    const uint32_t p = index_[n.GetNodeNum()];
    for (const ASTNode& c : n.GetChildren())
    {
      uint32_t ci;
      const bool seen = indexed(c, ci);
      if (!seen)
      {
        ci = indexOf(c);
        stack.push_back(c);
      }
      edges.push_back({ci, p});
    }
  }

  imported_ = nodes_.size();
  if (trace_ && edges.size() < 60)
    for (const auto& e : edges)
      MG_TRACE("import edge " << nodes_[e.first].GetNodeNum() << " <- parent "
                              << nodes_[e.second].GetNodeNum());
  offsets_.assign(imported_ + 1, 0);
  for (const auto& e : edges)
    offsets_[e.first + 1]++;
  for (uint32_t i = 0; i < imported_; i++)
    offsets_[i + 1] += offsets_[i];
  csrParents_.assign(edges.size(), 0);
  {
    std::vector<uint32_t> fill(offsets_.begin(), offsets_.end() - 1);
    for (const auto& e : edges)
      csrParents_[fill[e.first]++] = e.second;
  }
  liveImm_.assign(imported_, 0);
  stale_.assign(imported_, false);
  for (uint32_t i = 0; i < imported_; i++)
    liveImm_[i] = offsets_[i + 1] - offsets_[i];
  liveImm_[index_[root.GetNodeNum()]] += 1; // the root is held by the query
}

uint32_t MutableGraph::indexOf(const ASTNode& n)
{
  assert(!n.isMutableInterior());
  const auto it = index_.find(n.GetNodeNum());
  if (it != index_.end())
    return it->second;
  const uint32_t idx = nodes_.size();
  nodes_.push_back(n);
  index_.emplace(n.GetNodeNum(), idx);
  if (idx >= imported_ || offsets_.empty())
    liveImm_.push_back(0);
  stale_.push_back(false);
  return idx;
}

bool MutableGraph::indexed(const ASTNode& n, uint32_t& idx) const
{
  if (n.isMutableInterior())
    return false; // a copy carries its original's number
  const auto it = index_.find(n.GetNodeNum());
  if (it == index_.end())
    return false;
  idx = it->second;
  return true;
}

// ----------------------------------------------------------------- counts

bool MutableGraph::liveImmutable(uint32_t idx) const
{
  const ASTNode& n = nodes_[idx];
  if (isForwarded(n))
    return false;
  // Its own parents, mutable parents, and the parents of nodes it stands for.
  return immutableParentCount(n) > 0;
}

size_t MutableGraph::originParentCount(
    const std::vector<uint64_t>& origins) const
{
  size_t count = 0;
  for (uint64_t o : origins)
  {
    const auto it = index_.find(o);
    assert(it != index_.end());
    count += liveImm_[it->second];
    // Mutable parents that still hold the origin's handle: materialise
    // repoints them, and until it has they are this node's parents.
    const auto mp = mutParents_.find(o);
    if (mp != mutParents_.end())
      count += mp->second.size();
  }
  return count;
}

size_t MutableGraph::immutableParentCount(const ASTNode& n) const
{
  uint32_t idx;
  size_t count = 0;
  if (indexed(n, idx))
    count += liveImm_[idx];
  const auto m = mutParents_.find(n.GetNodeNum());
  if (m != mutParents_.end())
    count += m->second.size();
  const auto o = immOrigins_.find(n.GetNodeNum());
  if (o != immOrigins_.end())
    count += originParentCount(o->second);
  return count;
}

size_t MutableGraph::parentCount(const ASTNode& node) const
{
  const ASTNode n = current(node);
  if (const MutableInterior* m = asMutable(n))
  {
    if (m->dead_)
      return 0;
    return m->parents_.size() + originParentCount(m->origins_);
  }
  return immutableParentCount(n);
}

void MutableGraph::parents(const ASTNode& node, std::vector<ASTNode>& out) const
{
  const ASTNode n = current(node);
  const std::vector<uint64_t>* origins = NULL;
  if (const MutableInterior* m = asMutable(n))
  {
    if (m->dead_)
      return;
    for (MutableInterior* p : m->parents_)
      out.push_back(ASTNode(p));
    origins = &m->origins_;
  }
  else
  {
    const auto mp = mutParents_.find(n.GetNodeNum());
    if (mp != mutParents_.end())
      for (MutableInterior* p : mp->second)
        out.push_back(ASTNode(p));
    const auto io = immOrigins_.find(n.GetNodeNum());
    if (io != immOrigins_.end())
      origins = &io->second;
  }

  // Live immutable parents, of the node itself and of the nodes it stands
  // for. Every immutable node's parents are listed by CSR and extra edges.
  auto listImmutable = [this, &out](uint64_t uid) {
    const auto it = index_.find(uid);
    if (it == index_.end())
      return;
    const uint32_t idx = it->second;
    if (idx < imported_)
      for (uint32_t k = offsets_[idx]; k < offsets_[idx + 1]; k++)
        if (liveImmutable(csrParents_[k]))
          out.push_back(nodes_[csrParents_[k]]);
    const auto ex = extraParents_.find(uid);
    if (ex != extraParents_.end())
      for (uint32_t p : ex->second)
        if (liveImmutable(p))
          out.push_back(nodes_[p]);
  };
  if (!n.isMutableInterior())
    listImmutable(n.GetNodeNum());
  if (origins != NULL)
    for (uint64_t o : *origins)
      listImmutable(o);
}

ASTNode MutableGraph::current(const ASTNode& n) const
{
  ASTNode c = n;
  while (true)
  {
    // A NOT's number is reused by the NOT that replaces it, so a mutable
    // node's forward is consulted only when that node is dead.
    if (c.isMutableInterior())
    {
      const MutableInterior* m = asMutable(c);
      if (!m->dead_)
        break;
      const auto it = mutForward_.find(m);
      if (it == mutForward_.end())
        break;
      c = it->second;
      continue;
    }
    const auto it = forward_.find(c.GetNodeNum());
    if (it == forward_.end())
      break;
    c = it->second;
  }
  return c;
}

bool MutableGraph::isStale(const ASTNode& n) const
{
  uint32_t idx;
  return indexed(n, idx) && stale_[idx];
}

// idx has just been replaced (or stands above a replacement): every
// immutable node above it still points at old structure.
void MutableGraph::markStaleAbove(uint32_t start)
{
  std::vector<uint32_t> up;
  up.push_back(start);
  while (!up.empty())
  {
    const uint32_t idx = up.back();
    up.pop_back();
    auto visit = [&](uint32_t p) {
      if (!stale_[p])
      {
        MG_TRACE("  stale: " << nodes_[p].GetNodeNum() << " (above " << nodes_[idx].GetNodeNum() << ")");
        stale_[p] = true;
        up.push_back(p);
        pendingStale_.push_back(p);
        std::push_heap(pendingStale_.begin(), pendingStale_.end(), staleAfter_);
      }
    };
    if (idx < imported_)
      for (uint32_t k = offsets_[idx]; k < offsets_[idx + 1]; k++)
        visit(csrParents_[k]);
    const auto ex = extraParents_.find(nodes_[idx].GetNodeNum());
    if (ex != extraParents_.end())
      for (uint32_t p : ex->second)
        visit(p);
  }
}

void MutableGraph::settle()
{
  // Hold the depth by hand: a guard here would call settle again when it
  // went out of scope. The materialise calls below nest under this count.
  depth_++;
  MG_TRACE("settle: " << pendingStale_.size() << " pending, depth " << depth_);
  while (!pendingStale_.empty() || !dirty_.empty())
  {
    if (pendingStale_.empty())
    {
      drainDirty();
      continue;
    }
    // Lowest number first: an immutable node outnumbers its children, so
    // a stale node is converted after every stale node below it and the
    // conversion of a 20,000-deep chain does not recurse through it.
    std::pop_heap(pendingStale_.begin(), pendingStale_.end(), staleAfter_);
    const uint32_t idx = pendingStale_.back();
    pendingStale_.pop_back();
    const ASTNode n = nodes_[idx];
    MG_TRACE("settle " << n.GetNodeNum() << " forwarded " << isForwarded(n)
                       << " stale " << stale_[idx]);
    if (isForwarded(n) || !stale_[idx])
      continue;
    if (!liveImmutable(idx) && !isRoot(n))
      continue; // out of the formula: rebuilt if it ever comes back
    matReason_ = "settle";
    materialise(n);
  }
  depth_--;
}

// ------------------------------------------------------------------ edges

void MutableGraph::registerParentEdge(MutableInterior* parent,
                                      const ASTNode& given)
{
  // A detached node may have gone stale; refreshed (recursively) here, so
  // attach below only ever walks current children.
  const ASTNode child = normalise(given);
  const size_t before = parentCount(child);
  if (MutableInterior* m = asMutable(child))
    m->parents_.push_back(parent);
  else
  {
    indexOf(child);
    mutParents_[child.GetNodeNum()].push_back(parent);
  }
  note(Change::CountChanged, child);
  if (before == 0)
    attach(child);
}

void MutableGraph::unregisterParentEdge(MutableInterior* parent,
                                        const ASTNode& child)
{
  if (MutableInterior* m = asMutable(child))
  {
    auto& ps = m->parents_;
    const auto it = std::find(ps.begin(), ps.end(), parent);
    assert(it != ps.end());
    ps.erase(it);
  }
  else
  {
    auto& ps = mutParents_[child.GetNodeNum()];
    const auto it = std::find(ps.begin(), ps.end(), parent);
    assert(it != ps.end());
    ps.erase(it);
  }
  note(Change::CountChanged, child);
  if (parentCount(child) == 0 && !isRoot(child))
    detach(child);
}

// n has just gained its first parent: its own child edges now count. Walks
// down, continuing through any child that this brings into the formula.
void MutableGraph::attach(const ASTNode& start)
{
  std::vector<ASTNode> stack;
  stack.push_back(start);
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    note(Change::Attached, n);
    if (MutableInterior* m = asMutable(n))
    {
      assert(!m->dead_);
      if (m->attached_)
        continue;
      m->attached_ = true;
      // Not via registerParentEdge: the child's first-parent walk is this
      // loop's job, so the push happens here.
      for (const ASTNode& c : m->children_)
      {
        assert(current(c) == c); // normalise() refreshed any temporary
        const size_t before = parentCount(c);
        if (MutableInterior* mc = asMutable(c))
          mc->parents_.push_back(m);
        else
        {
          indexOf(c);
          mutParents_[c.GetNodeNum()].push_back(m);
        }
        note(Change::CountChanged, c);
        if (before == 0)
          stack.push_back(c);
      }
    }
    else
    {
      const uint32_t idx = indexOf(n);
      const bool fresh = idx >= imported_;
      for (const ASTNode& c : n.GetChildren())
      {
        // Built through the graph's factory, so over current children.
        assert(!fresh || (!isForwarded(c) && !isStale(c)));
        const size_t before = parentCount(c);
        const uint32_t ci = indexOf(c);
        liveImm_[ci]++;
        if (fresh)
          extraParents_[c.GetNodeNum()].push_back(idx);
        note(Change::CountChanged, c);
        if (before == 0)
          stack.push_back(current(c)); // a replaced child: its successor enters
      }
    }
  }
}

// n has just lost its last parent: withdraw its child edges, continuing
// through any child this takes out of the formula.
void MutableGraph::detach(const ASTNode& start)
{
  std::vector<ASTNode> stack;
  stack.push_back(start);
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    note(Change::Detached, n);
    MG_TRACE("detach " << n.GetNodeNum() << (n.isMutableInterior() ? " mutable" : ""));
    if (MutableInterior* m = asMutable(n))
    {
      if (!m->attached_)
        continue;
      m->attached_ = false;
      for (const ASTNode& c : m->children_)
      {
        if (MutableInterior* mc = asMutable(c))
        {
          auto& ps = mc->parents_;
          ps.erase(std::find(ps.begin(), ps.end(), m));
        }
        else
        {
          auto& ps = mutParents_[c.GetNodeNum()];
          ps.erase(std::find(ps.begin(), ps.end(), m));
        }
        note(Change::CountChanged, c);
        if (parentCount(c) == 0 && !isRoot(c))
          stack.push_back(c);
      }
    }
    else
    {
      // A forwarded immutable node's child edges were withdrawn when it was
      // replaced; only its own standing remains, counted on its replacement.
      if (isForwarded(n))
        continue;
      for (const ASTNode& c : n.GetChildren())
      {
        const uint32_t ci = indexOf(c);
        assert(liveImm_[ci] > 0);
        liveImm_[ci]--;
        note(Change::CountChanged, c);
        if (parentCount(c) == 0 && !isRoot(c))
          stack.push_back(current(c)); // a replaced child: its successor leaves
      }
    }
  }
}

// --------------------------------------------------------------- creation

MutableInterior* MutableGraph::create(Kind kind, unsigned index,
                                      unsigned width, ASTChildren children,
                                      uint64_t number)
{
  MutableInterior* m = new MutableInterior(&bm, this, kind, children);
  m->wide_ = children.size() > WIDE;
  // A NOT takes its child's number plus one, so that x and (not x) sort
  // next to each other. Over an immutable child that number is the
  // manager's NOT of it, which is absent, forwarded, or the node this
  // copies: never live beside this one.
  if (kind == NOT)
    m->node_uid = children[0].GetNodeNum() + 1;
  else
  {
    // A copy keeps its original's number while that is above every
    // child; a child newer than the original (an edit below) means the
    // export will make a fresh node here too. A forwarded node of this
    // structure lends its number the same way.
    if (number == 0 && !anyMutable(children))
    {
      ASTInterior* e = bm.FindInterior(kind, children);
      if (e != NULL && isForwarded(ASTNode(e)) && numberFree(ASTNode(e)))
        number = e->GetNodeNum();
    }
    bool above = number != 0;
    for (const ASTNode& c : children)
      if (c.GetNodeNum() >= number)
        above = false;
    if (above)
      m->node_uid = number;
  }
  MG_TRACE("create kind " << kind << " -> " << m->GetNodeNum());
  m->index_width_ = index;
  m->value_width_ = width;
  owned_.push_back(ASTNode(m));
  if (!m->wide_)
    table_.insert(m);
  return m;
}

ASTNode MutableGraph::lookupOrCreate(Kind kind, unsigned index,
                                     unsigned width, ASTChildren children)
{
  const auto it = table_.find(Probe{kind, children});
  if (it != table_.end())
  {
    MutableInterior* m = *it;
    // As the hashing factory does on a hit: re-assert the widths.
    m->setIndexWidth(index);
    m->setValueWidth(width);
    // A detached node is out of the renumbering cascade (no parent edges);
    // a child renumbered since may have passed it.
    if (!numberedAbove(m))
      renumber(m);
    return ASTNode(m);
  }
  if (!anyMutable(children))
  {
    // The manager's node, which may already exist; the children are in
    // its order already, so this is a lookup or a creation there. An
    // existing node that has since been replaced stands for something
    // else now, so this structure gets a mutable node of its own.
    ASTNode r;
    if (index > 0)
      r = bm.hashingNodeFactory->CreateArrayTerm(kind, index, width, children);
    else if (width > 0)
      r = bm.hashingNodeFactory->CreateTerm(kind, width, children);
    else
      r = bm.hashingNodeFactory->CreateNode(kind, children);
    if (!isForwarded(r))
      return r;
  }
  return ASTNode(create(kind, index, width, children));
}

ASTNode MutableGraph::normalise(const ASTNode& given)
{
  const ASTNode c = current(given);
  if (!c.isMutableInterior())
  {
    if (!isStale(c))
    {
      if (c.Degree() > 0)
        MG_TRACE("normalise " << given.GetNodeNum() << " -> " << c.GetNodeNum() << " not stale");
      return c;
    }
    uint32_t idx;
    indexed(c, idx);
    if (!liveImmutable(idx) && !isRoot(c))
      return rebuildDetached(c);
    matReason_ = "normalise";
    MutableInterior* m = materialise(c);
    return m == NULL ? current(c) : m->handle();
  }
  MutableInterior* m = asMutable(c);
  if (m->attached_ || m->dead_ || isRoot(c))
    return c;
  return refresh(m);
}

// A node the factory made that nothing has held yet may point at children
// that have since been replaced. Bring it up to date before it is used; if
// that makes it equal to a node the graph holds, it is that node.
ASTNode MutableGraph::refresh(MutableInterior* m)
{
  bool changed = false;
  for (size_t slot = 0; slot < m->children_.size(); slot++)
  {
    const ASTNode c = normalise(m->children_[slot]);
    if (c != m->children_[slot])
    {
      if (!changed)
        eraseFromTable(m);
      m->children_[slot] = c;
      wideSlots_.erase(m); // rebuilt on the next repoint, if ever
      changed = true;
    }
  }
  if (!changed && !m->wide_ && m->children_.size() > 1 &&
      isCommutative(m->GetKind()))
  {
    // A node below may have been renumbered since this node was sorted.
    ASTVec sorted(m->children_);
    sortCommutative(m->GetKind(), sorted);
    if (sorted != m->children_)
    {
      eraseFromTable(m);
      m->children_.swap(sorted);
      changed = true;
    }
  }
  if (!changed && !m->wide_ && !numberedAbove(m))
    renumber(m); // a child renumbered since; no parent edges carried it
  if (!changed || m->wide_)
    return ASTNode(m);
  if (m->GetKind() == NOT)
  {
    // As in rekey: the factory's NOT of the current child.
    const ASTNode fresh = normalise(raw_.CreateNode(NOT, {m->children_[0]}));
    if (fresh != ASTNode(m))
    {
      mutForward_[m] = fresh;
      m->dead_ = true;
    }
    else
      table_.insert(m);
    return fresh;
  }
  sortCommutative(m->GetKind(), m->children_);
  const auto hit = table_.find(Probe{m->GetKind(), m->GetChildren()});
  if (hit != table_.end())
  {
    mutForward_[m] = ASTNode(*hit);
    m->dead_ = true;
    return ASTNode(*hit);
  }
  if (!anyMutable(m->GetChildren()))
  {
    ASTInterior* e = bm.FindInterior(m->GetKind(), m->GetChildren());
    if (e != NULL && !isForwarded(ASTNode(e)))
    {
      mutForward_[m] = ASTNode(e);
      m->dead_ = true;
      return ASTNode(e);
    }
  }
  table_.insert(m);
  return ASTNode(m);
}

void MutableGraph::normalise(ASTChildren children, ASTVec& out)
{
  out.reserve(children.size());
  for (const ASTNode& c : children)
    out.push_back(normalise(c));
}

ASTNode MutableGraph::rebuildDetached(const ASTNode& n)
{
  MutableGraphNest nest(*this);
  MG_TRACE("rebuildDetached " << n.GetNodeNum() << " mutable " << n.isMutableInterior()
                              << " forwarded " << isForwarded(n) << " stale " << isStale(n));
  assert(!n.isMutableInterior());
  assert(!isForwarded(n));
  assert(isStale(n));
  ASTVec kids;
  normalise(n.GetChildren(), kids);
  ASTNode r;
  if (n.GetIndexWidth() > 0)
    r = raw_.CreateArrayTerm(n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(), kids);
  else if (n.GetValueWidth() > 0)
    r = raw_.CreateTerm(n.GetKind(), n.GetValueWidth(), kids);
  else
    r = raw_.CreateNode(n.GetKind(), kids);
  if ((n.GetExpWidth() > 0 || n.GetSigWidth() > 0) && r.canStoreFPFormat())
  {
    r.SetExpWidth(n.GetExpWidth());
    r.SetSigWidth(n.GetSigWidth());
  }
  MG_TRACE("rebuildDetached " << n.GetNodeNum() << " -> " << r.GetNodeNum());
  if (r == n)
    return r;
  std::vector<uint64_t> origins(1, n.GetNodeNum());
  const auto io = immOrigins_.find(n.GetNodeNum());
  if (io != immOrigins_.end())
  {
    origins.insert(origins.end(), io->second.begin(), io->second.end());
    immOrigins_.erase(io);
  }
  moveStanding(origins, r, false);
  return r;
}

MutableInterior* MutableGraph::materialise(const ASTNode& node)
{
  MutableGraphNest nest(*this);
  const ASTNode n = current(node);
  if (MutableInterior* m = asMutable(n))
    return m;
  assert(n.Degree() > 0); // a leaf has nothing to edit
  uint32_t idx;
  const bool known = indexed(n, idx);
  assert(known);
  (void)known;
  if (!liveImmutable(idx) && !isRoot(n))
  {
    // Out of the formula: nothing to edit. A stale one is brought up to
    // date in case it comes back; NULL either way unless that is mutable.
    if (!isStale(n))
      return NULL;
    return asMutable(rebuildDetached(n));
  }

  // The copy holds current children: a child that was replaced is taken as
  // its replacement, and a child standing above a replacement is converted
  // first, so the region between here and that replacement is mutable too.
  ASTVec kids;
  normalise(n.GetChildren(), kids);
  // Normalising the children can nest deep enough to replace n itself.
  if (isForwarded(n))
  {
    matReason_ = "re-resolve";
    return materialise(n);
  }
  sortCommutative(n.GetKind(), kids); // a replacement can change the order
  const ASTChildren kidsSpan(kids.data(), kids.size());
  MG_TRACE("materialise " << n.GetNodeNum() << " [" << matReason_ << "] (given " << node.GetNodeNum()
                          << ", forwarded " << isForwarded(n) << ", mutable "
                          << n.isMutableInterior() << ", dead "
                          << (n.isMutableInterior() ? asMutable(n)->dead_ : false)
                          << ", kind " << n.GetKind() << ")");
  matReason_ = "api";

  // A NOT whose child became a NOT is its grandchild; no node is made for
  // it. A leaf cannot be edited, so there is nothing to return then.
  if (n.GetKind() == NOT && kids[0].GetKind() == NOT)
  {
    const ASTNode target = kids[0][0];
    standFor(n, target, true);
    matReason_ = "notnot";
    return target.Degree() == 0 ? NULL : materialise(target);
  }

  // Whether an edit, not merely a copy, sits below n, and how far: only
  // within the horizon do the rules have a new shape to look at. A cone
  // of 400,000 nodes above three edits is converted once, but the rules
  // run on a handful of its nodes, not all of them.
  unsigned distance = UINT_MAX;
  for (const ASTNode& c : n.GetChildren())
    distance = std::min(distance, distanceVia(c, n.GetKind()));
  const bool changedBelow = distance <= HORIZON;

  // In current terms n may already be a node that exists elsewhere in the
  // formula, or one the rules fold to something else. Then n is that
  // node, and it is that node that gets the copy (a leaf gets none). The
  // holders' cones changed if an edit sits below, twin or not.
  uint64_t number = n.GetNodeNum();
  if (!anyMutable(kidsSpan))
  {
    ASTInterior* e = bm.FindInterior(n.GetKind(), kidsSpan);
    if (e != NULL && ASTNode(e) != n)
    {
      if (!isForwarded(ASTNode(e)))
      {
        standFor(n, ASTNode(e), changedBelow);
        matReason_ = "twin";
        return materialise(ASTNode(e));
      }
      // The export hands e back for this structure: its number, not n's.
      if (numberFree(ASTNode(e)))
        number = e->GetNodeNum();
    }
  }

  MutableInterior* m;
  const auto hit = table_.find(Probe{n.GetKind(), kidsSpan});
  if (hit != table_.end())
  {
    // Its children are these current kids; below them a detached cone may
    // have gone stale. normalise refreshes it and may hand back another
    // node when the refreshed structure exists already.
    const ASTNode h = normalise(ASTNode(*hit));
    if (!h.isMutableInterior())
    {
      standFor(n, h, false);
      matReason_ = "hit-refresh";
      return h.Degree() == 0 ? NULL : materialise(h);
    }
    m = asMutable(h);
  }
  else
  {
    m = create(n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(), kidsSpan,
               number);
    m->exp_width_ = n.GetExpWidth();
    m->sig_width_ = n.GetSigWidth();
  }
  standFor(n, ASTNode(m), false);

  // The children changed below n, so the copy is a shape the rules have
  // not seen: what they make of it. The copy is in the table, so the
  // factory returns it when nothing fires.
  if (changedBelow)
    markDirty(m, distance); // the rules see it when the operation settles
  return m;
}

// Every slot of p that holds `from` now holds `to`. Re-scanned after each
// patch: a patch re-keys p, which may re-sort its children or merge it.
MutableGraph::SlotIndex& MutableGraph::slotIndex(MutableInterior* wide)
{
  auto it = wideSlots_.find(wide);
  if (it == wideSlots_.end())
  {
    it = wideSlots_.emplace(wide, SlotIndex()).first;
    for (uint32_t i = 0; i < wide->children_.size(); i++)
      it->second[identity(wide->children_[i])].push_back(i);
  }
  return it->second;
}

void MutableGraph::repointAll(MutableInterior* p, const ASTNode& from,
                              const ASTNode& to, bool structural)
{
  if (p->wide_)
  {
    // Slots are stable in a wide node; patch each slot holding `from`.
    while (!p->dead_)
    {
      const SlotIndex& index = slotIndex(p);
      const auto it = index.find(identity(from));
      if (it == index.end() || it->second.empty())
        return;
      replaceChild(p, it->second.back(), to, structural);
    }
    return;
  }
  while (!p->dead_)
  {
    size_t slot = 0;
    while (slot < p->children_.size() && p->children_[slot] != from)
      slot++;
    if (slot == p->children_.size())
      return;
    replaceChild(p, slot, to, structural);
  }
}

void MutableGraph::standFor(const ASTNode& n, const ASTNode& givenTarget,
                            bool edited)
{
  assert(!n.isMutableInterior());
  const ASTNode target = normalise(givenTarget);
  assert(target != n);
  // target's child edges count from the moment it has a parent; n's are
  // withdrawn afterwards. Attach before detach, so a child shared by both
  // never transiently drops to zero.
  const size_t before = parentCount(target);
  // n, and whatever n itself already stood for: a node that earlier
  // replaced others carries their parents, and its successor carries them on.
  std::vector<uint64_t> origins(1, n.GetNodeNum());
  const auto io = immOrigins_.find(n.GetNodeNum());
  if (io != immOrigins_.end())
  {
    origins.insert(origins.end(), io->second.begin(), io->second.end());
    immOrigins_.erase(io);
  }
  moveStanding(origins, target, edited);
  note(Change::CountChanged, target);
  if (before == 0)
    attach(target);
  for (const ASTNode& c : n.GetChildren())
  {
    const uint32_t ci = indexOf(c);
    assert(liveImm_[ci] > 0);
    liveImm_[ci]--;
    note(Change::CountChanged, c);
    if (parentCount(c) == 0 && !isRoot(c))
      detach(current(c)); // a replaced child: its successor leaves
  }
  if (isRoot(n))
    root_ = target;

  // Mutable parents held n by handle; they hold target now.
  while (true)
  {
    const auto mp = mutParents_.find(n.GetNodeNum());
    if (mp == mutParents_.end() || mp->second.empty())
      break;
    repointAll(mp->second.back(), n, current(target), edited);
  }
}

// ------------------------------------------------------------------ edits

void MutableGraph::replaceChild(MutableInterior* parent, size_t slot,
                                const ASTNode& given)
{
  replaceChild(parent, slot, given, true);
}

void MutableGraph::replaceChild(MutableInterior* parent, size_t slot,
                                const ASTNode& given, bool structural)
{
  MutableGraphNest nest(*this);
  assert(!parent->dead_);
  assert(slot < parent->children_.size());
  // A caller may hand over a handle it took before a replacement, or an
  // immutable node that stands above one.
  const ASTNode child = normalise(given);
  assert(!parent->dead_); // materialising the child cannot touch the parent
  assert(child != ASTNode(parent)); // a cycle
  const ASTNode old = parent->children_[slot];
  if (old == child)
  {
    MG_TRACE("replaceChild " << parent->GetNodeNum() << " slot " << slot << " no-op ("
                             << given.GetNodeNum() << " is " << child.GetNodeNum() << ")");
    return;
  }

  MG_TRACE("replaceChild " << parent->GetNodeNum() << " slot " << slot << " "
                           << old.GetNodeNum() << " -> " << child.GetNodeNum());
  const bool erased = eraseFromTable(parent);
  MG_TRACE("  erased " << erased << " for " << parent->GetNodeNum());
  // The new child first, so a subtree that moves from the old slot's cone
  // to the new child's never drops out and back in.
  registerParentEdge(parent, child);
  parent->children_[slot] = child;
  if (parent->wide_)
  {
    const auto wi = wideSlots_.find(parent);
    if (wi != wideSlots_.end())
    {
      std::vector<uint32_t>& was = wi->second[identity(old)];
      was.erase(std::find(was.begin(), was.end(), slot));
      wi->second[identity(child)].push_back(slot);
    }
  }
  parent->source_sort_cache_ = NULL; // derived from the children
  unregisterParentEdge(parent, old);
  note(Change::Patched, ASTNode(parent));
  rekey(parent, structural);
}

ASTNode MutableGraph::runRules(Kind kind, unsigned index, unsigned width,
                               ASTChildren kids)
{
  if (index > 0)
    return simplifying_.CreateArrayTerm(kind, index, width, kids);
  if (width > 0)
    return simplifying_.CreateTerm(kind, width, kids);
  return simplifying_.CreateNode(kind, kids);
}

ASTNode MutableGraph::runRules(MutableInterior* m)
{
  return runRules(m->GetKind(), m->getIndexWidth(), m->getValueWidth(),
                  m->GetChildren());
}

// parent is out of the table with its current children. Put it back and
// run the rules over it: the factory finds parent itself when nothing
// fires, a twin when one exists, and otherwise the node parent becomes.
void MutableGraph::rekey(MutableInterior* parent, bool structural)
{
  MG_TRACE("rekey " << parent->GetNodeNum() << (parent->dead_ ? " (dead)" : ""));
  if (parent->dead_ || parent->wide_)
    return;
  // The hashing factory's own canonical forms hold for graph nodes too. A
  // NOT's number is its child's plus one, so a NOT whose child changed is
  // the factory's NOT of the new child (or the grandchild, for a double
  // negation), never this node under its old number.
  if (parent->GetKind() == NOT)
  {
    // The factory's answer may be an immutable NOT that this node already
    // stands for; then this node is that NOT and goes back in the table.
    // The rules for NOT are constant folding and double-negation collapse,
    // which read one child and build nothing else, so they run here: the
    // dirty queue cannot reach an immutable NOT.
    const ASTNode child = parent->children_[0];
    const ASTNode fresh = normalise(runRules(NOT, 0, 0, ASTChildren(&child, 1)));
    if (fresh != ASTNode(parent))
      replaceNode(parent, fresh, structural);
    else
    {
      table_.insert(parent);
      if (structural)
        markDirty(parent);
    }
    return;
  }
  sortCommutative(parent->GetKind(), parent->children_);
  const Probe probe{parent->GetKind(), parent->GetChildren()};
  const auto hit = table_.find(probe);
  if (hit != table_.end())
  {
    const ASTNode twin = current(ASTNode(*hit));
    replaceNode(parent, twin);
    // The structure is new to this node's cone; the rules run on the twin
    // that now carries it.
    if (structural)
      if (MutableInterior* t = asMutable(twin))
        markDirty(t);
    return;
  }
  // A structural change runs the rules before any merge into an immutable
  // twin (drainDirty): the manager's table holds nodes the rules never
  // saw, and a merge there would stand in for the rules.
  if (!structural && !anyMutable(parent->GetChildren()))
  {
    ASTInterior* existing =
        bm.FindInterior(parent->GetKind(), parent->GetChildren());
    // A hit that has itself been replaced is not a live duplicate; it may
    // well be the node this one was copied from.
    if (existing != NULL && !isForwarded(ASTNode(existing)))
    {
      replaceNode(parent, ASTNode(existing), false);
      return;
    }
  }
  table_.insert(parent);
  if (structural)
    markDirty(parent); // renumbered when the rules reach it
  else if (!numberedAbove(parent))
    renumber(parent); // a newer node moved in under it
}

bool MutableGraph::numberFree(const ASTNode& forwarded) const
{
  // Only a copy of that node carries its number, while it lives.
  const ASTNode c = current(forwarded);
  return !(c.isMutableInterior() && c.GetNodeNum() == forwarded.GetNodeNum());
}

uint64_t MutableGraph::numberFor(const MutableInterior* m) const
{
  if (m->GetKind() == NOT)
    return m->children_[0].GetNodeNum() + 1;
  if (!anyMutable(m->GetChildren()))
  {
    ASTInterior* e = bm.FindInterior(m->GetKind(), m->GetChildren());
    if (e != NULL && isForwarded(ASTNode(e)) && numberFree(ASTNode(e)))
    {
      bool above = true;
      for (const ASTNode& c : m->children_)
        if (c.GetNodeNum() >= e->GetNodeNum())
          above = false; // a child renumbered since e was made
      if (above)
        return e->GetNodeNum();
    }
  }
  return MutableInterior::freshNumber();
}

void MutableGraph::renumber(MutableInterior* m)
{
  const uint64_t number = numberFor(m);
  if (number == m->GetNodeNum())
    return;
  // The parents' keys and child order are by this number.
  std::vector<MutableInterior*> ps(m->parents_);
  std::sort(ps.begin(), ps.end());
  ps.erase(std::unique(ps.begin(), ps.end()), ps.end());
  std::vector<bool> keyed(ps.size(), false);
  for (size_t i = 0; i < ps.size(); i++)
    if (!ps[i]->dead_ && !ps[i]->wide_)
      keyed[i] = eraseFromTable(ps[i]);
  MG_TRACE("renumber " << m->GetNodeNum() << " -> " << number);
  if (m->dirty_)
    dirty_.erase({m->GetNodeNum(), m});
  m->node_uid = number;
  if (m->dirty_)
    dirty_.insert({number, m});
  for (size_t i = 0; i < ps.size(); i++)
  {
    if (!keyed[i])
      continue;
    sortCommutative(ps[i]->GetKind(), ps[i]->children_);
    const bool inserted = table_.insert(ps[i]).second;
    assert(inserted); // the same children set, re-sorted: no new twin
    (void)inserted;
  }
  // A parent beyond the horizon keeps its number, below this node's now:
  // its rules do not run, and renumbering every ancestor made a deep
  // chain quadratic. A parent the queue reaches is renumbered then.
}

bool MutableGraph::numberedAbove(const MutableInterior* m)
{
  if (m->GetKind() == NOT)
    return m->GetNodeNum() == m->children_[0].GetNodeNum() + 1;
  for (const ASTNode& c : m->children_)
    if (c.GetNodeNum() >= m->GetNodeNum())
      return false;
  return true;
}

void MutableGraph::markDirty(MutableInterior* m, unsigned distance)
{
  if (m->dead_ || m->wide_)
    return;
  if (m->dirty_)
  {
    if (distance < m->dirtyDistance_)
      m->dirtyDistance_ = distance;
    return;
  }
  m->dirty_ = true;
  m->dirtyDistance_ = distance;
  dirty_.insert({m->GetNodeNum(), m});
}

bool MutableGraph::looksThrough(Kind k)
{
  return k == READ || k == WRITE || k == BVEXTRACT;
}

// The rules over every node whose cone changed, children before parents:
// a node is queued when it changes, and after the rules have seen it its
// parents are queued, up to the root. A node the rules rewrite is
// replaced, which patches and re-queues its parents anyway. One run per
// node per operation; whether a horizon can bound this is a separate
// decision (see the design note).
void MutableGraph::drainDirty()
{
  while (!dirty_.empty())
  {
    MutableInterior* m = dirty_.begin()->second;
    dirty_.erase(dirty_.begin());
    m->dirty_ = false;
    if (m->dead_ || !m->attached_)
      continue;
    // The parents' cones changed whatever the rules make of m; those
    // within the horizon are queued, one further from the change than
    // m. A rule that rewrites m re-keys its holders, which queues them
    // at distance 0 again.
    {
      const unsigned d = m->dirtyDistance_;
      const std::vector<MutableInterior*> ps(m->parents_);
      for (MutableInterior* p : ps)
      {
        const unsigned next = looksThrough(p->GetKind()) ? d : d + 1;
        if (next <= HORIZON)
          markDirty(p, next);
      }
    }
    renumber(m); // its structure is new: a new number, above its children
    const ASTVec kids(m->children_);
    MG_TRACE("rules on " << m->GetNodeNum() << " kind " << m->GetKind());
    const ASTNode fresh = normalise(runRules(m->GetKind(), m->getIndexWidth(),
                                             m->getValueWidth(),
                                             ASTChildren(kids.data(), kids.size())));
    // A replacement re-keys the holders, which queues them; the parents of
    // the node m becomes are not touched otherwise, their cones unchanged.
    if (!m->dead_ && fresh != ASTNode(m))
    {
      MG_TRACE("  rules gave " << fresh.GetNodeNum() << " kind " << fresh.GetKind());
      replaceNode(m, fresh);
      continue;
    }
    if (!m->dead_ && !anyMutable(m->GetChildren()))
    {
      // Nothing fired; an immutable node with this structure is the same
      // node (the rekey left this probe for after the rules).
      ASTInterior* existing = bm.FindInterior(m->GetKind(), m->GetChildren());
      if (existing != NULL && !isForwarded(ASTNode(existing)))
      {
        MG_TRACE("  merges into " << existing->GetNodeNum());
        replaceNode(m, ASTNode(existing)); // the holders' cones did change
        continue;
      }
    }
  }
}

// The distance a copy of a node of kind `parentKind` holding `rawChild`
// is from the nearest change below it: 0 when the child itself was
// replaced by an edit (the copy's structure changed, as a patched
// node's does), one more than a queued live copy's distance (or the
// same through a look-through kind), UINT_MAX when nothing below it
// changed. A live copy that is not queued was made above copies only.
unsigned MutableGraph::distanceVia(const ASTNode& rawChild, Kind parentKind) const
{
  ASTNode c = rawChild;
  while (true)
  {
    if (c.isMutableInterior())
    {
      const MutableInterior* m = asMutable(c);
      if (!m->dead_)
      {
        if (!m->dirty_)
          return UINT_MAX;
        return looksThrough(parentKind) ? m->dirtyDistance_ : m->dirtyDistance_ + 1;
      }
      if (m->diedByEdit_)
        return 0;
      const auto it = mutForward_.find(m);
      if (it == mutForward_.end())
        return UINT_MAX;
      c = it->second;
      continue;
    }
    const auto it = forward_.find(c.GetNodeNum());
    if (it == forward_.end())
      return UINT_MAX;
    if (editedForward_.find(c.GetNodeNum()) != editedForward_.end())
      return 0;
    c = it->second;
  }
}

void MutableGraph::moveStanding(const std::vector<uint64_t>& origins,
                                const ASTNode& to, bool edited)
{
  for (uint64_t o : origins)
  {
    MG_TRACE("forward " << o << " -> " << to.GetNodeNum() << (edited ? " (edit)" : ""));
    forward_[o] = to;
    if (edited)
      editedForward_.insert(o);
    markStaleAbove(index_.at(o));
  }
  if (MutableInterior* m = asMutable(to))
    m->origins_.insert(m->origins_.end(), origins.begin(), origins.end());
  else
  {
    indexOf(to);
    auto& v = immOrigins_[to.GetNodeNum()];
    v.insert(v.end(), origins.begin(), origins.end());
  }
}

void MutableGraph::replaceNode(MutableInterior* old, const ASTNode& given,
                               bool structural)
{
  MutableGraphNest nest(*this);
  const ASTNode oldNode(old);
  // old may already have been merged away by a nested operation (the
  // rules run inside a re-key can cascade), and normalising `given` can
  // convert a stale node that old held, re-key old and merge it. Either
  // way the replacement applies to what stands for old now.
  const ASTNode by = normalise(given);
  if (old->dead_)
  {
    const ASTNode successor = current(oldNode);
    if (successor == by)
      return;
    if (MutableInterior* m = asMutable(successor))
      replaceNode(m, by);
    else if (successor.Degree() > 0)
      standFor(successor, by, true);
    return;
  }
  // A stale twin of old normalises to old itself: nothing to do.
  if (by == oldNode)
    return;
  MG_TRACE("replaceNode " << old->GetNodeNum() << " by " << by.GetNodeNum());

  // From here on old resolves to by, and nothing merges into old: a node
  // that comes to equal it mid-operation finds by instead.
  mutForward_[old] = by;
  eraseFromTable(old);

  // Standing and parents both move to by. A merge inside the loop can hand
  // old new parents or new origins, so run until it has neither.
  while (!old->origins_.empty() || !old->parents_.empty())
  {
    if (!old->origins_.empty())
    {
      const ASTNode target = normalise(by);
      const size_t before = parentCount(target);
      std::vector<uint64_t> origins;
      origins.swap(old->origins_);
      moveStanding(origins, target, structural);
      note(Change::CountChanged, target);
      if (before == 0 && parentCount(target) > 0)
        attach(target);
    }
    while (!old->parents_.empty())
      repointAll(old->parents_.back(), oldNode, normalise(by), structural);
  }

  if (isRoot(oldNode))
  {
    root_ = normalise(by);
    note(Change::CountChanged, root_);
    if (parentCount(root_) == 0)
      attach(root_); // the root's standing is the query's hold on it
  }

  old->diedByEdit_ = structural;
  if (!old->dead_)
    kill(old);
}

void MutableGraph::replace(const ASTNode& node, const ASTNode& by)
{
  MutableGraphNest nest(*this);
  const ASTNode n = current(node);
  // A node a nested cascade has already taken out of the formula has
  // nothing left to replace.
  if (parentCount(n) == 0 && !isRoot(n))
    return;
  if (MutableInterior* m = asMutable(n))
  {
    replaceNode(m, by);
    return;
  }
  assert(n.Degree() > 0); // a leaf is not replaced, it is substituted
  const ASTNode target = normalise(by);
  if (target == n)
    return;
  standFor(n, target, true);
}

void MutableGraph::kill(MutableInterior* n)
{
  if (n->dead_)
    return;
  wideSlots_.erase(n);
  assert(n->parents_.empty());
  assert(n->origins_.empty());
  n->dead_ = true;
  eraseFromTable(n);
  detach(ASTNode(n)); // withdraws its child edges if it was attached
}

// ----------------------------------------------------------------- export

ASTNode MutableGraph::exportRoot()
{
  return rebuild(root_);
}

// Hash-cons the current formula under n. Immutable nodes with no replaced
// descendant return as they are; the ancestors of a replaced node, and
// every mutable node, are rebuilt bottom-up through the hashing factory.
ASTNode MutableGraph::rebuild(const ASTNode& top)
{
  auto unchanged = [&](const ASTNode& n) {
    if (n.isMutableInterior() || n.Degree() == 0)
      return !n.isMutableInterior();
    if (isForwarded(n))
      return false;
    uint32_t idx;
    if (!indexed(n, idx))
      return true; // never in this graph: nothing below it was replaced
    return !stale_[idx];
  };

  ankerl::unordered_dense::map<uint64_t, ASTNode> memo;
  struct Frame
  {
    ASTNode n;
    size_t i = 0;
    ASTVec kids;
    explicit Frame(const ASTNode& node) : n(node) { kids.reserve(node.Degree()); }
  };
  std::deque<Frame> stack;
  ASTNode result;

  auto answer = [&](const ASTNode& n, ASTNode& out) {
    const ASTNode c = current(n);
    if (unchanged(c))
    {
      out = c;
      return true;
    }
    const auto it = memo.find(c.GetNodeNum());
    if (it == memo.end())
      return false;
    out = it->second;
    return true;
  };

  if (answer(top, result))
    return result;
  stack.emplace_back(current(top));
  while (!stack.empty())
  {
    Frame& f = stack.back();
    const ASTChildren ch = f.n.GetChildren();
    bool descended = false;
    while (f.i < ch.size())
    {
      ASTNode out;
      if (answer(ch[f.i], out))
      {
        f.kids.push_back(out);
        f.i++;
        continue;
      }
      // Nothing above may be read after this push.
      stack.emplace_back(current(ch[f.i]));
      descended = true;
      break;
    }
    if (descended)
      continue;

    const ASTNode n = f.n;
    const ASTNode built =
        hashCons(bm, n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(),
                 n.GetExpWidth(), n.GetSigWidth(), f.kids);
    memo.emplace(n.GetNodeNum(), built);
    stack.pop_back();
    if (stack.empty())
      return built;
    Frame& parent = stack.back();
    parent.kids.push_back(built);
    parent.i++;
  }
  return result; // unreachable
}

// -------------------------------------------------------------- checking

bool MutableGraph::checkInvariant(std::string* why) const
{
  auto fail = [why](const char* what) {
    if (why != NULL)
      *why = what;
    return false;
  };
  // Recount from scratch over the current formula.
  // By identity: a detached copy may share a number with a live node.
  ankerl::unordered_dense::map<uintptr_t, size_t> count;
  ankerl::unordered_dense::map<uintptr_t, ASTNode> seen;
  ankerl::unordered_dense::map<uint64_t, ASTNode> byNumber;
  std::vector<ASTNode> stack;
  const ASTNode r = current(root_);
  stack.push_back(r);
  seen.emplace(identity(r), r);
  byNumber.emplace(r.GetNodeNum(), r);
  count[identity(r)] += 1; // the query's hold
  while (!stack.empty())
  {
    const ASTNode n = stack.back();
    stack.pop_back();
    if (const MutableInterior* m = asMutable(n))
      if (m->dead_)
        return fail("dead node reachable");
    for (const ASTNode& raw : n.GetChildren())
    {
      const ASTNode c = current(raw);
      // A mutable node's children are current: a replaced child would have
      // been patched, a stale one converted.
      if (n.isMutableInterior() && (c != raw || isStale(c)))
        return fail("mutable node holds a replaced or stale child");
      count[identity(c)] += 1;
      if (seen.emplace(identity(c), c).second)
        stack.push_back(c);
      const auto num = byNumber.emplace(c.GetNodeNum(), c);
      if (!num.second && num.first->second != c)
        return fail("two nodes of the formula share a number");
    }
  }
  for (const auto& e : seen)
    if (!e.second.isMutableInterior() && isStale(e.second))
      return fail("stale immutable node in the formula after an operation");
  if (!dirty_.empty())
    return fail("nodes still queued for the rules after an operation");
  for (const auto& e : seen)
    if (parentCount(e.second) != count[e.first])
    {
      if (why != NULL)
        *why = "parent count of " + std::to_string(e.second.GetNodeNum()) + " is " +
               std::to_string(parentCount(e.second)) + ", recount says " +
               std::to_string(count[e.first]);
      return false;
    }

  // Table and back-pointers.
  for (const ASTNode& h : owned_)
  {
    const MutableInterior* m = asMutable(h);
    // By identity: a dead node may share its structure with a live one.
    const auto it = table_.find(const_cast<MutableInterior*>(m));
    const bool inTable = it != table_.end() && *it == m;
    if (!m->wide_ && m->dead_ == inTable)
    {
      if (why != NULL)
        *why = std::string("table membership disagrees with liveness: node ") +
               std::to_string(h.GetNodeNum()) + (m->dead_ ? " dead" : " live") +
               (inTable ? " in table" : " not in table") + " kind " +
               std::to_string(h.GetKind()) + " parents " +
               std::to_string(m->parents_.size()) + " origins " +
               std::to_string(m->origins_.size());
      return false;
    }
    if (m->dead_)
      continue;
    const bool inFormula = seen.find(identity(h)) != seen.end();
    if (m->attached_ != inFormula)
      return fail(inFormula ? "node in formula but not attached"
                            : "node attached but not in formula");
    for (MutableInterior* p : m->parents_)
    {
      if (p->dead_)
        return fail("dead parent in back-pointers");
      if (std::find(p->children_.begin(), p->children_.end(), h) ==
          p->children_.end())
        return fail("back-pointer to a node that does not hold it");
    }
  }
  return true;
}

} // namespace stp
