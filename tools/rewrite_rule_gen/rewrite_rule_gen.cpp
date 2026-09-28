/**************
 *
 * Author: Trevor Hansen
 *
 * Date: Nov, 2011
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

/*This automatically discovers rewrite rules for us to build into STP.
  The structure of the rules is limited, so that we can make a rewrite system
  that doesn't cause infinite loops.

  Expressions are generated, then pairwise checked over a range of bit-widths
  to see if they are the same.
  
  If they are the same, then C++ code can be written out that implements the rule.
*/

#include <algorithm>
#include <ctime>
#include <fstream>
#include <iostream>
#include <set>
#include <memory>
#include <vector>

#include "stp/AST/AST.h"
#include "stp/Printer/printers.h"

#include "stp/AST/AST.h"
#include "stp/NodeFactory/TypeChecker.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/STPManager.h"
#include "stp/Sat/SATSolver.h"
#include "stp/Sat/SATSolverFactory.h"
#include "stp/Simplifier/DifficultyScore.h"
#include "stp/cpp_interface.h"

#include "Functionlist.h"
#include "VariableAssignment.h"
#include "misc.h"
#include "rewrite_rule.h"
#include "rewrite_system.h"

#include "stp/ToSat/BBNodeManagerAIG.h"
#include "stp/ToSat/ToCNFAIG.h"
#include "stp/ToSat/ToSATAIG.h"
#include "stp/ToSat/BitBlaster.h"

#include <fstream>
#include <sstream>
using std::stringstream;
using std::make_pair;
using std::deque;
using std::swap;
using std::ios;
using std::map;
using std::pair;
using std::ofstream;
using std::ifstream;
using namespace stp;

extern int smt2parse();

// Holds the rewrite that was disproved at the largest bitwidth.
ASTNode highestDisproved;
int highestLevel = 0;
int discarded = 0;

//////////////////////////////////
// Search bounds for the rule-finding modes. findRewrites() recurses once per
// expression it separates out, so on a full function list it goes tens of
// thousands of frames deep and exhausts the stack before finishing. These cap
// it. Both default to "no limit", which is the historical behaviour.
int max_search_depth = -1;   // -1: unbounded
int max_rules_wanted = -1;   // -1: unbounded

const int bits = 6;
const int widen_to = 10;
//////////////////////////////////

// Set by the signal handler to write out the rules that have been discovered.
volatile bool force_writeout = false;

// Saves a little bit of time. The vectors are saved between invocations.
vector<ASTVec*> saved_array;

// Stores the difficulties that have already been generated.
std::map<ASTNode, int> difficulty_cache;

Rewrite_system rewrite_system;

void clearSAT();

bool is_subgraph(const ASTNode& g, const ASTNode& h);

void createVariables();

template <class T> void removeDuplicates(T& big);

bool is_candidate(ASTNode from, ASTNode to);

bool isConstantToSat(const ASTNode& query);

void writeOutRules();

int getDifficulty(const ASTNode& n_);

vector<ASTNode> getVariables(const ASTNode& n);

typedef std::unordered_map<ASTNode, string, ASTNode::ASTNodeHasher,
                           ASTNode::ASTNodeEqual>
    ASTNodeString;

stp::STPMgr* mgr;
NodeFactory* nf;

// GlobalSTP is a borrowed pointer everywhere in the tree; this is the one
// owner in this tool. shutdown() frees it, while mgr is still alive -- an STP
// outliving its STPMgr is a use-after-free, because ~STP drops ASTNode
// references back into the manager's node tables.
std::unique_ptr<STP> stpOwner;

SATSolver* ss;
ASTNodeSet stored; // Store nodes so they aren't garbage collected.
Simplifier* simp;

ASTNode zero, one, maxNode, v, w, v0, w0;

// Width of the rewrite rules that were output last time.
int lastOutput = 0;

bool checkRule(const ASTNode& from, const ASTNode& to, VariableAssignment& ass,
               bool& bad);

ASTNode withNF(const ASTNode& n)
{
  if (n.isAtom())
    return n;

  ASTVec c;
  for (size_t i = 0; i < n.Degree(); i++)
    c.push_back(withNF(n[i]));

  if (n.GetType() == BOOLEAN_TYPE)
    return nf->CreateNode(n.GetKind(), c);
  else
    return nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                               n.GetValueWidth(), c);
}

ASTNode renameVars(const ASTNode& n)
{
  ASTNodeMap ft;

  assert(v.GetValueWidth() == v0.GetValueWidth());
  assert(w.GetValueWidth() == w0.GetValueWidth());

  ft.insert(make_pair(v, v0));
  ft.insert(make_pair(w, w0));

  ASTNodeMap cache;
  return SubstitutionMap::replace(n, ft, cache, nf);
}

ASTNode renameVarsBack(const ASTNode& n)
{
  ASTNodeMap ft;

  assert(v.GetValueWidth() == v0.GetValueWidth());
  assert(w.GetValueWidth() == w0.GetValueWidth());

  ft.insert(make_pair(v0, v));
  ft.insert(make_pair(w0, w));

  ASTNodeMap cache;
  return SubstitutionMap::replace(n, ft, cache, nf);
}

// Helper functions. Don't need to specify the width.
ASTNode create(Kind k, const ASTNode& n0, const ASTNode& n1)
{
  if (is_Term_kind(k))
    return nf->CreateTerm(k, n0.GetValueWidth(), n0, n1);
  else
    return nf->CreateNode(k, n0, n1);
}

ASTNode create(Kind k, ASTVec& c)
{
  if (is_Term_kind(k))
    return nf->CreateTerm(k, c[0].GetValueWidth(), c);
  else
    return nf->CreateNode(k, c);
}

// Get the unique variables in the expression.
void getVariables(const ASTNode& n, vector<ASTNode>& symbols,
                  ASTNodeSet& visited)
{
  if (visited.find(n) != visited.end())
    return;
  visited.insert(n);

  if (n.GetKind() == SYMBOL &&
      (find(symbols.begin(), symbols.end(), n) == symbols.end()))
    symbols.push_back(n);

  for (size_t i = 0; i < n.Degree(); i++)
    getVariables(n[i], symbols, visited);
}

vector<ASTNode> getVariables(const ASTNode& n)
{
  vector<ASTNode> symbols;
  ASTNodeSet visited;
  getVariables(n, symbols, visited);

  return symbols;
}

// Get the constant from replacing values in the map.
ASTNode eval(const ASTNode& n, ASTNodeMap& map, int count = 0)
{
  assert(n != mgr->ASTUndefined);

  if (n.isConstant())
    return n;

  if (map.find(n) != map.end())
  {
    assert((*map.find(n)).second != mgr->ASTUndefined);
    return (*map.find(n)).second;
  }

  if (n.Degree() == 0)
  {
    cerr << n;
    assert(false);
  }

  // We have an array of arrays already created to store the children.
  // This reduces the number of objects created/destroyed.
  if ((size_t)count >= saved_array.size())
    saved_array.push_back(new ASTVec());

  ASTVec& new_children = *saved_array[count];
  new_children.clear();

  for (size_t i = 0; i < n.Degree(); i++)
    new_children.push_back(eval(n[i], map, count + 1));

  ASTNode r = NonMemberBVConstEvaluator(mgr, n.GetKind(), new_children,
                                        n.GetValueWidth());
  new_children.clear();
  map.insert(make_pair(n, r));
  return r;
}

bool checkProp(const ASTNode& n)
{
  vector<ASTNode> symbols;
  ASTNodeSet visited;
  getVariables(n, symbols, visited);
  int value = -1;

  if (n.isConstant())
    return true;

  for (int i = 0; i < pow(2, symbols.size()); i++)
  {
    ASTNodeMap mapToVal;
    for (size_t j = 0; j < symbols.size(); j++)
      mapToVal.insert(make_pair(symbols[j],
                                (0x1 & (i >> (j * bits))) == 0 ? mgr->ASTFalse
                                                               : mgr->ASTTrue));

    if (i == 0)
    {
      ASTNode r = eval(n, mapToVal);
      if (r.GetType() == BOOLEAN_TYPE)
        value = (mgr->ASTFalse == r ? 0 : 1);
      else
        value = r.GetUnsignedConst();
    }
    else
    {
      ASTNode nd = eval(n, mapToVal);
      if (nd.GetType() == BOOLEAN_TYPE)
      {
        if (value != (mgr->ASTFalse == nd ? 0 : 1))
          return false;
      }
      else if (value != (int)nd.GetUnsignedConst())
        return false;
    }
  }

  cout << "is actually a const: "
       << "[" << value << "]" << n;
  return true;
}

// True if it's always true, otherwise fills the assignment.
bool isConstant(const ASTNode& n, VariableAssignment& different,
                const int bit_width, const int64_t timeout_max_confl)
{
  if (isConstantToSat(n, timeout_max_confl))
    return true;
  else
  {
    mgr->ValidFlag = false;

    vector<ASTNode> symbols = getVariables(n);

    // Both of them might not be contained in the assignment,
    // (which might have been widened).
    ASTNode vN = mgr->CreateZeroConst(bit_width);
    ASTNode wN = mgr->CreateZeroConst(bit_width);

    for (size_t i = 0; i < symbols.size(); i++)
    {
      assert(symbols[i].GetValueWidth() == (unsigned)bit_width);

      if (strncmp(symbols[i].GetName(), "v", 1) == 0)
        vN = GlobalSTP->Ctr_Example->GetCounterExample(symbols[i]);
      else if (strncmp(symbols[i].GetName(), "w", 1) == 0)
        wN = GlobalSTP->Ctr_Example->GetCounterExample(symbols[i]);
    }

    different.setValues(vN, wN);

    return false;
  }
}

// Widens terms from "bits" to "width".
ASTNode widen(const ASTNode& w, int width)
{
  assert(bits >= 4);

  if (w.isConstant() && w.GetValueWidth() == 1)
    return w;

  if (w.isConstant() && w.GetValueWidth() == bits)
  {
    ASTNode width_n = mgr->CreateBVConst(32, width);
    return nf->CreateTerm(BVSX, width, w, width_n);
  }

  if (w.isConstant() && w.GetValueWidth() == bits - 1)
  {
    ASTNode width_n = mgr->CreateBVConst(32, width - 1);
    return nf->CreateTerm(BVSX, width - 1, w, width_n);
  }

  if (w.isConstant() && w.GetValueWidth() == 32) // Extract DEFINATELY.
  {
    if (w == mgr->CreateZeroConst(32))
      return w;

    if (w == mgr->CreateOneConst(32))
      return w;

    if (w == mgr->CreateBVConst(32, bits))
      return mgr->CreateBVConst(32, width);

    if (w == mgr->CreateBVConst(32, bits - 1))
      return mgr->CreateBVConst(32, width - 1);

    if (w == mgr->CreateBVConst(32, bits - 2))
      return mgr->CreateBVConst(32, width - 2);
  }

  if (w.isConstant())
    return mgr->ASTUndefined;

  if (w.GetKind() == SYMBOL && w.GetType() == BOOLEAN_TYPE)
    return w;

  if (w.GetKind() == SYMBOL && w.GetType() == BITVECTOR_TYPE)
  {
    char s[20];
    // sprintf(s, "%s_widen_to_rarely_used_name", w.GetName());
    sprintf(s, "%s_widen", w.GetName());
    ASTNode newS = mgr->LookupOrCreateSymbol(s);
    newS.SetValueWidth(width);
    stored.insert(newS);
    return newS;
  }

  ASTVec ch;
  for (size_t i = 0; i < w.Degree(); i++)
  {
    ch.push_back(widen(w[i], width));
    if (ch.back() == mgr->ASTUndefined)
      return mgr->ASTUndefined;
  }

  if (w.GetKind() == BVCONCAT &&
      ((int)(ch[0].GetValueWidth() + ch[1].GetValueWidth()) != width))
    return mgr->ASTUndefined; // Didn't widen properly.

  // We got to the trouble below because sometimes we get 1-bit wide expressions
  // which we don't
  // want to widen to "bits".
  ASTNode result;
  if (w.GetType() == BOOLEAN_TYPE)
    result = nf->CreateNode(w.GetKind(), ch);
  else if (w.GetKind() == BVEXTRACT)
  {
    int new_width = ch[1].GetUnsignedConst() - ch[2].GetUnsignedConst() + 1;
    result = nf->CreateTerm(BVEXTRACT, new_width, ch);
  }
  else if (w.GetKind() == BVCONCAT)
    result = nf->CreateTerm(BVCONCAT,
                            ch[1].GetValueWidth() + ch[0].GetValueWidth(), ch);
  else if (w.GetKind() == ITE)
    result = nf->CreateTerm(ITE, ch[1].GetValueWidth(), ch);
  else if (w.GetKind() == BVSX)
    result = nf->CreateTerm(BVSX, ch[1].GetUnsignedConst(), ch);
  else
    result = nf->CreateTerm(w.GetKind(), ch[0].GetValueWidth(), ch);

  BVTypeCheck(result);
  return result;
}

/*
 * Accepts t_0 -> t_1,
 * when:
 * 1) t_0 and t_1 aren't the syntactically equal.
 * 2) t_1 is a constant (t_0 isn't).
 * 3) t_1 is a subgraph of t_0.
 */

bool orderEquivalence(ASTNode& from, ASTNode& to)
{
  if (from.IsNull())
    return false;
  if (from.GetKind() == UNDEFINED)
    return false;
  if (to.IsNull())
    return false;
  if (to.GetKind() == UNDEFINED)
    return false;

  if (from == to)
    return false;

  // Sometimes this function is run on pairs to see if they can be ordered,
  // even if they aren't equivalences. For instance (1,2).
  if (from.isConstant() && to.isConstant())
    return false;

  if (from.isConstant())
  {
    swap(from, to);
    return true;
  }

  if (to.isConstant())
  {
    return true;
  }

  if (is_subgraph(to, from))
  {
    return true;
  }

  if (is_subgraph(from, to))
  {
    swap(from, to);
    return true;
  }

  return false;
}

int getDifficulty(const ASTNode& n_)
{
  assert(n_.GetType() == BITVECTOR_TYPE);

  if (difficulty_cache.find(n_) != difficulty_cache.end())
    return difficulty_cache.find(n_)->second;

  // Calculate the difficulty over the widened version.
  ASTNode n = widen(n_, widen_to);
  if (n.GetKind() == UNDEFINED)
    return -1;

  if (n.GetValueWidth() != widen_to)
    return -1;

  BBNodeManagerAIG nm;
  BitBlasterAIG bb(&nm, simp, mgr->defaultNodeFactory, &mgr->UserFlags);

  // equals fresh variable to convert to boolean type.
  ASTNode f = mgr->CreateFreshVariable(0, widen_to, "ffff");
  ASTNode input = create(EQ, f, n);

  BBNodeAIG BBFormula = bb.BBForm(input);

  clearSAT();

  CNF cnfData;
  ToCNFAIG toCNF(mgr->UserFlags);
  ToSATBase::ASTNodeToSATVar nodeToSATVar;
  toCNF.toCNF(BBFormula, cnfData, nodeToSATVar, false, nm);

  // Send the clauses to the SAT solver, do unit propagation, and count what
  // is left. Backends that keep no clause count fall back to the raw CNF
  // size: a coarser difficulty, but still monotone with formula size.
  ///////////////
  int score;
  if (ss->reportsClauseCount())
  {
    // Create a new sat variable for each of the variables in the CNF.
    assert(ss->nVars() == 0);
    for (uint32_t i = 0; i < cnfData.varCount(); i++)
      ss->newVar();

    SATSolver::vec_literals satSolverClause;
    for (CNF::ClauseCursor c = cnfData.clauses(); c.next();)
    {
      satSolverClause.clear();
      for (const int *pLit = c.begin(), *pStop = c.end(); pLit < pStop; pLit++)
      {
        uint32_t var = (*pLit) >> 1;
        assert((var < ss->nVars()));
        SATSolver::Lit l = SATSolver::mkLit(var, (*pLit) & 1);
        satSolverClause.push(l);
      }

      ss->addClause(satSolverClause);
    }

    ss->simplify();
    assert(ss->okay());
    // should be satisfiable.

    // Why we go to all this trouble. The number of clauses.
    score = ss->nClauses();
    assert(score <= (int)cnfData.clauseCount());
  }
  else
  {
    score = (int)cnfData.clauseCount();
  }
  //////////////

  cnfData.clear();

  // Free the memory in the AIGs.
  BBFormula = BBNodeAIG(); // null node

  difficulty_cache.insert(make_pair(n_, score));
  return score;
}

// binary proposition.
void doProp(Kind k, ASTNode a)
{
  checkProp(nf->CreateNode(k, mgr->ASTTrue, a));
  checkProp(nf->CreateNode(k, a, mgr->ASTTrue));
  checkProp(nf->CreateNode(k, mgr->ASTFalse, a));
  checkProp(nf->CreateNode(k, a, mgr->ASTFalse));
  checkProp(nf->CreateNode(k, a, a));

  if (a.GetKind() != NOT)
    doProp(k, mgr->CreateNode(NOT, a));
}

// Get all four variations of the prop A.
ASTNode get(ASTNode a, int i, int pos)
{
  int v = i >> (2 * pos);
  if ((v & 3) == 3)
    return a;
  if ((v & 2) == 2)
    return mgr->ASTTrue;
  if ((v & 1) == 1)
    return mgr->ASTFalse;
  if ((v & 0) == 0)
    return mgr->CreateNode(NOT, a);

  cerr << "FAILED";
  exit(1);
}

void doIte(ASTNode a)
{
  for (int i = 0; i < 64; i++)
  {
    ASTNode n = nf->CreateNode(ITE, get(a, i, 2), get(a, i, 1), get(a, i, 0));
    checkProp(n);
  }
}

void do_write_out(int /*ignore*/)
{
  difficulty_cache.clear();
  force_writeout = true;
}

volatile bool debug_usr2 = false;

// toggle.
void do_usr2(int /*ignore*/)
{
  debug_usr2 = !debug_usr2;
}

void startup()
{
  CONSTANTBV::ErrCode ec = CONSTANTBV::BitVector_Boot();
  if (0 != ec)
  {
    cout << CONSTANTBV::BitVector_Error(ec) << endl;
    return;
  }

  mgr = new stp::STPMgr();
  stp::GlobalParserBM = mgr;
  stpOwner = std::make_unique<STP>(mgr);
  GlobalSTP = stpOwner.get();

  mgr->defaultNodeFactory =
      new SimplifyingNodeFactory(*mgr->hashingNodeFactory, *mgr);
  nf = new TypeChecker(*mgr->defaultNodeFactory, *mgr);

  mgr->UserFlags.stats_flag = false;
  mgr->UserFlags.optimize_flag = true;

  ss = createSATSolver(mgr->UserFlags);

  // Prime the cache with 100..
  for (int i = 0; i < 100; i++)
  {
    saved_array.push_back(new ASTVec());
  }

  zero = mgr->CreateZeroConst(bits);
  one = mgr->CreateOneConst(bits);
  maxNode = mgr->CreateMaxConst(bits);

  srand(time(NULL));

  v0 = mgr->LookupOrCreateSymbol("v0");
  v0.SetValueWidth(bits);
  w0 = mgr->LookupOrCreateSymbol("w0");
  w0.SetValueWidth(bits);

  // Write out the work so far..
  signal(SIGUSR1, do_write_out);
  signal(SIGUSR2, do_usr2);
}

// Mirrors the STP half of startup(). Runs while mgr is still alive, which is
// the order ~STP needs.
void shutdown()
{
  GlobalSTP = NULL;
  stpOwner.reset();
}

void clearSAT()
{
  delete ss;
  ss = createSATSolver(mgr->UserFlags);

  delete GlobalSTP->tosat;
  ToSATAIG* aig = new ToSATAIG(mgr, GlobalSTP->arrayTransformer);
  GlobalSTP->tosat = aig;
}

// Return true if the negation of the query is unsatisfiable.
bool isConstantToSat(const ASTNode& query, int64_t timeout_max_confl)
{
  assert(query.GetType() == BOOLEAN_TYPE);

  GlobalSTP->ClearAllTables();
  clearSAT();

  ASTNode query2 = nf->CreateNode(NOT, query);

  assert(!ss->reportsClauseCount() || ss->nClauses() == 0);
  mgr->SetQuery(mgr->ASTUndefined);

  // A negative budget means "no limit", which is spelled by not configuring
  // one: the SAT solvers are only ever handed a value >= 0.
  if (timeout_max_confl >= 0)
    ss->setMaxConflicts(timeout_max_confl);

  SOLVER_RETURN_TYPE r = GlobalSTP->Ctr_Example->CallSAT_ResultCheck(
      *ss, query2, query2, query2, GlobalSTP->tosat, false);

  return (r == SOLVER_VALID); // unsat, always true
}

// Replaces the symbols in n, by each of the values, and concatenates them
// to turn it into a single 64-bit value.
uint64_t getHash(const ASTNode& n_, const vector<VariableAssignment>& values)
{
  assert(values.size() > 0);
  const size_t ass_bitwidth = values[0].getV().GetValueWidth();
  assert(ass_bitwidth >= bits);

  ASTNode n = n_;

  // The values might be at a higher bit-width.
  if (ass_bitwidth > bits)
    n = widen(n_, ass_bitwidth);

  if (n == mgr->ASTUndefined) // Can't be widened.
    return 0;

  vector<ASTNode> symbols = getVariables(n);

  uint64_t hash = 0;

  for (size_t j = 0; j < symbols.size(); j++)
  {
    assert(symbols[j].GetValueWidth() == ass_bitwidth);
  }

  for (size_t i = 0; i < values.size(); i++)
  {
    // They both should be set..
    assert(values[i].getV().GetValueWidth() == ass_bitwidth);
    assert(values[i].getW().GetValueWidth() == ass_bitwidth);

    ASTNodeMap mapToVal;
    for (size_t j = 0; j < symbols.size(); j++)
    {
      assert(symbols[j].GetValueWidth() == ass_bitwidth);

      if (strncmp(symbols[j].GetName(), "v", 1) == 0)
        mapToVal.insert(make_pair(symbols[j], values[i].getV()));
      else if (strncmp(symbols[j].GetName(), "w", 1) == 0)
        mapToVal.insert(make_pair(symbols[j], values[i].getW()));
      else
      {
        cerr << "Unknown symbol!" << symbols[j];
        FatalError("f");
      }
    }

    ASTNode r = eval(n, mapToVal);
    assert(r.isConstant());
    hash <<= ass_bitwidth;
    hash += r.GetUnsignedConst();
  }
  return hash;
}

// is from a sub-term of "to"?
bool contained_in(ASTNode from, ASTNode to)
{
  if (from == to)
    return true;

  for (size_t i = 0; i < from.Degree(); i++)
    if (contained_in(from[i], to))
      return true;

  return false;
}

// Is mapping from "From" to "to" a rule we are interested in??
bool is_candidate(ASTNode from, ASTNode to)
{
  if (to.Degree() == 0)
    return true; // Leaves are always good.

  if (contained_in(from, to))
    return true; // If what we are mapping to is contained in the "from", that's
                 // good too.

  return false;
}

bool is_subgraph(const ASTNode& g, const ASTNode& h)
{
  if (g == h)
    return true;

  for (size_t i = 0; i < h.Degree(); i++)
    if (is_subgraph(g, h[i]))
      return true;

  return false;
}

// Breaks the expressions into buckets recursively, then pairwise checks that
// they are equivalent.
// This used to recurse three ways, and an unbounded run segfaulted: the stack
// ran out at depth 23771. Two of the calls were tail calls -- "narrow the list
// by one counterexample, start again, and return" -- and the list shrinks by
// about one element each time, so they alone went tens of thousands of frames
// deep. The third splits the list into equivalence buckets and recurses into
// each, and because a narrowed restart re-enters that split, converting only
// the tail calls just moved the growth (it then died at depth 38730).
//
// So the search carries its own stack. `pending` holds the buckets still to
// be examined, the tail calls are iterations of the inner loop, and the depth
// STP's own stack reaches no longer depends on the size of the function list.
void findRewrites(ASTVec& expressions, const vector<VariableAssignment>& values,
                  const int depth = 0)
{
  struct Frame
  {
    ASTVec expressions;
    vector<VariableAssignment> values;
    int depth;
  };

  vector<Frame> pending;
  {
    // Taken by reference and consumed, exactly as before.
    Frame first;
    first.expressions.swap(expressions);
    first.values = values;
    first.depth = depth;
    pending.push_back(std::move(first));
  }

  while (!pending.empty())
  {
  ASTVec work;
  work.swap(pending.back().expressions);
  vector<VariableAssignment> vals(std::move(pending.back().values));
  int d = pending.back().depth;
  pending.pop_back();

  // The former tail calls set this and go round again with a narrowed list.
  bool restart = true;
  // Set when a split separated nothing, so the next round goes straight to
  // the pairwise pass instead of performing the identical split again.
  bool skipSplit = false;
  while (restart)
  {
  restart = false;

  if (work.size() < 2)
  {
    discarded += work.size();
    break;
  }

  if (max_search_depth >= 0 && d >= max_search_depth)
  {
    discarded += work.size();
    break;
  }

  if (max_rules_wanted >= 0 &&
      (int)rewrite_system.size() >= max_rules_wanted)
  {
    discarded += work.size();
    break;
  }

  cout << '\n'
       << "depth:" << d << ", size:" << work.size()
       << " values:" << vals.size() << " found: " << rewrite_system.size()
       << " done:" << discarded << "\n";

  assert(work.size() > 0);

  if (vals.size() > 0 && !skipSplit)
  {
    const int old_size = vals.size();
    if (old_size > 10)
      removeDuplicates(work);

    discarded += (old_size - vals.size());

    // Put the functions in buckets based on their results on the values.
    std::unordered_map<uint64_t, ASTVec> map;
    for (size_t i = 0; i < work.size(); i++)
    {
      if (work[i] == mgr->ASTUndefined)
        continue; // omit undefined.

      if (i % 50000 == 49999)
        cout << ".";
      uint64_t hash = getHash(work[i], vals);
      if (map.find(hash) == map.end())
        map.insert(make_pair(hash, ASTVec()));
      map[hash].push_back(work[i]);
    }
    work.clear();

    std::unordered_map<uint64_t, ASTVec>::iterator it2;

    cout << "Split into " << map.size() << " pieces\n";
    if (d > 0)
    {
      assert(map.size() > 0);
    }

    // One bucket holding everything means this value set told the expressions
    // apart not at all, so it has taught us nothing and must be kept rather
    // than reset -- resetting it is what made every split as coarse as the
    // first, and the pairwise pass then produced the same counterexample
    // forever. Go on to examine the group pairwise, and retry the split once
    // that pass has contributed another assignment.
    if (map.size() == 1)
    {
      work.swap(map.begin()->second);
      skipSplit = true;
      restart = true;
      continue; // same frame, straight to the pairwise pass
    }

    // Pushed rather than recursed into. Reversed first so they come back off
    // the stack in the order the recursive version visited them.
    vector<ASTVec> buckets;
    for (it2 = map.begin(); it2 != map.end(); it2++)
      buckets.push_back(std::move(it2->second));
    map.clear();

    for (size_t b = buckets.size(); b-- > 0;)
    {
      Frame f;
      f.expressions.swap(buckets[b]);
      f.depth = d + 1;
      pending.push_back(std::move(f));
    }
    break;
  }
  ASTVec& equiv = work;

  for (size_t i = 0; i < equiv.size(); i++)
  {
    if (equiv[i].GetKind() == UNDEFINED)
      continue;

    // nb. I haven't rebuilt the map, it's done by writeOutRules().
    equiv[i] = rewrite_system.rewriteNode(equiv[i]);

    for (size_t j = i + 1; j < equiv.size();
         j++) /// commutative so skip some.
    {
      if (equiv[i].GetKind() == UNDEFINED || equiv[j].GetKind() == UNDEFINED)
        continue;

      ASTNode& from = equiv[i];
      ASTNode& to = equiv[j];

      if (from == to)
      {
        to = mgr->ASTUndefined;
        continue;
      }

      /* If they can't be ordered continue. Maybe they could be ordered if we
       *applied
       * the rewrites through. This also means that we won't split on terms that
       *can't
       * be ordered.
       *
       * Sometimes we run it anyway. Otherwise we do O(n^2) on big groups of
       * expression that can't be ordered.
       */

      ASTNode f = from, t = to;
      if ((rand() % 500 != 0) && !orderEquivalence(f, t))
        continue;

      VariableAssignment different;
      bool bad = false;
      const int64_t st = getCurrentTime();

      if (checkRule(from, to, different, bad))
      {
        const int64_t checktime = getCurrentTime() - st;

        equiv[i] = rewriteThroughWithAIGS(equiv[i]);
        equiv[j] = rewriteThroughWithAIGS(equiv[j]);

        equiv[i] = rewrite_system.rewriteNode(equiv[i]);
        equiv[j] = rewrite_system.rewriteNode(equiv[j]);

        // The rules should have been created with the simplifying node factory.
        assert(equiv[i] == withNF(equiv[i]));
        assert(equiv[j] == withNF(equiv[j]));

        ASTNode f = equiv[i];
        ASTNode t = equiv[j];

        if (t == f)
        {
          equiv[j] = mgr->ASTUndefined;
          continue;
        }

        bool r = orderEquivalence(f, t);

        if (!r)
          continue;

        Rewrite_rule rr(mgr, f, t, checktime);

        cout << "i:" << i << " j:" << j << " size:" << equiv.size() << "\n";

        VariableAssignment bad;
        if (!rr.timedCheck(10000, bad))
        {
          vector<VariableAssignment> ass;
          ass.push_back(bad);

          cout << "Rule failed extended verification.";

          // If it can fit into an unsigned. Split the list on it.
          if (sizeof(unsigned int) * 8 > bad.getV().GetValueWidth())
          {
            // equiv aliases work, so the list carries over untouched.
            // Accumulated, not replaced: dropping the assignments already
            // found makes every split as coarse as the first one, so a group
            // the newest value cannot separate never gets separated.
            vals.push_back(bad);
            skipSplit = false; // the enlarged set can separate them now
            d++;
            restart = true;
            break;
          }
          else
            continue;
        }

        cout << "Discovered a new rule.";
        cout << f << t;
        cout << getDifficulty(f) << " to " << getDifficulty(t) << endl;

        cout << "Verified Rule to: " << rr.getVerifiedToBits() << " bits"
             << endl;
        cout << "------";

        rewrite_system.push_back(rr);

        // In some unusual cases it's not synatically identical.
        // assert (t == rewrite_system.rewriteNode(f))

        equiv[i] = rewrite_system.rewriteNode(equiv[i]);
        equiv[j] = rewrite_system.rewriteNode(equiv[j]);

        // They're the same, so in future we only care about one of them.
        if (equiv[i] == equiv[j])
          equiv[j] = mgr->ASTUndefined;
      }
      else if (!bad)
      {
        vector<VariableAssignment> ass;
        ass.push_back(different);

        // Discard the ones we've checked entirely.
        ASTVec newEquiv(equiv.begin() + std::max((int)i - (int)1, 0),
                        equiv.end());
        equiv.clear();

        work.swap(newEquiv);
        vals.push_back(different); // accumulated, see above
        skipSplit = false; // the enlarged set can separate them now
        d++;
        restart = true;
        break;
      }

      // Write out the rules intermitently.
      if (force_writeout || lastOutput + 500 < rewrite_system.size())
      {
        rewrite_system.rewriteAll();
        writeOutRules();
        lastOutput = rewrite_system.size();
      }
    }
    if (restart)
      break;
  }

  if (restart)
    continue; // narrowed list, one more counterexample: go round again

  discarded += work.size();
  } // while (restart)
  } // while (!pending.empty())
}

// Widen the rule.
// Check it holds at higher bit-widths.
// If so, then save the rule for later.
bool checkRule(const ASTNode& from, const ASTNode& to,
               VariableAssignment& assignment, bool& bad)
{
  ASTVec children;
  children.push_back(from);
  children.push_back(to);

  // The simplifying node factory sometimes meant it couldn't be widended.
  const ASTNode n = mgr->hashingNodeFactory->CreateNode(EQ, children);

  assert(widen_to > bits);

  for (int i = bits; i < widen_to; i++)
  {
    const ASTNode& widened = widen(n, i);

    // Can't widen (usually because of CONCAT or a BVCONST).
    if (widened == mgr->ASTUndefined)
    {
      cout << "cannot widen";
      bad = true;
      return false;
    }

    // Send it to the SAT solver to verify that the widening has the same
    // answer.
    bool result = isConstant(widened, assignment, i);

    if (!result)
    {
      if (i > highestLevel)
      {
        highestLevel = i;
        highestDisproved = n;
      }

      // Detected it's not a constant, or is constant FALSE.

      cout << "*" << i - bits << "*";
      return false;
    }
  }

  return true;
}

template <class T> void removeDuplicates(T& big)
{
  cout << "Before removing duplicates: " << big.size();
  std::sort(big.begin(), big.end());
  typename T::iterator it = std::unique(big.begin(), big.end());
  big.erase(it, big.end());
  cout << ". After removing duplicates: " << big.size() << endl;
}

/* Writes out:
 * rules_new.smt2: rules in SMT2 one rule per frame.
 * array.smt2: rules in SMT2 in one big conjunct.
 */

// Write out all the rules that have been discovered to various files in
// different formats.
void writeOutRules()
{
  cout << "Writing out: " << rewrite_system.size() << " rules" << endl;
  force_writeout = false;

  ofstream outputFile;

  ///////////////
  outputFile.open("rules_new.smt2", ios::trunc);
  for (Rewrite_system::RewriteRuleContainer::iterator it =
           rewrite_system.toWrite.begin();
       it != rewrite_system.toWrite.end(); it++)
  {
    it->writeOut(outputFile);
  }
  outputFile.close();

  /////////////////
  outputFile.open("array.smt2", ios::trunc);
  ASTVec v;
  for (Rewrite_system::RewriteRuleContainer::iterator it =
           rewrite_system.toWrite.begin();
       it != rewrite_system.toWrite.end(); it++)
  {
    v.push_back(it->getN());
  }

  if (v.size() > 0)
  {
    ASTNode n = mgr->CreateNode(AND, v);
    printer::SMTLIB2_PrintBack(outputFile, n, mgr, true);
  }
  outputFile.close();
}

// ASSUMES that buildRewrite() has recently been run on the rules..

ASTNode rename_then_rewrite(ASTNode n, const Rewrite_rule& original_rule)
{
  n = renameVars(n);
  ASTNodeMap seen;
  n = rewrite(n, original_rule, seen, 0);
  return renameVarsBack(n);
}

// assumes the variables in n are two characters wide.
ASTNode rewrite(const ASTNode& n, const Rewrite_rule& original_rule,
                ASTNodeMap& seen, int depth)
{
  if (depth > 50)
    return n;

  if (n.isAtom())
    return n;

  //  if (seen.find(n) != seen.end())
  //    return seen.find(n)->second;

  ASTVec v;
  v.reserve(n.Degree());
  for (size_t i = 0; i < n.Degree(); i++)
    v.push_back(rewrite(n[i], original_rule, seen, depth + 1));

  assert(v.size() > 0);
  ASTNode n2;

  if (ASTChildren(v) != n.GetChildren())
  {
    if (n.GetType() != BOOLEAN_TYPE)
      n2 = mgr->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),
                                n.GetValueWidth(), v);
    else
      n2 = mgr->CreateNode(n.GetKind(), v);
  }
  else
    n2 = n;

  ASTNodeMap fromTo;

  if (rewrite_system.lookups_invalid)
    rewrite_system.buildLookupTable();

  vector<Rewrite_rule>& rr = rewrite_system.kind_to_rr[n.GetKind()];

  for (size_t i = 0; i < rr.size(); i++)
  {
    // If they are the same rule. Then don't match them.
    if (original_rule == (rr[i]))
      continue;

    if (fromTo.size() > 0)
      fromTo.clear();

    ASTNode f = rr[i].getFrom();
    // if (n2.GetValueWidth() > bits)
    //        f = widen(f,n2.GetValueWidth());

    if (commutative_matchNode(f, n2, fromTo, 1))
    {
      if (debug_usr2)
      {
        cerr << "Original Rule";

        cerr << original_rule.getFrom();
        cerr << "->" << original_rule.getTo();

        cerr << "Matching Rule";
        cerr << rr[i].getFrom();
        cerr << "->" << rr[i].getTo();

        cerr << "--------------";
        cerr << "Unifying" << f;
        cerr << "with:" << n2;
        cerr << "--------------";

        for (ASTNodeMap::iterator it = fromTo.begin(); it != fromTo.end(); it++)
        {
          cerr << it->first << "to" << it->second << endl;
        }

        cerr << "--------------";
      }

      // The substitution map replace should never infinite loop.
      ASTNodeMap cache;

      ASTNode rrTo = rr[i].getTo();
      // if (n2.GetValueWidth() > bits)
      //   rrTo = widen(rrTo,n2.GetValueWidth());

      ASTNode r =
          SubstitutionMap::replace(rrTo, fromTo, cache, nf, false, true);

      if (debug_usr2 && (getDifficulty(n2) < getDifficulty(r)))
      {
        cerr << rr[i].getFrom() << rr[i].getTo();
        cerr << getDifficulty(rr[i].getFrom()) << "to"
             << getDifficulty(rr[i].getTo()) << "\n";
        cerr << n2 << r;
        cerr << getDifficulty(n2) << "to" << getDifficulty(r);
        assert(getDifficulty(n2) >= getDifficulty(r));
      }

      seen.insert(make_pair(n2, r));

      if (debug_usr2)
      {
        cerr << "Term after replacing (1/2) :";
        cerr << n2 << ":" << r;
      }

      r = rewrite(r, original_rule, seen, depth + 1);
      seen.erase(n2);
      seen.insert(make_pair(n2, r));
      if (debug_usr2)
      {
        cerr << "inserting (2/2)" << n2 << r;
        cerr << "+++++++!!!!!!!!!!++++++++";
      }

      return r;
    }
  }
  // seen.insert(make_pair(n2, n2));
  return n2;
}

int smt2_scan_string(const char* yy_str);

// http://stackoverflow.com/questions/3418231/c-replace-part-of-a-string-with-another-string
bool replace(std::string& str, const std::string& from, const std::string& to)
{
  size_t start_pos = str.find(from);
  if (start_pos == std::string::npos)
    return false;
  str.replace(start_pos, from.length(), to);
  return true;
}

void load_new_rules(const string fileName = "rules_new.smt2")
{
  FILE* in;
  bool opended = false;

  if (!ifstream(
          fileName.c_str())) /// use stdin if the default file is not found.
  {
    // Silently blocking on a terminal looks like a hang, and reading rules
    // from a pipe by accident looks like there were none.
    cerr << "rewrite_rule_gen: no " << fileName << ", reading rules from stdin"
         << endl;
    in = stdin;
  }
  else
  {
    cerr << "rewrite_rule_gen: reading rules from " << fileName << endl;
    in = fopen(fileName.c_str(), "r");
    opended = true; // so we know to fclose it.
  }

  // We store references to "v" and "w". A symbol's source sort is part of its
  // identity, so these have to be made at the sort the parser will declare
  // them at -- LookupOrCreateSymbol leaves it Unknown, which interns a
  // *different* node from the one the rule blocks then talk about.
  v = mgr->CreateSourceSymbol("v", stp::SourceSort::bitVector(bits));
  w = mgr->CreateSourceSymbol("w", stp::SourceSort::bitVector(bits));

  TypeChecker nfTypeCheckDefault(*mgr->hashingNodeFactory, *mgr);
  Cpp_interface piTypeCheckDefault(*mgr, &nfTypeCheckDefault);
  mgr->UserFlags.print_STPinput_back_SMTLIB2_flag = true;
  GlobalParserInterface = &piTypeCheckDefault;

  // This file I/O code: 1) Is terrible  2) I'm in a big rush so just getting it
  // working 3) am embarised by it.
  while (!feof(in))
  {
    int id, verified_to_bits, time_used, from_v, to_v;

    string s;
    char line[63000];

    bool first = true;
    bool done = false;
    while (true)
    {
      if (fgets(line, sizeof line, in) == NULL)
      {
        done = true;
        break;
      }
      if (first)
      {
        int rv = sscanf(line, ";id:%d\tverified_to:%d\ttime:%d\tfrom_"
                              "difficulty:%d\tto_difficulty:%d\n",
                        &id, &verified_to_bits, &time_used, &from_v, &to_v);
        if (rv != 5)
        {
          cerr << line;
          done = true;
          break;
        }
        first = false;
        continue;
      }
      s += line;
      if (!strcmp(line, "(exit)\n"))
        break;
    }
    if (done)
      break;

    mgr->GetRunTimes()->start(RunTimes::Parsing);

    // The declarations are left in: the parser resolves a name through its
    // own binding frames and no longer falls back to the manager's symbol
    // table, so each block has to declare what it names. They intern to the
    // v and w above, which were made at the same sort.

    // Load it into a string because other wise the parser reads in big blocks
    // way past where we want it to.
    smt2_scan_string(s.c_str());
    smt2parse();
    ASTVec values = piTypeCheckDefault.GetAsserts();
    values = FlattenKind(AND, values);

    assert(values.size() == 1);

    // The nodes have been built with the hashing node factory.
    // In practice we want to match nodes that are created with the simplifying
    // NF.
    // If we enabled the simplifying NF, the EQUALS checks would remove rules we
    // want to keep.
    ASTNode from = withNF(values[0][0]);
    ASTNode to = withNF(values[0][1]);

    // Rule should be orderable.
    bool ok = orderEquivalence(from, to);
    if (!ok)
    {
      cout << "discarding rule that can't be ordered";
      cout << from << to;
      cout << "----";
      //mgr->PopQuery();
      GlobalParserInterface->popToFirstLevel();
      continue;
    }

    Rewrite_rule r(mgr, from, to, 0, id);
    r.setVerified(verified_to_bits, time_used);

    rewrite_system.push_back(r);

    //mgr->PopQuery();
    GlobalParserInterface->popToFirstLevel();
  }

  extern int smt2lex_destroy(void);
  smt2lex_destroy();

  GlobalParserInterface->cleanUp();
  GlobalParserInterface = NULL;
  if (opended)
  {
    cout << "New Style Rules Loaded:" << rewrite_system.size() << endl;
    fclose(in);
  }

  // So we don't output as soon as one is discovered...
  lastOutput = rewrite_system.size();
  mgr->GetRunTimes()->clear();
}

// Reads in new format rules. And tests each of them for the allocated time.
void expandRules(int timeout_ms, const char* fileName = "")
{
  load_new_rules(fileName);
  createVariables();

  for (Rewrite_system::RewriteRuleContainer::iterator it =
           rewrite_system.begin();
       it != rewrite_system.end(); it++)
  {
    VariableAssignment bad;
    int to_run = timeout_ms - it->getTime();
    if (to_run <= 0)
      continue;
    if ((*it).timedCheck(to_run, bad))
    {
      // NB. only writes out rules that have used less time than specified.
      it->writeOut(cout);
    }
  }
}

void t2()
{
  extern FILE* smt2in;

  smt2in = fopen("big_array.smt2", "r");
  TypeChecker nfTypeCheckDefault(*mgr->hashingNodeFactory, *mgr);
  Cpp_interface piTypeCheckDefault(*mgr, &nfTypeCheckDefault);
  GlobalParserInterface = &piTypeCheckDefault;

  mgr->GetRunTimes()->start(RunTimes::Parsing);
  smt2parse();

  ASTVec v = FlattenKind(AND, piTypeCheckDefault.GetAsserts());
  ASTNode n = nf->CreateNode(XOR, v);

  // rewrite(const ASTNode&n, const Rewrite_rule& original_rule, ASTNodeMap&
  // seen)
  ASTNodeMap seen;
  createVariables();
  ASTNode r = rename_then_rewrite(n, Rewrite_rule::getNullRule());
  cerr << r;
  GlobalParserInterface = NULL;
}

// loads the already existing rules.
void load_old_rules(string fileName)
{
  if (!ifstream(fileName.c_str()))
    return; // file doesn't exist.

  extern FILE* smt2in;

  smt2in = fopen(fileName.c_str(), "r");
  TypeChecker nfTypeCheckDefault(*mgr->hashingNodeFactory, *mgr);
  Cpp_interface piTypeCheckDefault(*mgr, &nfTypeCheckDefault);
  GlobalParserInterface = &piTypeCheckDefault;

  GlobalParserInterface->push(); // so the rules can be de-asserted.

  mgr->GetRunTimes()->start(RunTimes::Parsing);
  smt2parse();

  ASTVec values = piTypeCheckDefault.GetAsserts();
  values = FlattenKind(AND, values);

  cout << "Rewrite rule size:" << values.size() << endl;

  for (size_t i = 0; i < values.size(); i++)
  {
    if ((values[i].GetKind() != EQ))
    {
      cout << "Not equality??";
      cout << values[i];
      continue;
    }

    ASTNode from = values[i][0];
    ASTNode to = values[i][1];

    // Rule should be orderable.
    bool ok = orderEquivalence(from, to);
    if (!ok)
    {
      cout << "discarding rule that can't be ordered";
      cout << from << to;
      cout << "----";
      continue;
    }

    Rewrite_rule r(mgr, from, to, 0);

    rewrite_system.push_back(r);
  }

  //mgr->PopQuery();
  GlobalParserInterface->popToFirstLevel();
  GlobalParserInterface->cleanUp();
  GlobalParserInterface = NULL;

  rewrite_system.buildLookupTable();

  ASTVec vvv = mgr->GetAsserts();
  for (size_t i = 0; i < vvv.size(); i++)
    cout << vvv[i];

  // So we don't output as soon as one is discovered...
  lastOutput = rewrite_system.size();
}

void testProps()
{
  ASTNode a = mgr->CreateSymbol("a", 0, 0);
  ASTNode b = mgr->CreateSymbol("b", 0, 0);

  /////////////////////////// ITE(bv,bv,bv)
  doIte(a);

  /////////////////////////// Prop, Prop -> Prop
  Kind propKinds[] = {AND, OR, IMPLIES, XOR, IFF};
  int number_types = sizeof(propKinds) / sizeof(Kind);

  // Check that the propositions don't evaluate to true/false.
  for (int k = 0; k < number_types; k++)
    doProp(propKinds[k], a);
}

void test()
{
  // Test code.
  load_old_rules("test.smt2");

  v = mgr->LookupOrCreateSymbol("v");
  v.SetValueWidth(bits);

  v0 = mgr->LookupOrCreateSymbol("v0");
  v0.SetValueWidth(bits);

  w = mgr->LookupOrCreateSymbol("w");
  w.SetValueWidth(bits);

  w0 = mgr->LookupOrCreateSymbol("w0");
  w0.SetValueWidth(bits);

  writeOutRules();
  rewrite_system.verifyAllwithSAT();
  rewrite_system.clear();
}

// ---------------------------------------------------------------------------
// missed-constants: expressions the simplifying node factory left as
// expressions, when they can only ever take one value.
//
// Every two-level function and predicate over the two variables is built --
// no constant leaves, so nothing folds merely because a constant was handed
// in -- and each result the factory did not reduce to a constant is asked
// whether it is one anyway. (bvsub v v) is the shape being looked for.
//
// Constancy is "n agrees with a copy of itself over fresh variables, for
// every assignment", which needs no candidate value to be guessed. A
// concrete-evaluation filter runs first: a node taking two different values
// under two assignments needs no solver call at all.

// Substitutes concrete values for the variables. Every leaf is a constant
// afterwards, so the factory folds the result -- unless it is missing a fold,
// which is what this mode hunts, so the caller checks rather than assumes.
// The variables the enumeration is over, and a disjoint copy of each. The
// copies are what makes constancy decidable without guessing a value: n is
// constant exactly when it agrees with itself over fresh variables.
vector<ASTNode> mcVars;
vector<ASTNode> mcFresh;

// Substitutes concrete values for the variables. Every leaf is a constant
// afterwards, so the factory folds the result -- unless it is missing a fold,
// which is what this mode hunts, so the caller checks rather than assumes.
ASTNode evalAt(const ASTNode& n, const vector<ASTNode>& values)
{
  ASTNodeMap ft;
  for (size_t i = 0; i < mcVars.size(); i++)
    ft.insert(make_pair(mcVars[i], values[i]));
  ASTNodeMap cache;
  return SubstitutionMap::replace(n, ft, cache, nf);
}

bool isFolded(const ASTNode& n)
{
  return n.isConstant() || n == mgr->ASTTrue || n == mgr->ASTFalse;
}

// Distinct nodes in the DAG; used only to report the smallest findings first.
size_t nodeCount(const ASTNode& n, ASTNodeSet& seen)
{
  if (!seen.insert(n).second)
    return 0;
  size_t total = 1;
  for (size_t i = 0; i < n.Degree(); i++)
    total += nodeCount(n[i], seen);
  return total;
}

size_t nodeCount(const ASTNode& n)
{
  ASTNodeSet seen;
  return nodeCount(n, seen);
}

// True when n takes the same value at every sample. Wrong only in the safe
// direction: it can pass a node that is not constant, never reject one that
// is.
bool sameAtEverySample(const ASTNode& n, const vector<vector<ASTNode>>& samples,
                       ASTNode& value)
{
  value = evalAt(n, samples[0]);
  if (!isFolded(value))
    return false; // not folded even fully applied; not what this looks for

  for (size_t i = 1; i < samples.size(); i++)
    if (evalAt(n, samples[i]) != value)
      return false;
  return true;
}

// n is constant exactly when it agrees with a copy of itself over fresh
// variables, whatever they are assigned.
bool provablyConstant(const ASTNode& n)
{
  ASTNodeMap ft;
  for (size_t i = 0; i < mcVars.size(); i++)
    ft.insert(make_pair(mcVars[i], mcFresh[i]));
  ASTNodeMap cache;
  const ASTNode other = SubstitutionMap::replace(n, ft, cache, nf);

  const ASTNode agree = (n.GetType() == BOOLEAN_TYPE)
                            ? nf->CreateNode(IFF, n, other)
                            : nf->CreateNode(EQ, n, other);
  if (agree == mgr->ASTTrue)
    return true;
  return isConstantToSat(agree, -1);
}

// One more level of operators over `fromTerms`, appending to `terms` and
// `preds`. Unary, binary, and up to `maxArity` children for the kinds the AST
// lets take more than two. No constants are introduced anywhere.
void addLevel(const ASTVec& fromTerms, ASTVec& terms, ASTVec& preds,
              unsigned maxArity)
{
  static const Kind termUnary[] = {stp::BVNOT, stp::BVUMINUS};
  static const Kind termBinary[] = {
      stp::BVPLUS,       stp::BVSUB,   stp::BVMULT, stp::BVDIV,
      stp::BVMOD,        stp::SBVDIV,  stp::SBVREM, stp::SBVMOD,
      stp::BVAND,        stp::BVOR,    stp::BVXOR,  stp::BVLEFTSHIFT,
      stp::BVRIGHTSHIFT, stp::BVSRSHIFT};
  static const Kind predBinary[] = {stp::EQ,    stp::BVLT,  stp::BVLE,
                                    stp::BVGT,  stp::BVGE,  stp::BVSLT,
                                    stp::BVSLE, stp::BVSGT, stp::BVSGE};
  // The kinds that take a variable number of children.
  static const Kind termNary[] = {stp::BVPLUS, stp::BVMULT, stp::BVAND,
                                  stp::BVOR, stp::BVXOR};

  for (size_t i = 0; i < fromTerms.size(); i++)
  {
    for (size_t u = 0; u < sizeof(termUnary) / sizeof(Kind); u++)
    {
      ASTVec c;
      c.push_back(fromTerms[i]);
      terms.push_back(create(termUnary[u], c));
    }

    for (size_t j = 0; j < fromTerms.size(); j++)
    {
      for (size_t b = 0; b < sizeof(termBinary) / sizeof(Kind); b++)
        terms.push_back(create(termBinary[b], fromTerms[i], fromTerms[j]));
      for (size_t b = 0; b < sizeof(predBinary) / sizeof(Kind); b++)
        preds.push_back(create(predBinary[b], fromTerms[i], fromTerms[j]));
    }
  }

  // Three and more children, for the kinds that allow it. These are all
  // commutative and associative, so only non-decreasing index tuples are
  // built: any other order is the same node.
  for (unsigned arity = 3; arity <= maxArity; arity++)
  {
    vector<size_t> idx(arity, 0);
    while (true)
    {
      ASTVec c;
      for (unsigned a = 0; a < arity; a++)
        c.push_back(fromTerms[idx[a]]);
      for (size_t b = 0; b < sizeof(termNary) / sizeof(Kind); b++)
        terms.push_back(create(termNary[b], c));

      // Odometer over non-decreasing tuples.
      int a = (int)arity - 1;
      while (a >= 0 && ++idx[a] >= fromTerms.size())
        a--;
      if (a < 0)
        break;
      for (unsigned f = a + 1; f < arity; f++)
        idx[f] = idx[a];
    }
  }
}

void findMissedConstants(unsigned numVars, unsigned maxArity)
{
  mcVars.clear();
  mcFresh.clear();
  for (unsigned i = 0; i < numVars; i++)
  {
    std::stringstream a, b;
    a << "x" << i;
    b << "x" << i << "_fresh";
    ASTNode s0 = mgr->LookupOrCreateSymbol(a.str().c_str());
    s0.SetValueWidth(bits);
    ASTNode s1 = mgr->LookupOrCreateSymbol(b.str().c_str());
    s1.SetValueWidth(bits);
    mcVars.push_back(s0);
    mcFresh.push_back(s1);
  }

  // Corners first, then random: the corners are where the shift and division
  // edge cases live.
  vector<vector<ASTNode>> samples;
  const ASTNode corner[] = {mgr->CreateZeroConst(bits),
                            mgr->CreateOneConst(bits),
                            mgr->CreateMaxConst(bits)};
  for (size_t c = 0; c < 3; c++)
  {
    samples.push_back(vector<ASTNode>(numVars, corner[c]));
    for (unsigned i = 0; i < numVars; i++)
    {
      vector<ASTNode> one(numVars, mgr->CreateZeroConst(bits));
      one[i] = corner[c];
      samples.push_back(one);
    }
  }
  for (int r = 0; r < 12; r++)
  {
    vector<ASTNode> vals;
    for (unsigned i = 0; i < numVars; i++)
      vals.push_back(mgr->CreateBVConst(bits, rand() % (1 << bits)));
    samples.push_back(vals);
  }

  // No constant leaves: a fold that only fires because a constant was passed
  // in is not what this is looking for.
  ASTVec leaves(mcVars.begin(), mcVars.end());

  ASTVec terms(leaves), preds;
  addLevel(leaves, terms, preds, maxArity);
  removeDuplicates(terms);
  removeDuplicates(preds);
  cout << "one level:  " << terms.size() << " terms, " << preds.size()
       << " predicates" << endl;

  const ASTVec firstLevel(terms);
  addLevel(firstLevel, terms, preds, maxArity);
  removeDuplicates(terms);
  removeDuplicates(preds);
  cout << "two levels: " << terms.size() << " terms, " << preds.size()
       << " predicates" << endl;

  ASTVec all(terms);
  all.insert(all.end(), preds.begin(), preds.end());

  // The second level pairs the first with itself, so this grows fast enough
  // to be worth saying out loud before it runs for half an hour.
  if (all.size() > 1000000)
    cout << "note: " << all.size()
         << " expressions. Measured: 4 variables at arity 3 takes about half "
            "an hour and 1.2GB, and finds exactly what 2 variables at arity 3 "
            "finds in twenty seconds."
         << endl;

  unsigned candidates = 0, found = 0;

  // (op x0 x0) and (op x1 x1) are the same finding twice. Reporting is keyed
  // on the expression with every variable mapped to the first, which
  // collapses them.
  std::set<string> seen;
  vector<std::pair<size_t, string>> hits; // node count, text

  for (size_t i = 0; i < all.size(); i++)
  {
    const ASTNode& n = all[i];

    if (isFolded(n))
      continue; // the factory already reduced it; nothing missed here

    ASTNode value;
    if (!sameAtEverySample(n, samples, value))
      continue;

    candidates++;
    if (!provablyConstant(n))
      continue;

    ASTNodeMap ft;
    for (size_t k = 1; k < mcVars.size(); k++)
      ft.insert(make_pair(mcVars[k], mcVars[0]));
    ASTNodeMap cache;
    const ASTNode canonical =
        ft.empty() ? n : SubstitutionMap::replace(n, ft, cache, nf);

    std::stringstream key;
    printer::SMTLIB2_Print1(key, canonical, 0, false);
    if (!seen.insert(key.str()).second)
      continue;

    found++;

    std::stringstream line;
    printer::SMTLIB2_Print1(line, n, 0, false);
    line << "\n    is always ";
    printer::SMTLIB2_Print1(line, value, 0, false);
    hits.push_back(std::make_pair(nodeCount(n), line.str()));
  }

  // Smallest first: those are the ones worth teaching the factory.
  std::sort(hits.begin(), hits.end());
  for (size_t i = 0; i < hits.size(); i++)
    cout << "\n" << hits[i].second << endl;

  cout << "\nchecked " << all.size() << " expressions at " << bits
       << " bits over " << numVars << " variables, n-ary arity up to "
       << maxArity << "; " << candidates << " constant at every sample, "
       << found << " distinct shapes confirmed constant but not folded"
       << endl;
}

void createVariables()
{
  v = mgr->LookupOrCreateSymbol("v");
  v.SetValueWidth(bits);

  v0 = mgr->LookupOrCreateSymbol("v0");
  v0.SetValueWidth(bits);

  w = mgr->LookupOrCreateSymbol("w");
  w.SetValueWidth(bits);

  w0 = mgr->LookupOrCreateSymbol("w0");
  w0.SetValueWidth(bits);
}

void unit_test()
{

  // Create the negation and not terms in different orders. This tests the
  // commutative matching.
  ASTVec c;
  c.push_back(v);
  ASTNode not_v = create(stp::BVNOT, c);
  ASTNode neg_v = create(stp::BVUMINUS, c);

  ASTNode plus_v = create(BVPLUS, not_v, neg_v);

  c.clear();
  c.push_back(w);
  ASTNode neg_w = create(stp::BVUMINUS, c);
  ASTNode not_w = create(stp::BVNOT, c);
  ASTNode plus_w = create(BVPLUS, not_w, neg_w);

  ASTNodeMap sub;
  plus_w = renameVars(plus_w);
  assert(commutative_matchNode(plus_w, plus_v, sub, 2));
  sub.clear();

  assert(commutative_matchNode(plus_v, plus_w, sub, 1));
}

// The modes, and what each needs. Without this the only way to find out was
// to read main(): an unrecognised argument fell through every branch and the
// tool exited 0, so a typo looked exactly like success.
void usage()
{
  cout <<
      "usage: rewrite_rule_gen [mode [arguments]]\n"
      "\n"
      "Searches for bit-vector rewrite rules, and checks the ones already\n"
      "found. Rules are read from ./rules_new.smt2 where a mode needs them,\n"
      "and written back there.\n"
      "\n"
      "  (no arguments)        search for new rules, unbounded. Reads the\n"
      "                        current rule set from stdin if there is no\n"
      "                        rules_new.smt2.\n"
      "  generate D N          the same search, stopping at depth D or after\n"
      "                        N rules. -1 for either means no limit.\n"
      "  verify [FILE]         SAT-check every rule in FILE.\n"
      "  expand MS [FILE]      widen the bit-widths the rules are checked at,\n"
      "                        spending at most MS milliseconds on each.\n"
      "  rewrite               apply the rule set to itself and write it back.\n"
      "  write-out             re-emit the rule set, including its C++ form.\n"
      "  missed-constants [V A]\n"
      "                        build every two-level function and predicate\n"
      "                        over V variables, with no constant leaves and\n"
      "                        up to A children for the n-ary kinds, and\n"
      "                        report the ones the node factory left as\n"
      "                        expressions that can only take one value.\n"
      "                        Defaults to 4 variables and arity 3.\n"
      "  unit-test             check the commutative matcher. Needs no input.\n"
      "  test                  check the rule properties. Needs no input.\n"
      "\n"
      "The search prints its progress; it can run for a long time before it\n"
      "reports anything.\n";
}

int main(int argc, const char* argv[])
{
  if (argc > 1 && (!strcmp("--help", argv[1]) || !strcmp("-h", argv[1]) ||
                   !strcmp("help", argv[1])))
  {
    usage();
    return 0;
  }

  startup();

  if (argc == 1) // Read the current rule set, find new rules.
  {
    std::cout << "Waiting for rules, press enter to skip.";
    load_new_rules();
    createVariables();
    ////////////
    rewrite_system.buildLookupTable();

    Function_list functionList;
    functionList.buildAll();

    // The hash is generated on these values.
    vector<VariableAssignment> values;
    findRewrites(functionList.functions, values);

    cout << "Initial:" << bits << " widening to :" << widen_to << endl;
    cout << "Highest disproved @ level: " << highestLevel << endl;
    cout << highestDisproved << endl;
    ////////////

    rewrite_system.rewriteAll();
    writeOutRules();
  }
  else if (argc == 4 && !strcmp("generate", argv[1]))
  {
    // Bounded, non-interactive form of the argc == 1 mode above, for smoke
    // testing: "generate <max-depth> <max-rules>". Either bound may be -1 for
    // no limit, though with both unbounded this is the mode that exhausts the
    // stack. Rules found are written out as usual.
    max_search_depth = atoi(argv[2]);
    max_rules_wanted = atoi(argv[3]);
    cout << "Bounded search: max depth " << max_search_depth << ", max rules "
         << max_rules_wanted << endl;

    load_new_rules();
    createVariables();
    rewrite_system.buildLookupTable();

    Function_list functionList;
    functionList.buildAll();

    vector<VariableAssignment> values;
    findRewrites(functionList.functions, values);

    rewrite_system.rewriteAll();
    writeOutRules();
    cout << "Rules found: " << rewrite_system.size() << endl;
  }
  else if (argc == 2 && !strcmp("unit-test", argv[1]))
  {
    load_new_rules();
    createVariables();
    unit_test();
  }
  else if ((argc == 2 || argc == 3) && !strcmp("verify", argv[1]))
  {
    // "verify [file]" -- SAT-check every loaded rule. Without a file the rules
    // come from ./rules_new.smt2, or stdin when that does not exist.
    if (argc == 3)
    {
      // Fail rather than verify nothing. load_new_rules() falls back to stdin
      // when the file is missing, so a mistyped path would otherwise load zero
      // rules and report success.
      if (!ifstream(argv[2]))
      {
        cerr << "Cannot read rules file: " << argv[2] << endl;
        return 1;
      }
      load_new_rules(argv[2]);
      if (rewrite_system.size() == 0)
      {
        cerr << "No rules loaded from " << argv[2] << endl;
        return 1;
      }
    }
    else
      load_new_rules();

    cout << "Verifying " << rewrite_system.size() << " rules" << endl;
    rewrite_system.verifyAllwithSAT();
    cout << "Verified " << rewrite_system.size() << " rules" << endl;
  }
  else if ((argc == 4 || argc == 3) && !strcmp("expand", argv[1]))
  {
    // expand the bit-widths rules are tested at.
    int timeout_ms = atoi(argv[2]);
    assert(timeout_ms > 0);
    expandRules(timeout_ms, (argc == 4 ? argv[3] : ""));
  }
  else if (argc == 2 && !strcmp("rewrite", argv[1]))
  {
    // load the rules and apply the rewrite system to itself.
    load_new_rules();
    if (rewrite_system.size() == 0)
    {
      cerr << "rewrite_rule_gen: no rules to rewrite" << endl;
      return 1;
    }
    createVariables();
    rewrite_system.eraseDuplicates();
    rewrite_system.rewriteAll();
    writeOutRules();
  }
  else if (argc == 2 && !strcmp("write-out", argv[1]))
  {
    load_new_rules();
    if (rewrite_system.size() == 0)
    {
      // Otherwise this truncates rules_new.smt2 to nothing and reports success.
      cerr << "rewrite_rule_gen: no rules to write out" << endl;
      return 1;
    }
    createVariables();
    rewrite_system.rewriteAll();
    writeOutRules(); // have the times now..
  }
  else if (argc == 2 && !strcmp("test", argv[1]))
  {
    testProps();
  }
  else if (argc == 2 && !strcmp("test2", argv[1]))
  {
    load_new_rules();
    t2();
  }
  else if ((argc == 2 || argc == 4) && !strcmp("missed-constants", argv[1]))
  {
    const unsigned numVars = (argc == 4) ? atoi(argv[2]) : 4;
    const unsigned maxArity = (argc == 4) ? atoi(argv[3]) : 3;
    if (numVars < 1 || maxArity < 2)
    {
      cerr << "rewrite_rule_gen: missed-constants needs at least 1 variable "
              "and arity 2"
           << endl;
      return 1;
    }
    findMissedConstants(numVars, maxArity);
  }
  else
  {
    cerr << "rewrite_rule_gen: unrecognised mode";
    for (int i = 1; i < argc; i++)
      cerr << " " << argv[i];
    cerr << "\n\n";
    usage();
    return 1;
  }

  for (size_t i = 0; i < saved_array.size(); i++)
    delete saved_array[i];

  shutdown();
}

bool debug_matching = false;

/////////
// Term variables have a specified width!!!
// "false" if it definately can't be matched with any possible commutative
// ordering.
// "true" can be matched, later you need to check if all the "commutative" can
// be matched.
bool commutative_matchNode(const ASTNode& n0, const ASTNode& n1,
                           const int term_variable_width,
                           deque<pair<ASTNode, ASTNode>>& commutative,
                           ASTNode& vNode, ASTNode& wNode)
{
  // Pointers to the same value. OK.
  if (n0 == n1)
    return true;

  // If we try and match sub-terms of concatenations,e,g. 000::x = 000111, we
  // want it to fail.
  if (n0.GetValueWidth() != n1.GetValueWidth())
    return false;

  if (n0.GetKind() == SYMBOL && strlen(n0.GetName()) == (size_t)term_variable_width)
  {
    if (n0.GetName()[0] == 'v')
    {
      if (vNode != mgr->ASTUndefined)
        return commutative_matchNode(vNode, n1, term_variable_width,
                                     commutative, vNode, wNode);
      else
      {
        vNode = n1;
        return true;
      }
    }
    else if (n0.GetName()[0] == 'w')
    {
      if (wNode != mgr->ASTUndefined)
        return commutative_matchNode(wNode, n1, term_variable_width,
                                     commutative, vNode, wNode);
      else
      {
        wNode = n1;
        return true;
      }
    }
    else
      FatalError("nefeafs");
  }

  // Here:
  // They could be different BVConsts, different symbols, or
  // different functions.

  if (n0.Degree() != n1.Degree() || (n0.Degree() == 0))
    return false;

  if (n0.GetKind() != n1.GetKind())
    return false;

  // If it's commutative, check it specially / seprately later.
  if (isCommutative(n0.GetKind()) && n0.Degree() > 1)
  {
    commutative.push_back(make_pair(n0, n1));
    return true;
  }
  else
  {
    for (size_t i = 0; i < n0.Degree(); i++)
    {
      if (!commutative_matchNode(n0[i], n1[i], term_variable_width, commutative,
                                 vNode, wNode))
        return false;
    }
  }
  return true;
}

//
// Term variables have a specified width!!!
bool c_matchNode(const ASTNode& n0, const ASTNode& n1,
                 const int term_variable_width,
                 deque<pair<ASTNode, ASTNode>>& commutative_to_check,
                 ASTNode& vNode, ASTNode& wNode)
{
  ASTNode vNode_copy = vNode;
  ASTNode wNode_copy = wNode;

  const size_t init_comm_size = commutative_to_check.size();

  bool r = commutative_matchNode(n0, n1, term_variable_width,
                                 commutative_to_check, vNode, wNode);
  assert(commutative_to_check.size() >= init_comm_size);
  // if anything, only pushed onto the back.

  if (debug_matching)
  {
    cerr << "======Commut-match=======" << r << endl;
    cerr << "given" << n0 << n1;
    cerr << "Commutative still to match:" << endl;
    for (size_t j = 0; j < commutative_to_check.size(); j++)
    {
      cerr << "++++++++++" << endl;
      cerr << "first" << commutative_to_check[j].first;
      cerr << "second" << commutative_to_check[j].second;
    }
    cerr << "From To Map is:" << endl;
    cerr << "vNode" << vNode;
    cerr << "wNode" << wNode;
    cerr << "=============";
  }

  if (!r)
  {
    // If it's bad we restore it all back.
    commutative_to_check.erase(commutative_to_check.begin() + init_comm_size,
                               commutative_to_check.end());
    vNode = vNode_copy;
    wNode = wNode_copy;
    return false;
  }

  // base case.
  if (commutative_to_check.size() == 0)
    return r;

  pair<ASTNode, ASTNode> p = commutative_to_check.back();
  commutative_to_check.pop_back();
  assert(p.first.GetKind() == p.second.GetKind());
  const ASTChildren f = p.first.GetChildren();
  // Materialised, not a view: sorted in place below.
  ASTVec s = toASTVec(p.second.GetChildren());

  if (f.size() != s.size())
  {
    cerr << "different sized!!!";
    // If it's bad we restore it all back.
    if (commutative_to_check.size() < init_comm_size)
      commutative_to_check.push_back(p);
    else
      commutative_to_check.erase(commutative_to_check.begin() + init_comm_size,
                                 commutative_to_check.end());

    vNode = vNode_copy;
    wNode = wNode_copy;

    return false;
  }

  // The next_permutation function requires this.
  sort(s.begin(), s.end());

  ASTNode vNode_copy2 = vNode;
  ASTNode wNode_copy2 = wNode;

  // deque<pair<ASTNode, ASTNode> > todo_copy2 = commutative_to_check;
  const int new_comm_size = commutative_to_check.size();

  // Check each permutation of the commutative operation's operands.
  do
  {
    // Check each of the operands matches. Store Extra away in
    // "commutative_to_check".
    bool good = true;
    for (size_t i = 0; i < f.size(); i++)
    {
      if (!commutative_matchNode(f[i], s[i], term_variable_width,
                                 commutative_to_check, vNode, wNode))
      {
        good = false;
        break;
      }
    }

    // Empty out the "commutative_to_check".
    if (good)
      if (!c_matchNode(mgr->ASTTrue, mgr->ASTTrue, term_variable_width,
                       commutative_to_check, vNode, wNode))
        good = false;

    if (good)
    {
      assert(commutative_to_check.size() == 0);
      return true; // all match.
    }
    else
    {
      vNode = vNode_copy2;
      wNode = wNode_copy2;
      commutative_to_check.erase(commutative_to_check.begin() + new_comm_size,
                                 commutative_to_check.end());
      // assert(commutative_to_check == todo_copy2);
      // commutative_to_check = todo_copy2;
    }
  } while (next_permutation(s.begin(), s.end()));

  // None of the permutations match. We return the data unchanged.

  vNode = vNode_copy;
  wNode = wNode_copy;

  if (commutative_to_check.size() < init_comm_size)
    commutative_to_check.push_back(p);
  else
    commutative_to_check.erase(commutative_to_check.begin() + init_comm_size,
                               commutative_to_check.end());

  return false;
}

/* This does commutative matching of nodes. A substitution to the term variables
 *(which are the
 * those with a name of the width specified), of n0 is found. That is if the
 *variables of n0 are
 * substituted with the "substitution", then it will equal n1.
 *
 * Initially I thought commutative matching was easy to get right. NO!
 *
 * NB: This uses a "static" container so this can't be called recursively.
 */
bool in_commutative = false;

bool commutative_matchNode(const ASTNode& n0, const ASTNode& n1,
                           ASTNodeMap& substitution,
                           const int term_variable_width)
{
  assert(substitution.size() == 0);

  assert(!in_commutative);
  // because the container is static. Check there is only one at a time.
  in_commutative = true;

  static deque<pair<ASTNode, ASTNode>> commutative;
  commutative.clear();

  ASTNode vNode = mgr->ASTUndefined;
  ASTNode wNode = mgr->ASTUndefined;
  bool r = c_matchNode(n0, n1, term_variable_width, commutative, vNode, wNode);

  if (r)
  {
    vector<ASTNode> s = getVariables(n0);
    for (vector<ASTNode>::iterator it = s.begin(); it != s.end(); it++)
    {
      assert(it->GetKind() == SYMBOL);
      assert(strlen(it->GetName()) == (size_t)term_variable_width);
      if (it->GetName()[0] == 'v')
      {
        assert(vNode != mgr->ASTUndefined);
        assert(vNode.GetValueWidth() == it->GetValueWidth());
        substitution.insert(make_pair(*it, vNode));
      }
      if (it->GetName()[0] == 'w')
      {
        assert(wNode != mgr->ASTUndefined);
        assert(wNode.GetValueWidth() == it->GetValueWidth());
        substitution.insert(make_pair(*it, wNode));
      }
    }
  }

  if (debug_matching)
  {
    cerr << "=======" << endl
         << "The result is: " << r << "for the inputs" << n0 << n1 << "=-===";
  }

  if (!r)
  {
    assert(substitution.size() == 0);
    assert(commutative.size() == 0);
    // should be none left to process.
  }

  assert(in_commutative);
  in_commutative = false;
  return r;
}

ASTNode rewriteThroughWithAIGS(const ASTNode& n_)
{
  assert(n_.GetType() == BITVECTOR_TYPE);
  ASTNode f = mgr->LookupOrCreateSymbol("rewriteThroughWithAIGS");
  f.SetValueWidth(n_.GetValueWidth());
  ASTNode n = create(EQ, n_, f);

  BBNodeManagerAIG nm;
  BitBlasterAIG bb(&nm, simp, mgr->defaultNodeFactory, &mgr->UserFlags);
  ASTNodeMap fromTo;
  ASTNodeMap equivs;
  bb.getConsts(n, fromTo, equivs);

  ASTNode result = n_;
  if (equivs.size() > 0)
  {
    ASTNodeMap cache;
    result = SubstitutionMap::replace(result, equivs, cache, nf, false, true);
  }

  if (fromTo.size() > 0)
  {
    ASTNodeMap cache;
    result = SubstitutionMap::replace(result, fromTo, cache, nf);
  }
  return result;
}
