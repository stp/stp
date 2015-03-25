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

// This generates C++ code that implements automatically discovered rewrite
// rules.
// Expressions are generated, then pairwise checked over a range of bit-widths
// to see if they are the same.
// If they are the same, then C++ code is written out that implements the rule.

#include <ctime>
#include <vector>
#include <algorithm>
#include <iostream>
#include <fstream>

#include "stp/AST/AST.h"
#include "stp/Printer/printers.h"

#include "stp/STPManager/STPManager.h"
//#include "stp/To-sat/AIG/ToSATAIG.h"
#include "stp/Sat/MinisatCore.h"
#include "stp/STPManager/STP.h"
#include "stp/STPManager/DifficultyScore.h"
#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/AST/NodeFactory/TypeChecker.h"
#include "stp/cpp_interface.h"

#include "stp/Util/find_rewrites/VariableAssignment.h"

#include "stp/Util/find_rewrites/rewrite_rule.h"
#include "stp/Util/find_rewrites/rewrite_system.h"
#include "stp/Util/find_rewrites/Functionlist.h"
#include "stp/Util/find_rewrites/misc.h"
#include "stp/ToSat/AIG/BBNodeManagerAIG.h"
#include "stp/ToSat/AIG/ToCNFAIG.h"
#include "stp/ToSat/AIG/ToSATAIG.h"
#include "stp/ToSat/BitBlaster.h"

#include <sstream>
#include <fstream>
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
const int bits = 6;
const int widen_to = 10;
const int values_in_hash = 64 / bits;
const int mask = (1 << (bits)) - 1;
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

string containsNode(const ASTNode& n, const ASTNode& hunting, string& current);

void writeOutRules();

int getDifficulty(const ASTNode& n_);

vector<ASTNode> getVariables(const ASTNode& n);

bool matchNode(const ASTNode& n0, const ASTNode& n1, ASTNodeMap& fromTo,
               const int term_variable_width);

typedef hash_map<ASTNode, string, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
    ASTNodeString;

stp::STPMgr* mgr;
NodeFactory* nf;

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
  for (int i = 0; i < n.Degree(); i++)
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

// Gets the name of the lhs in terms of the rhs.
// If it's a constant it's the name of the constant,
// otherwise it's the position of the lhs in the rhs. Otherwise empty.
string getToName(const ASTNode& lhs, const ASTNode& rhs)
{
  string name = "n";
  if (!lhs.isConstant())
    name = containsNode(rhs, lhs, name);
  else if (lhs == mgr->CreateZeroConst(lhs.GetValueWidth()))
    name = "zero";
  else if (lhs == mgr->CreateOneConst(lhs.GetValueWidth()))
    name = "one";
  else if (lhs == mgr->CreateMaxConst(lhs.GetValueWidth()))
    name = "max";
  else
    name = "";

  return name;
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

  for (int i = 0; i < n.Degree(); i++)
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
  if (count >= saved_array.size())
    saved_array.push_back(new ASTVec());

  ASTVec& new_children = *saved_array[count];
  new_children.clear();

  for (int i = 0; i < n.Degree(); i++)
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
  int value;

  if (n.isConstant())
    return true;

  for (int i = 0; i < pow(2, symbols.size()); i++)
  {
    ASTNodeMap mapToVal;
    for (int j = 0; j < symbols.size(); j++)
      mapToVal.insert(make_pair(symbols[j], (0x1 & (i >> (j * bits))) == 0
                                                ? mgr->ASTFalse
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
      else if (value != nd.GetUnsignedConst())
        return false;
    }
  }

  cout << "is actually a const: "
       << "[" << value << "]" << n;
  return true;
}

// True if it's always true, otherwise fills the assignment.
bool isConstant(const ASTNode& n, VariableAssignment& different,
                const int bit_width)
{
  if (isConstantToSat(n))
    return true;
  else
  {
    mgr->ValidFlag = false;

    vector<ASTNode> symbols = getVariables(n);

    // Both of them might not be contained in the assignment,
    // (which might have been widened).
    ASTNode vN = mgr->CreateZeroConst(bit_width);
    ASTNode wN = mgr->CreateZeroConst(bit_width);

    for (int i = 0; i < symbols.size(); i++)
    {
      assert(symbols[i].GetValueWidth() == bit_width);

      if (strncmp(symbols[i].GetName(), "v", 1) == 0)
        vN = GlobalSTP->Ctr_Example->GetCounterExample(true, symbols[i]);
      else if (strncmp(symbols[i].GetName(), "w", 1) == 0)
        wN = GlobalSTP->Ctr_Example->GetCounterExample(true, symbols[i]);
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
  for (int i = 0; i < w.Degree(); i++)
  {
    ch.push_back(widen(w[i], width));
    if (ch.back() == mgr->ASTUndefined)
      return mgr->ASTUndefined;
  }

  if (w.GetKind() == BVCONCAT &&
      ((ch[0].GetValueWidth() + ch[1].GetValueWidth()) != width))
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

bool orderEquivalence_not_yet(ASTNode& from, ASTNode& to)
{
  if (from.IsNull())
    return false;
  if (from.GetKind() == UNDEFINED)
    return false;
  if (to.IsNull())
    return false;
  if (to.GetKind() == UNDEFINED)
    return false;

  {
    ASTVec c;
    c.push_back(from);
    c.push_back(to);
    ASTNode w = widen(mgr->hashingNodeFactory->CreateNode(EQ, c), widen_to);

    if (w.IsNull() || w.GetKind() == UNDEFINED)
      return false;
  }

  vector<ASTNode> s_from; // The variables in the from node.
  ASTNodeSet visited;
  getVariables(from, s_from, visited);
  std::sort(s_from.begin(), s_from.end());
  const int from_c = visited.size();

  vector<ASTNode> s_to; // The variables in the to node.
  visited.clear();
  getVariables(to, s_to, visited);
  sort(s_to.begin(), s_to.end());
  const int to_c = visited.size();

  if (from_c > 50 || to_c > 50)
    return false; // not interested in giant rules.

  vector<ASTNode> result(s_to.size() + s_from.size());
  // We must map from most variables to fewer variables.
  vector<ASTNode>::iterator it = std::set_intersection(
      s_from.begin(), s_from.end(), s_to.begin(), s_to.end(), result.begin());
  int intersection = it - result.begin();

  if (intersection != s_from.size() && intersection != s_to.size())
    return false;

  if (to.isAtom() && from.isAtom())
    return false; // no such rules

  if (to == from)
    return false; // no such rules

  if (to.isAtom())
    return true;

  if (from.isAtom())
  {
    std::swap(from, to);
    return true;
  }

  // Is one a subgraph of another.
  if (is_candidate(from, to))
  {
    return true;
  }

  if (is_candidate(to, from))
  {
    std::swap(from, to);
    return true;
  }

  if (s_from.size() < s_to.size())
  {
    swap(to, from);
    return true;
  }

  if (s_from.size() > s_to.size())
    return true;

  if ((getDifficulty(from) + 5) < getDifficulty(to))
  {
    swap(from, to);
    return true;
  }

  if (getDifficulty(from) > (getDifficulty(to) + 5))
  {
    return true;
  }

  if (to_c < from_c)
  {
    return true;
  }

  if (to_c > from_c)
  {
    swap(from, to);
    return true;
  }

  // Can't order they have the same number of nodes and the same AIG size.
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
  BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&nm, simp, mgr->defaultNodeFactory,
                                             &mgr->UserFlags);

  // equals fresh variable to convert to boolean type.
  ASTNode f = mgr->CreateFreshVariable(0, widen_to, "ffff");
  ASTNode input = create(EQ, f, n);

  BBNodeAIG BBFormula = bb.BBForm(input);

  clearSAT();

  Cnf_Dat_t* cnfData = NULL;
  ToCNFAIG toCNF(mgr->UserFlags);
  ToSATBase::ASTNodeToSATVar nodeToSATVar;
  toCNF.toCNF(BBFormula, cnfData, nodeToSATVar, false, nm);

  // Send the clauses to Minisat, do unit propagation.
  ///////////////

  // Create a new sat variable for each of the variables in the CNF.
  assert(ss->nVars() == 0);
  for (int i = 0; i < cnfData->nVars; i++)
    ss->newVar();

  SATSolver::vec_literals satSolverClause;
  for (int i = 0; i < cnfData->nClauses; i++)
  {
    satSolverClause.clear();
    for (int* pLit = cnfData->pClauses[i], *pStop = cnfData->pClauses[i + 1];
         pLit < pStop; pLit++)
    {
      uint32_t var = (*pLit) >> 1;
      assert((var < ss->nVars()));
      Minisat::Lit l = SATSolver::mkLit(var, (*pLit) & 1);
      satSolverClause.push(l);
    }

    ss->addClause(satSolverClause);
  }

  ss->simplify();
  assert(ss->okay());
  // should be satisfiable.

  // Why we go to all this trouble. The number of clauses.
  const int score = ss->nClauses();
  assert(score <= cnfData->nClauses);
  //////////////

  // Cnf_ClearMemory();
  Cnf_DataFree(cnfData);
  cnfData = NULL;

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

void do_write_out(int ignore)
{
  difficulty_cache.clear();
  force_writeout = true;
}

volatile bool debug_usr2 = false;

// toggle.
void do_usr2(int ignore)
{
  debug_usr2 = !debug_usr2;
}

int startup()
{
  CONSTANTBV::ErrCode ec = CONSTANTBV::BitVector_Boot();
  if (0 != ec)
  {
    cout << CONSTANTBV::BitVector_Error(ec) << endl;
    return 0;
  }

  mgr = new stp::STPMgr();
  stp::GlobalParserBM = mgr;

  mgr->UserFlags.division_by_zero_returns_one_flag = true;

  simp = new Simplifier(mgr);
  ArrayTransformer* at = new ArrayTransformer(mgr, simp);
  AbsRefine_CounterExample* abs = new AbsRefine_CounterExample(mgr, simp, at);
  ToSATAIG* tosat = new ToSATAIG(mgr, at);

  GlobalSTP = new STP(mgr, simp, at, tosat, abs);

  mgr->defaultNodeFactory =
      new SimplifyingNodeFactory(*mgr->hashingNodeFactory, *mgr);
  nf = new TypeChecker(*mgr->defaultNodeFactory, *mgr);

  mgr->UserFlags.stats_flag = false;
  mgr->UserFlags.optimize_flag = true;

  ss = new MinisatCore;

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

void clearSAT()
{
  delete ss;
  ss = new MinisatCore;

  delete GlobalSTP->tosat;
  ToSATAIG* aig = new ToSATAIG(mgr, GlobalSTP->arrayTransformer);
  GlobalSTP->tosat = aig;
}

// Return true if the negation of the query is unsatisfiable.
bool isConstantToSat(const ASTNode& query)
{
  assert(query.GetType() == BOOLEAN_TYPE);

  GlobalSTP->ClearAllTables();
  clearSAT();

  ASTNode query2 = nf->CreateNode(NOT, query);

  assert(ss->nClauses() == 0);
  mgr->AddQuery(mgr->ASTUndefined);
  SOLVER_RETURN_TYPE r = GlobalSTP->Ctr_Example->CallSAT_ResultCheck(
      *ss, query2, query2, GlobalSTP->tosat, false);

  return (r == SOLVER_VALID); // unsat, always true
}

// Replaces the symbols in n, by each of the values, and concatenates them
// to turn it into a single 64-bit value.
uint64_t getHash(const ASTNode& n_, const vector<VariableAssignment>& values)
{
  assert(values.size() > 0);
  const int ass_bitwidth = values[0].getV().GetValueWidth();
  assert(ass_bitwidth >= bits);

  ASTNode n = n_;

  // The values might be at a higher bit-width.
  if (ass_bitwidth > bits)
    n = widen(n_, ass_bitwidth);

  if (n == mgr->ASTUndefined) // Can't be widened.
    return 0;

  vector<ASTNode> symbols = getVariables(n);

  uint64_t hash = 0;

  for (int j = 0; j < symbols.size(); j++)
  {
    assert(symbols[j].GetValueWidth() == ass_bitwidth);
  }

  for (int i = 0; i < values.size(); i++)
  {
    // They both should be set..
    assert(values[i].getV().GetValueWidth() == ass_bitwidth);
    assert(values[i].getW().GetValueWidth() == ass_bitwidth);

    ASTNodeMap mapToVal;
    for (int j = 0; j < symbols.size(); j++)
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

  for (int i = 0; i < from.Degree(); i++)
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

  for (int i = 0; i < h.Degree(); i++)
    if (is_subgraph(g, h[i]))
      return true;

  return false;
}

bool lessThan(const ASTNode& n1, const ASTNode& n2)
{
  bool n1_bad = n1.IsNull() || (n1.GetKind() == UNDEFINED);
  bool n2_bad = n2.IsNull() || (n2.GetKind() == UNDEFINED);

  if (n1_bad && !n2_bad)
    return true;

  if (!n1_bad && n2_bad)
    return false;

  if (n1_bad && n2_bad)
    return false;

  return getDifficulty(n1) < getDifficulty(n2);
}

// Breaks the expressions into buckets recursively, then pairwise checks that
// they are equivalent.
void findRewrites(ASTVec& expressions, const vector<VariableAssignment>& values,
                  const int depth = 0)
{
  if (expressions.size() < 2)
  {
    discarded += expressions.size();
    return;
  }

  cout << '\n' << "depth:" << depth << ", size:" << expressions.size()
       << " values:" << values.size() << " found: " << rewrite_system.size()
       << " done:" << discarded << "\n";

  assert(expressions.size() > 0);

  if (values.size() > 0)
  {
    const int old_size = values.size();
    if (old_size > 10)
      removeDuplicates(expressions);

    discarded += (old_size - values.size());

    // Put the functions in buckets based on their results on the values.
    hash_map<uint64_t, ASTVec> map;
    for (int i = 0; i < expressions.size(); i++)
    {
      if (expressions[i] == mgr->ASTUndefined)
        continue; // omit undefined.

      if (i % 50000 == 49999)
        cout << ".";
      uint64_t hash = getHash(expressions[i], values);
      if (map.find(hash) == map.end())
        map.insert(make_pair(hash, ASTVec()));
      map[hash].push_back(expressions[i]);
    }
    expressions.clear();

    hash_map<uint64_t, ASTVec>::iterator it2;

    cout << "Split into " << map.size() << " pieces\n";
    if (depth > 0)
    {
      assert(map.size() > 0);
    }

    for (it2 = map.begin(); it2 != map.end(); it2++)
    {
      ASTVec& equiv = it2->second;
      vector<VariableAssignment> a;
      findRewrites(equiv, a, depth + 1);
      equiv.clear();
    }
    return;
  }
  ASTVec& equiv = expressions;

  // Sort so that constants, and smaller expressions will be checked first.
  // std::sort(equiv.begin(), equiv.end(), lessThan);

  for (int i = 0; i < equiv.size(); i++)
  {
    if (equiv[i].GetKind() == UNDEFINED)
      continue;

    // nb. I haven't rebuilt the map, it's done by writeOutRules().
    equiv[i] == rewrite_system.rewriteNode(equiv[i]);

    for (int j = i + 1; j < equiv.size(); j++) /// commutative so skip some.
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
      const long st = getCurrentTime();

      if (checkRule(from, to, different, bad))
      {
        const long checktime = getCurrentTime() - st;

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
            findRewrites(equiv, ass, depth + 1);
            return;
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
        ASTVec newEquiv(equiv.begin() + std::max(i - 1, 0), equiv.end());
        equiv.clear();

        findRewrites(newEquiv, ass, depth + 1);
        return;
      }

      // Write out the rules intermitently.
      if (force_writeout || lastOutput + 500 < rewrite_system.size())
      {
        rewrite_system.rewriteAll();
        writeOutRules();
        lastOutput = rewrite_system.size();
      }
    }
  }
  discarded += expressions.size();
}

// Converts the node into an IF statement that matches the node.
void rule_to_string(const ASTNode& n, ASTNodeString& names, string& current,
                    string& sofar)
{

  if (n.isConstant() && n.GetValueWidth() == 1 && n == mgr->CreateZeroConst(1))
  {
    sofar += "&& " + current + " == bm->CreateZeroConst(1) ";
    return;
  }
  if (n.isConstant() && n.GetValueWidth() == 1 && n == mgr->CreateOneConst(1))
  {
    sofar += "&& " + current + " == bm->CreateOneConst(1) ";
    return;
  }

  if (n.isConstant() &&
      (n.GetValueWidth() == bits || n.GetValueWidth() == bits - 1))
  {
    sofar += "&& " + current + " == ";
    stringstream constant;
    constant << "bm->CreateBVConst(" << bits << "," << n.GetUnsignedConst()
             << ")";
    sofar += "bm->CreateTerm(BVSX,width," + constant.str() + ")";
    return;
  }

  if (n.isConstant() && n.GetValueWidth() == 32) // Extract DEFINATELY.
  {
    if (n == mgr->CreateZeroConst(32))
    {
      sofar += "&& " + current + " == bm->CreateZeroConst(32) ";
      return;
    }

    if (n == mgr->CreateOneConst(32))
    {
      sofar += "&& " + current + " == bm->CreateOneConst(32) ";
      return;
    }

    if (n == mgr->CreateBVConst(32, bits))
    {
      sofar += "&& " + current + " == bm->CreateBVConst(32, width) ";
      return;
    }

    if (n == mgr->CreateBVConst(32, bits - 1))
    {
      sofar += "&& " + current + " == bm->CreateBVConst(32, width-1) ";
      return;
    }

    if (n == mgr->CreateBVConst(32, bits - 2))
    {
      sofar += "&& " + current + " == bm->CreateBVConst(32, width-2) ";
      return;
    }
  }

  if (n.isConstant())
  {
    sofar += " !!! !!! ";
  }

  if (names.find(n) != names.end())
    sofar += "&& " + current + " == " + names.find(n)->second + " ";

  names.insert(make_pair(n, current));

  if (n.isAtom())
    return;

  sofar += "&& " + current + ".GetKind() == " + _kind_names[n.GetKind()] + " ";

  // constrain to being == 2 for those that can be flattened.
  // if (current != "n")
  switch (n.GetKind())
  {
    case BVXOR:
    case BVMULT:
    case BVPLUS:
    case BVOR:
    case BVAND:
      sofar += "&& " + current + ".Degree() ==2 ";
      break;
  }

  for (int i = 0; i < n.Degree(); i++)
  {
    char t[1000];
    sprintf(t, "%s[%d]", current.c_str(), i);
    string s(t);
    rule_to_string(n[i], names, s, sofar);
  }

  return;
}

string containsNode(const ASTNode& n, const ASTNode& hunting, string& current)
{
  if (n == hunting)
    return current;

  if (n.isAtom())
    return "";

  for (int i = 0; i < n.Degree(); i++)
  {
    char t[1000];
    sprintf(t, "%s[%d]", current.c_str(), i);
    string s(t);
    string r = containsNode(n[i], hunting, s);
    if (r != "")
      return r;
  }

  return "";
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
  cout << "Before removing duplicates:" << big.size();
  std::sort(big.begin(), big.end());
  typename T::iterator it = std::unique(big.begin(), big.end());
  big.erase(it, big.end());
  cout << ".After removing duplicates:" << big.size() << endl;
}

// Put all the inputs containing the substring together in the same bucket.
void bucket(string substring, vector<string>& inputs,
            hash_map<string, vector<string>>& buckets)
{
  for (int i = 0; i < inputs.size(); i++)
  {
    string current = inputs[i];
    size_t from = current.find(substring);
    if (from == string::npos)
    {
      buckets[""].push_back(current);
    }
    else
    {
      size_t to = current.find("&&", from);
      string val = current.substr(from, to - from);
      // current = current.replace(from, to - from + 2, "/*" + val + " && */");
      // // Remove what we've searched for.
      // buckets[val].push_back(current);
      buckets[val].push_back(current);
    }
  }
}

string name(const ASTNode& n)
{
  assert(n.GetValueWidth() == 32);
  // Widen a constant used in an extract only.

  if (n == mgr->CreateBVConst(32, bits))
    return "width";
  if (n == mgr->CreateBVConst(32, bits - 1))
    return "width-1";
  if (n == mgr->CreateBVConst(32, bits - 2))
    return "width-2";
  if (n == mgr->CreateZeroConst(32))
    return "0";
  if (n == mgr->CreateOneConst(32))
    return "1";

  FatalError("@!#$@#$@#");
}

// Turns "n" into a statement in STP's C++ language to create it.
string createString(ASTNode n, std::map<ASTNode, string>& val)
{
  if (val.find(n) != val.end())
    return val.find(n)->second;

  string result = "";

  if (n.GetKind() == BVCONST)
  {
    if (n.isConstant() && n.GetValueWidth() == 1 &&
        n == mgr->CreateZeroConst(1))
    {
      result = "bm->CreateZeroConst(1";
    }
    if (n.isConstant() && n.GetValueWidth() == 1 && n == mgr->CreateOneConst(1))
    {
      result = "bm->CreateOneConst(1";
    }

    if (n.isConstant() && (n.GetValueWidth() == bits))
    {
      stringstream constant;
      constant << "bm->CreateBVConst(" << bits << "," << n.GetUnsignedConst()
               << ")";
      result += "bm->CreateTerm(BVSX,width," + constant.str() + "";
    }

    if (n.isConstant() && (n.GetValueWidth() == bits - 1))
    {
      stringstream constant;
      constant << "bm->CreateBVConst(" << bits - 1 << ","
               << n.GetUnsignedConst() << ")";
      result += "bm->CreateTerm(BVSX,width-1," + constant.str() + "";
    }

    if (n.isConstant() && n.GetValueWidth() == 32) // Extract DEFINATELY.
    {
      if (n == mgr->CreateZeroConst(32))
        result += " bm->CreateZeroConst(32 ";

      if (n == mgr->CreateOneConst(32))
        result += " bm->CreateOneConst(32 ";

      if (n == mgr->CreateBVConst(32, bits))
        result = " bm->CreateBVConst(32, width ";

      if (n == mgr->CreateBVConst(32, bits - 1))
        result = "  bm->CreateBVConst(32, width-1 ";

      if (n == mgr->CreateBVConst(32, bits - 2))
        result = "  bm->CreateBVConst(32, width-2 ";
    }

    if (result == "")
    {
      // uh oh.
      result = "~~~~~~~!!!!!!!!~~~~~~~~~~~";
    }
  }

  else if (n.GetType() == BOOLEAN_TYPE)
  {
    char buf[100];
    sprintf(buf, "bm->CreateNode(%s,", _kind_names[n.GetKind()]);
    result += buf;
  }
  else if (n.GetKind() == BVEXTRACT)
  {
    std::stringstream ss;
    ss << "bm->CreateTerm(BVEXTRACT,";

    ss << name(n[2]) << " +1 - (" << name(n[1]) << "),"; // width.
    ss << createString(n[0], val) << ",";
    ss << "bm->CreateBVConst(32," << name(n[1]) << "),"; // top then bottom.
    ss << "bm->CreateBVConst(32," << name(n[2]) << ")";

    result += ss.str();
  }
  else if (n.GetType() == BITVECTOR_TYPE)
  {
    char buf[100];
    sprintf(buf, "bm->CreateTerm(%s,width,", _kind_names[n.GetKind()]);
    result += buf;
  }
  else
  {
    cerr << n;
    cerr << "never here";
    exit(1);
  }

  if (n.GetKind() != BVEXTRACT)
    for (int i = 0; i < n.Degree(); i++)
    {
      if (i > 0)
        result += ",";

      result += createString(n[i], val);
    }
  result += ")";

  val.insert(make_pair(n, result));
  return result;
}

// loads all the expressions in "n" into the list of available expressions.
void visit_all(const ASTNode& n, map<ASTNode, string>& visited, string current)
{
  if (visited.find(n) != visited.end())
    return;

  visited.insert(make_pair(n, current));

  for (int i = 0; i < n.Degree(); i++)
  {
    char t[1000];
    sprintf(t, "%s[%d]", current.c_str(), i);
    string s(t);
    visit_all(n[i], visited, s);
  }
}

template <class T> std::string to_string(T i)
{
  std::stringstream ss;
  ss << i;
  return ss.str();
}

/* Writes out:
 * rewrite_data_new.cpp: rules coded in C++.
 * array.cpp: rules in SMT2 in one big conjunct.
 * rules_new.smt2: rules in SMT2 one rule per frame.
 */

// Write out all the rules that have been discovered to various files in
// different formats.
void writeOutRules()
{
  cout << "Writing out: " << rewrite_system.size() << " rules" << endl;
  force_writeout = false;

#if 0
  std::vector<string> output;
  std::map<string, Rewrite_rule> dup;

  for (Rewrite_system::RewriteRuleContainer::iterator it = rewrite_system.toWrite.begin();
      it != rewrite_system.toWrite.end(); it++)
    {
      ASTNode to = it->getTo();
      ASTNode from = it->getFrom();

      // If the RHS is just part of the LHS, then we output something like children[0][1][0][1] as the RHS.
      string to_name = getToName(to, from);

      if (to_name == "")
        {
          // The name is not contained in the rhs.
          ASTNodeSet visited;
          vector<ASTNode> symbols;

          getVariables(to, symbols, visited);
          map<ASTNode, string> val;
          for (int i = 0; i < symbols.size(); i++)
            val.insert(make_pair(symbols[i], getToName(symbols[i], from)));

          val.insert(make_pair(one, "one"));
          val.insert(make_pair(maxNode, "max"));
          val.insert(make_pair(zero, "zero"));

          // loads all the expressions in the rhs into the list of available expressions.
          visit_all(from, val, "n");

          to_name = createString(to, val);
        }

      ASTNodeString names;
      string current = "n";
      string sofar = "if ( width >= " + to_string(bits) + " ";

      rule_to_string(from, names, current, sofar);
      sofar += ")    set(result,  " + to_name + ");";

//      if (sofar.find("!!!") == std::string::npos && sofar.length() < 500)
        {
            {
              char buf[100];
              sprintf(buf, "//%d -> %d | %d ms\n", getDifficulty(from), getDifficulty(to), 0 /*toWrite[i].time*/);
              sofar += buf;
              output.push_back(sofar);

              if (dup.find(sofar) != dup.end())
                {
                  cout << "-----Writing out has found a duplicate rule-----";
                  cout << sofar;

                  ASTNode f = it->getFrom();
                  cout << "This:" << f << std::endl;
                  cout << "Has the same text as this: " << dup.find(sofar)->second.getFrom();

                  ASTNodeMap fromTo;
                  f = renameVars(f);
                  bool result = commutative_matchNode(f, dup.find(sofar)->second.getFrom(), fromTo, 2);
                  cout << "Has it unified:" << result << endl;
                  ASTNodeMap seen;

                  // The text of this rule is the same as another rule.
                  rewrite_system.erase(it--);
                  continue;
                }
              else
                dup.insert(make_pair(sofar, *it));
            }
        }
    }

  // Remove the duplicates from output.
  removeDuplicates(output);

  cout << "Rules Discovered in total: " << rewrite_system.size() << endl;


  // Group functions of the same kind all together.
  hash_map<string, vector<string> > buckets;
  bucket("n.GetKind() ==", output, buckets);
#endif

  ofstream outputFile;

// Because we output the difficulty (i.e. the number of CNF clauses),
// this is very slow.
#ifdef OUTPUT_CPP_RULES
  outputFile.open("rewrite_data_new.cpp", ios::trunc);

  // output the C++ code.
  hash_map<string, vector<string>>::const_iterator it;
  for (it = buckets.begin(); it != buckets.end(); it++)
  {
    outputFile << "if (" + it->first + ")" << endl;
    outputFile << "{" << endl;
    vector<string>::const_iterator it2 = it->second.begin();
    for (; it2 != it->second.end(); it2++)
      outputFile << *it2;

    outputFile << "}" << endl;
  }
  outputFile.close();
#endif

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
    printer::SMTLIB2_PrintBack(outputFile, n, true);
  }
  outputFile.close();
}

ASTNode replace_withRR(ASTNode n)
{
  ASTNodeMap cache;
  return rewrite(n, Rewrite_rule::getNullRule(), cache, 0);
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
  for (int i = 0; i < n.Degree(); i++)
    v.push_back(rewrite(n[i], original_rule, seen, depth + 1));

  assert(v.size() > 0);
  ASTNode n2;

  if (v != n.GetChildren())
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

  for (int i = 0; i < rr.size(); i++)
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
    in = stdin;
  else
  {
    in = fopen(fileName.c_str(), "r");
    opended = true; // so we know to fclose it.
  }

  // We store references to "v" and "w", so we need to remove the
  // definitions from the input we parse.

  v = mgr->LookupOrCreateSymbol("v");
  v.SetValueWidth(bits);
  w = mgr->LookupOrCreateSymbol("w");
  w.SetValueWidth(bits);

  TypeChecker nfTypeCheckDefault(*mgr->hashingNodeFactory, *mgr);
  Cpp_interface piTypeCheckDefault(*mgr, &nfTypeCheckDefault);
  mgr->UserFlags.print_STPinput_back_SMTLIB2_flag = true;
  GlobalParserInterface = &piTypeCheckDefault;

  stringstream v_ss, w_ss;
  v_ss << "(declare-fun v () (_ BitVec " << bits << "))";
  string v_string = v_ss.str();

  w_ss << "(declare-fun w () (_ BitVec " << bits << "))";
  string w_string = w_ss.str();

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
      fgets(line, sizeof line, in);
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

    replace(s, v_string, "");
    replace(s, w_string, "");

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
      mgr->PopQuery();
      GlobalParserInterface->popToFirstLevel();
      continue;
    }

    Rewrite_rule r(mgr, from, to, 0, id);
    r.setVerified(verified_to_bits, time_used);

    rewrite_system.push_back(r);

    mgr->PopQuery();
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

  for (int i = 0; i < values.size(); i++)
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

  mgr->PopQuery();
  GlobalParserInterface->popToFirstLevel();
  GlobalParserInterface->cleanUp();
  GlobalParserInterface = NULL;

  rewrite_system.buildLookupTable();

  ASTVec vvv = mgr->GetAsserts();
  for (int i = 0; i < vvv.size(); i++)
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

int test()
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
  ASTNode not_v = create(stp::BVNEG, c);
  ASTNode neg_v = create(stp::BVUMINUS, c);

  ASTNode plus_v = create(BVPLUS, not_v, neg_v);

  c.clear();
  c.push_back(w);
  ASTNode neg_w = create(stp::BVUMINUS, c);
  ASTNode not_w = create(stp::BVNEG, c);
  ASTNode plus_w = create(BVPLUS, not_w, neg_w);

  ASTNodeMap sub;
  plus_w = renameVars(plus_w);
  assert(commutative_matchNode(plus_w, plus_v, sub, 2));
  sub.clear();

  assert(commutative_matchNode(plus_v, plus_w, sub, 1));
}

int main(int argc, const char* argv[])
{
  startup();

  if (argc == 1) // Read the current rule set, find new rules.
  {
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
  else if (argc == 2 && !strcmp("unit-test", argv[1]))
  {
    load_new_rules();
    createVariables();
    unit_test();
  }
  else if (argc == 2 && !strcmp("verify", argv[1]))
  {
    load_new_rules();
    rewrite_system.verifyAllwithSAT();
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
    createVariables();
    rewrite_system.eraseDuplicates();
    rewrite_system.rewriteAll();
    writeOutRules();
  }
  else if (argc == 2 && !strcmp("write-out", argv[1]))
  {
    load_new_rules();
    createVariables();
    rewrite_system.rewriteAll();
    writeOutRules(); // have the times now..
  }
  else if (argc == 2 && !strcmp("test", argv[1]))
  {
    testProps();
  }
#if 0
  else if (argc == 2 && !strcmp("delete-failed",argv[1]))
    {
      load_new_rules();
      ifstream fin;
      fin.open("failed.txt",ios::in);
      char line[256];
      while (!fin.eof())
        {
          fin.getline(line,256);
          int id;
          sscanf(line,"FAILED:%d",&id);
          //cerr << "Failed id: " << id << endl;
          rewrite_system.deleteID(id);
        }
      createVariables();
      writeOutRules();
    }
#endif
  else if (argc == 2 && !strcmp("test2", argv[1]))
  {
    load_new_rules();
    t2();
  }

  for (int i = 0; i < saved_array.size(); i++)
    delete saved_array[i];
}

#if 0
// Term variables have a specified width!!!
bool
matchNode(const ASTNode& n0, const ASTNode& n1, ASTNodeMap& fromTo, const int term_variable_width)
  {
    // Pointers to the same value. OK.
    if (n0 == n1)
    return true;

    if (n0.GetKind() == SYMBOL && strlen(n0.GetName()) == term_variable_width)
      {
        if (fromTo.find(n0) != fromTo.end())
        return matchNode(fromTo.find(n0)->second, n1, fromTo, term_variable_width);

        fromTo.insert(make_pair(n0, n1));
        return matchNode(fromTo.find(n0)->second, n1, fromTo, term_variable_width);
      }

    // Here:
    // They could be different BVConsts, different symbols, or
    // different functions.

    if (n0.Degree() != n1.Degree() || (n0.Degree() == 0))
    return false;

    if (n0.GetKind() != n1.GetKind())
    return false;

    for (int i = 0; i < n0.Degree(); i++)
      {
        if (!matchNode(n0[i], n1[i], fromTo, term_variable_width))
        return false;
      }

    return true;
  }
#endif

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

  if (n0.GetKind() == SYMBOL && strlen(n0.GetName()) == term_variable_width)
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
    for (int i = 0; i < n0.Degree(); i++)
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

  const int init_comm_size = commutative_to_check.size();

  bool r = commutative_matchNode(n0, n1, term_variable_width,
                                 commutative_to_check, vNode, wNode);
  assert(commutative_to_check.size() >= init_comm_size);
  // if anything, only pushed onto the back.

  if (debug_matching)
  {
    cerr << "======Commut-match=======" << r << endl;
    cerr << "given" << n0 << n1;
    cerr << "Commutative still to match:" << endl;
    for (int j = 0; j < commutative_to_check.size(); j++)
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
  const ASTVec& f = p.first.GetChildren();
  ASTVec s = p.second.GetChildren(); // non-const, needs to be sorted later.

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
    for (int i = 0; i < f.size(); i++)
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

#ifdef PEDANTIC_MATCHING_ASSERTS
  {
    // There shouldn't be any term variables on the RHS.
    vector<ASTNode> vars = getVariables(n1);
    vector<ASTNode>::iterator it = vars.begin();
    while (it != vars.end())
    {
      assert(strlen(it->GetName()) != term_variable_width);
      assert(it->GetName()[0] == 'v' || it->GetName()[0] == 'w');
      it++;
    }
    assert(vars.size() <= 2);

    // All the LHS variables should be term variables.
    vars = getVariables(n0);
    it = vars.begin();
    while (it != vars.end())
    {
      assert(strlen(it->GetName()) == term_variable_width);
      it++;
    }
    assert(vars.size() <= 2);
  }

#endif

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
      assert(strlen(it->GetName()) == term_variable_width);
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
    cerr << "=======" << endl << "The result is: " << r << "for the inputs"
         << n0 << n1 << "=-===";
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
  BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&nm, simp, mgr->defaultNodeFactory,
                                             &mgr->UserFlags);
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
