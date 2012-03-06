// This generates C++ code that implements automatically discovered rewrite rules.
// Expressions are generated, then pairwise checked over a range of bit-widths to see if they are the same.
// If they are the same, then C++ code is written out that implements the rule.

#include <ctime>
#include <vector>
#include <algorithm>
#include <iostream>
#include <fstream>

#include "../../AST/AST.h"
#include "../../printer/printers.h"

#include "../../STPManager/STPManager.h"
#include "../../to-sat/AIG/ToSATAIG.h"
#include "../../sat/MinisatCore.h"
#include "../../STPManager/STP.h"
#include "../../STPManager/DifficultyScore.h"
#include "../../simplifier/BigRewriter.h"
#include "../../AST/NodeFactory/TypeChecker.h"
#include "../../cpp_interface/cpp_interface.h"

#include "VariableAssignment.h"

#include "rewrite_rule.h"
#include "rewrite_system.h"
#include "Functionlist.h"

extern int
smt2parse();

using namespace std;
using namespace BEEV;

// Holds the rewrite that was disproved at the largest bitwidth.
ASTNode highestDisproved;
int highestLevel = 0;
int discarded = 0;

//static
int  Rewrite_rule::static_id;

//////////////////////////////////
const int bits = 6;
const int widen_to = 10;
const int values_in_hash = 64 / bits;
const int mask = (1 << (bits)) - 1;
//////////////////////////////////

// Set by the signal handler to write out the rules that have been discovered.
volatile bool force_writeout = false;

// Saves a little bit of time. The vectors are saved between invocations.
vector<ASTVec> saved_array;

// Stores the difficulties that have already been generated.
map<ASTNode, int> difficulty_cache;

Rewrite_system rewrite_system;

void
clearSAT();

void
createVariables();

template<class T>
  void
  removeDuplicates(T & big);

bool
is_candidate(ASTNode from, ASTNode to);

bool
isConstantToSat(const ASTNode & query);

string
containsNode(const ASTNode& n, const ASTNode& hunting, string& current);

void
writeOutRules();

int
getDifficulty(const ASTNode& n_);

vector<ASTNode>
getVariables(const ASTNode& n);

bool
unifyNode(const ASTNode& n0, const ASTNode& n1,  ASTNodeMap& fromTo, const int term_variable_width);

typedef HASHMAP<ASTNode, string, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> ASTNodeString;

BEEV::STPMgr* mgr;
NodeFactory* nf;
SATSolver * ss;
ASTNodeSet stored; // Store nodes so they aren't garbage collected.
Simplifier *simp;

ASTNode zero, one, maxNode, v, w, v0, w0;

// Width of the rewrite rules that were output last time.
int lastOutput = 0;


bool
checkRule(const ASTNode & from, const ASTNode & to, VariableAssignment& ass, bool& bad);

ASTNode
renameVars(const ASTNode &n)
{
  ASTNodeMap ft;

  assert(v.GetValueWidth() == v0.GetValueWidth());
  assert(w.GetValueWidth() == w0.GetValueWidth());

  ft.insert(make_pair(v, v0));
  ft.insert(make_pair(w, w0));

  ASTNodeMap cache;
  return SubstitutionMap::replace(n, ft, cache, nf);
}

ASTNode
renameVarsBack(const ASTNode &n)
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
ASTNode
create(Kind k, const ASTNode& n0, const ASTNode& n1)
{
  if (is_Term_kind(k))
    return nf->CreateTerm(k, n0.GetValueWidth(), n0, n1);
  else
    return nf->CreateNode(k, n0, n1);
}

ASTNode
create(Kind k, ASTVec& c)
{
  if (is_Term_kind(k))
    return nf->CreateTerm(k, c[0].GetValueWidth(), c);
  else
    return nf->CreateNode(k, c);
}

// Gets the name of the lhs in terms of the rhs.
// If it's a constant it's the name of the constant,
// otherwise it's the position of the lhs in the rhs. Otherwise empty.
string
getToName(const ASTNode& lhs, const ASTNode& rhs)
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
void
getVariables(const ASTNode& n, vector<ASTNode>& symbols, ASTNodeSet& visited)
{
  if (visited.find(n) != visited.end())
    return;
  visited.insert(n);

  if (n.GetKind() == SYMBOL && (find(symbols.begin(), symbols.end(), n) == symbols.end()))
    symbols.push_back(n);

  for (int i = 0; i < n.Degree(); i++)
    getVariables(n[i], symbols, visited);
}

vector<ASTNode>
getVariables(const ASTNode& n)
{
  vector<ASTNode> symbols;
  ASTNodeSet visited;
  getVariables(n, symbols, visited);

  return symbols;
}

// Get the constant from replacing values in the map.
ASTNode
eval(const ASTNode &n, ASTNodeMap& map, int count = 0)
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
    saved_array.push_back(ASTVec());

  ASTVec& new_children = saved_array[count];
  new_children.clear();

  for (int i = 0; i < n.Degree(); i++)
    new_children.push_back(eval(n[i], map, count + 1));

  ASTNode r = NonMemberBVConstEvaluator(mgr, n.GetKind(), new_children, n.GetValueWidth());
  map.insert(make_pair(n, r));
  return r;
}

bool
checkProp(const ASTNode& n)
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
        mapToVal.insert(make_pair(symbols[j], (0x1 & (i >> (j * bits))) == 0 ? mgr->ASTFalse : mgr->ASTTrue));

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

  cout << "is actually a const: " << "[" << value << "]" << n;
  return true;
}

// True if it's always true. Otherwise fills the assignment.
bool
isConstant(const ASTNode& n, VariableAssignment& different)
{
  if (isConstantToSat(n))
    return true;
  else
    {
      mgr->ValidFlag = false;

      vector<ASTNode> symbols = getVariables(n);
      assert(symbols.size() > 0);

      // Both of them might not be contained in the assignment.
      different.setV(mgr->CreateZeroConst(symbols[0].GetValueWidth()));
      different.setW(mgr->CreateZeroConst(symbols[0].GetValueWidth()));

      // It might have been widened.
      for (int i = 0; i < symbols.size(); i++)
        {
          if (strncmp(symbols[i].GetName(), "v", 1) == 0)
              different.setV(GlobalSTP->Ctr_Example->GetCounterExample(true, symbols[i]));
          else if (strncmp(symbols[i].GetName(), "w", 1) == 0)
              different.setW(GlobalSTP->Ctr_Example->GetCounterExample(true, symbols[i]));
        }
      return false;
    }
}

// Widens terms from "bits" to "width".
ASTNode
widen(const ASTNode& w, int width)
{
  assert(bits >=4);

  if (w.isConstant() && w.GetValueWidth() == 1)
    return w;

  if (w.isConstant() && w.GetValueWidth() == bits)
    return nf->CreateTerm(BVSX, width, w);

  if (w.isConstant() && w.GetValueWidth() == bits - 1)
    return nf->CreateTerm(BVSX, width - 1, w);

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

  if (w.GetKind() == BVCONCAT && ((ch[0].GetValueWidth() + ch[1].GetValueWidth()) != width))
    return mgr->ASTUndefined; // Didn't widen properly.

  // We got to the trouble below because sometimes we get 1-bit wide expressions which we don't
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
    result = nf->CreateTerm(BVCONCAT, ch[1].GetValueWidth() + ch[0].GetValueWidth(), ch);
  else if (w.GetKind() == ITE)
    result = nf->CreateTerm(ITE, ch[1].GetValueWidth(), ch);
  else if (w.GetKind() == BVSX)
    result = nf->CreateTerm(BVSX, ch[1].GetUnsignedConst(), ch);
  else
    result = nf->CreateTerm(w.GetKind(), ch[0].GetValueWidth(), ch);

  BVTypeCheck(result);
  return result;
}


bool
orderEquivalence(ASTNode& from, ASTNode& to)
{
  vector<ASTNode> s_from; // The variables in the from node.
  ASTNodeSet visited;
  getVariables(from, s_from, visited);
  std::sort(s_from.begin(), s_from.end());

  vector<ASTNode> s_to;  // The variables in the to node.
  visited.clear();
  getVariables(to, s_to, visited);
  sort(s_to.begin(), s_to.end());

  vector<ASTNode> result(s_to.size() + s_from.size());
  // We must map from most variables to fewer variables.
  vector<ASTNode>::iterator it = std::set_intersection(s_from.begin(), s_from.end(), s_to.begin(), s_to.end(),
      result.begin());
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

  if (getDifficulty(from) < getDifficulty(to))
    {
      swap(from, to);
      return true;
    }

  if (getDifficulty(from) > getDifficulty(to))
    {
      return true;
    }

  // Difficulty is equal. Order based on the number of nodes.
  vector<ASTNode> symbols;
  visited.clear();
  getVariables(from, symbols, visited);
  int from_c = visited.size();

  symbols.clear();
  visited.clear();
  getVariables(to, symbols, visited);
  int to_c = visited.size();

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

int
getDifficulty(const ASTNode& n_)
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
  BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&nm, simp, mgr->defaultNodeFactory, &mgr->UserFlags);

  // equals fresh variable to convert to boolean type.
  ASTNode f = mgr->CreateFreshVariable(0, widen_to, "ffff");
  ASTNode input = create(EQ, f, n);

  BBNodeAIG BBFormula = bb.BBForm(input);

  clearSAT();

  Cnf_Dat_t* cnfData = NULL;
  ToCNFAIG toCNF(mgr->UserFlags);
  ToSATBase::ASTNodeToSATVar nodeToSATVar;
  toCNF.toCNF(BBFormula, cnfData, nodeToSATVar, false, nm);

  // Why we go to all this trouble. The number of clauses.
  int score = cnfData->nClauses;

  //Cnf_ClearMemory();
  Cnf_DataFree(cnfData);
  cnfData = NULL;

  // Free the memory in the AIGs.
  BBFormula = BBNodeAIG(); // null node

  difficulty_cache.insert(make_pair(n_, score));
  return score;
}

// binary proposition.
void
doProp(Kind k, ASTNode a)
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
ASTNode
get(ASTNode a, int i, int pos)
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

void
doIte(ASTNode a)
{
  for (int i = 0; i < 64; i++)
    {
      ASTNode n = nf->CreateNode(ITE, get(a, i, 2), get(a, i, 1), get(a, i, 0));
      checkProp(n);
    }
}

void do_write_out(int ignore)
{
  force_writeout = true;
}


int
startup()
{
  CONSTANTBV::ErrCode ec = CONSTANTBV::BitVector_Boot();
  if (0 != ec)
    {
      cout << CONSTANTBV::BitVector_Error(ec) << endl;
      return 0;
    }

  mgr = new BEEV::STPMgr();
  BEEV::ParserBM = mgr;

  mgr->UserFlags.division_by_zero_returns_one_flag = true;

  simp = new Simplifier(mgr);
  ArrayTransformer * at = new ArrayTransformer(mgr, simp);
  AbsRefine_CounterExample* abs = new AbsRefine_CounterExample(mgr, simp, at);
  ToSAT* tosat = new ToSAT(mgr);

  GlobalSTP = new STP(mgr, simp, at, tosat, abs);

#ifndef NOTSIMPLIFYING_NF
  nf = new SimplifyingNodeFactory(*(mgr->hashingNodeFactory), *mgr);
  mgr->defaultNodeFactory = nf;
#else
  nf =  mgr->hashingNodeFactory;
  mgr->defaultNodeFactory = mgr->hashingNodeFactory;
#endif

  mgr->UserFlags.stats_flag = false;
  mgr->UserFlags.optimize_flag = true;

  ss = new MinisatCore<Minisat::Solver>(mgr->soft_timeout_expired);

  // Prime the cache with 100..
  for (int i = 0; i < 100; i++)
    {
      saved_array.push_back(ASTVec());
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
  signal(SIGUSR1,do_write_out);

}

void
clearSAT()
{
  delete ss;
  ss = new MinisatCore<Minisat::Solver>(mgr->soft_timeout_expired);
}

// Return true if the negation of the query is unsatisfiable.
bool
isConstantToSat(const ASTNode & query)
{
  assert(query.GetType() == BOOLEAN_TYPE);

  GlobalSTP->ClearAllTables();
  clearSAT();

  ASTNode query2 = nf->CreateNode(NOT, query);

  SOLVER_RETURN_TYPE r = GlobalSTP->Ctr_Example->CallSAT_ResultCheck(*ss, query2, query2, GlobalSTP->tosat, false);

  return (r == SOLVER_VALID); // unsat, always true
}

// Replaces the symbols in n, by each of the values, and concatenates them
// to turn it into a single 64-bit value.
uint64_t
getHash(const ASTNode& n_, const vector<VariableAssignment>& values)
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

  vector<ASTNode> symbols; // The variables in the n node.
  ASTNodeSet visited;
  getVariables(n, symbols, visited);

  uint64_t hash = 0;

  for (int i = 0; i < values.size(); i++)
    {
      ASTNodeMap mapToVal;
      for (int j = 0; j < symbols.size(); j++)
        {
          if (strncmp(symbols[j].GetName(), "v", 1) == 0)
            {
              mapToVal.insert(make_pair(symbols[j], values[i].getV()));
              assert(symbols[j].GetValueWidth() == values[i].getV().GetValueWidth());
            }
          else if (strncmp(symbols[j].GetName(), "w", 1) == 0)
            {
              mapToVal.insert(make_pair(symbols[j], values[i].getW()));
              assert(symbols[j].GetValueWidth() == values[i].getW().GetValueWidth());
            }
          else
            {
              cerr << "Unknown symbol!" << symbols[j];
              FatalError("f");
            }
          assert(symbols[j].GetValueWidth() == ass_bitwidth);
        }

      ASTNode r = eval(n, mapToVal);
      assert(r.isConstant());
      hash <<= ass_bitwidth;
      hash += r.GetUnsignedConst();
    }
  return hash;
}

// is from a sub-term of "to"?
bool
contained_in(ASTNode from, ASTNode to)
{
  if (from == to)
    return true;

  for (int i = 0; i < from.Degree(); i++)
    if (contained_in(from[i], to))
      return true;

  return false;
}

// Is mapping from "From" to "to" a rule we are interested in??
bool
is_candidate(ASTNode from, ASTNode to)
{
  if (to.Degree() == 0)
    return true; // Leaves are always good.

  if (contained_in(from, to))
    return true; // If what we are mapping to is contained in the "from", that's good too.

  return false;
}

bool
lessThan(const ASTNode& n1, const ASTNode& n2)
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

// Breaks the expressions into buckets recursively, then pairwise checks that they are equivalent.
void
findRewrites(ASTVec& expressions, const vector<VariableAssignment>& values, const int depth = 0)
{
  if (expressions.size() < 2)
    {
      discarded += expressions.size();
      return;
    }

  cout << '\n' << "depth:" << depth << ", size:" << expressions.size() << " values:" << values.size() << " found: "
      << rewrite_system.size() << " done:" << discarded << "\n";

  assert(expressions.size() >0);

  if (values.size() > 0)
    {
      if (values.size() > 10)
        removeDuplicates(expressions);

      // Put the functions in buckets based on their results on the values.
      HASHMAP<uint64_t, ASTVec> map;
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

      HASHMAP<uint64_t, ASTVec>::iterator it2;

      cout << "Split into " << map.size() << " pieces\n";

      int id = 1;
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
  std::sort(equiv.begin(), equiv.end(), lessThan);

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

          equiv[j] = rewrite_system.rewriteNode(equiv[j]);

          ASTNode from = equiv[i];
          ASTNode to = equiv[j];
          bool r = orderEquivalence(from, to);

          if (!r)
          {
            if (from != to)
                cout << "can't be ordered" << from << to;
            continue;
          }

          VariableAssignment different;
          bool bad = false;
          const int st = getCurrentTime();

          if (checkRule(from, to, different, bad))
            {
              cout << "Discovered a new rule.";
              cout << from;
              cout << to;
              cout << getDifficulty(from) << " to " << getDifficulty(to) << endl;
              cout << "After rewriting";
              cout << rewrite_system.rewriteNode(from);
              cout << rewrite_system.rewriteNode(to);
              cout << "------";

              Rewrite_rule rr(mgr, from, to, getCurrentTime() - st);

              if (!rr.timedCheck(10000))
                continue;

              rewrite_system.push_back(rr);

              // Remove the more difficult expression.
              if (from == equiv[i])
                {
                  cout << ".";
                  equiv[i] = mgr->ASTUndefined;
                }
              if (from == equiv[j])
                {
                  cout << ".";
                  equiv[j] = mgr->ASTUndefined;
                }
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
          if (force_writeout || lastOutput + 5000 < rewrite_system.size())
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
void
rule_to_string(const ASTNode & n, ASTNodeString& names, string& current, string& sofar)
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

  if (n.isConstant() && (n.GetValueWidth() == bits || n.GetValueWidth() == bits - 1))
    {
      sofar += "&& " + current + " == ";
      stringstream constant;
      constant << "bm->CreateBVConst(" << bits << "," << n.GetUnsignedConst() << ")";
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
  //if (current != "n")
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

string
containsNode(const ASTNode& n, const ASTNode& hunting, string& current)
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
bool
checkRule(const ASTNode & from, const ASTNode & to, VariableAssignment& assignment, bool&bad)
{
  ASTVec children;
  children.push_back(from);
  children.push_back(to);
  const ASTNode n = mgr->hashingNodeFactory->CreateNode(EQ, children);

  assert(widen_to > bits);

  for (int i = bits; i < widen_to; i++)
    {
      const ASTNode& widened = widen(n, i);

      // Can't widen (usually because of CONCAT or a BVCONST).
      if (widened == mgr->ASTUndefined)
        {
          cout << "cannot widen";
          //cerr << n;
          bad = true;
          return false;
        }

      // Send it to the SAT solver to verify that the widening has the same answer.
      bool result = isConstant(widened, assignment);

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

template<class T>
  void
  removeDuplicates(T & big)
  {
    cout << "Before removing duplicates:" << big.size();
    std::sort(big.begin(), big.end());
    typename T::iterator it = std::unique(big.begin(), big.end());
    big.erase(it, big.end());
    cout << ".After removing duplicates:" << big.size() << endl;
  }

// Hash function for the hash_map of a string..
template<class T>
  struct hashF
  {
    size_t
    operator()(const T & x) const
    {
      return __gnu_cxx::hash<const char*>()(x.c_str());
    }
  };

// Put all the inputs containing the substring together in the same bucket.
void
bucket(string substring, vector<string>& inputs, hash_map<string, vector<string>, hashF<std::string> >& buckets)
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
          //current = current.replace(from, to - from + 2, "/*" + val + " && */"); // Remove what we've searched for.
          //buckets[val].push_back(current);
          buckets[val].push_back(current);
        }
    }
}

string
name(const ASTNode& n)
{
  assert(n.GetValueWidth() ==32);
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
string
createString(ASTNode n, map<ASTNode, string>& val)
{
  if (val.find(n) != val.end())
    return val.find(n)->second;

  string result = "";

  if (n.GetKind() == BVCONST)
    {
      if (n.isConstant() && n.GetValueWidth() == 1 && n == mgr->CreateZeroConst(1))
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
          constant << "bm->CreateBVConst(" << bits << "," << n.GetUnsignedConst() << ")";
          result += "bm->CreateTerm(BVSX,width," + constant.str() + "";
        }

      if (n.isConstant() && (n.GetValueWidth() == bits - 1))
        {
          stringstream constant;
          constant << "bm->CreateBVConst(" << bits - 1 << "," << n.GetUnsignedConst() << ")";
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
void
visit_all(const ASTNode& n, map<ASTNode, string>& visited, string current)
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

template<class T>
  std::string
  to_string(T i)
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

// Write out all the rules that have been discovered to various files in different formats.
void
writeOutRules()
{
  force_writeout = false;

  std::vector<string> output;
  std::map<string, Rewrite_rule> dup;

  for (Rewrite_system::RewriteRuleContainer::iterator it = rewrite_system.toWrite.begin() ; it != rewrite_system.toWrite.end(); it++)
    {
      if (!it->isOK())
        {
          rewrite_system.erase(it--);
          continue;
        }

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
                  cout << "-----";
                  cout << sofar;

                  ASTNode f = it->getFrom();
                  cout << f << std::endl;
                  cout << dup.find(sofar)->second.getFrom();

                  ASTNodeMap fromTo;

                  cerr << f;
                  f = renameVars(f);
                  //cerr << "renamed" << f;
                  bool result = unifyNode(f,dup.find(sofar)->second.getFrom(),fromTo,2) ;
                  cout << "unified" << result << endl;
                  ASTNodeMap seen;
                  cout << rewrite(f,*it,seen );

                  // The text of this rule is the same as another rule.
                  rewrite_system.erase(it--);
                  continue;
                }
              else
                dup.insert(make_pair(sofar,*it));
            }
        }
    }

  // Remove the duplicates from output.
  removeDuplicates(output);

  cout << "Rules Discovered in total: " << rewrite_system.size() << endl;

  // Group functions of the same kind all together.
  hash_map<string, vector<string>, hashF<std::string> > buckets;
  bucket("n.GetKind() ==", output, buckets);

  ofstream outputFile;
  outputFile.open("rewrite_data_new.cpp", ios::trunc);

  // output the C++ code.
  hash_map<string, vector<string>, hashF<std::string> >::const_iterator it;
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

  ///////////////
  outputFile.open("rules_new.smt2", ios::trunc);
  for (Rewrite_system::RewriteRuleContainer::iterator it = rewrite_system.toWrite.begin() ; it != rewrite_system.toWrite.end(); it++)
  {
      it->writeOut(outputFile);
  }
  outputFile.close();

  /////////////////
  outputFile.open("array.smt2", ios::trunc);
  ASTVec v;
  for (Rewrite_system::RewriteRuleContainer::iterator it = rewrite_system.toWrite.begin() ; it != rewrite_system.toWrite.end(); it++)
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

// ASSUMES that buildRewrite() has recently been run on the rules..

ASTNode
rename_then_rewrite(ASTNode n, const Rewrite_rule& original_rule)
{
  n = renameVars(n);
  ASTNodeMap seen;
  n = rewrite(n,original_rule,seen);
  return renameVarsBack(n);
}

// assumes the variables in n are two characters wide.
ASTNode
rewrite(const ASTNode&n, const Rewrite_rule& original_rule, ASTNodeMap& seen)
{
  if (n.isAtom())
    return n;

  // nb. won't rewrite through EQ etc.
  if (n.GetType() != BITVECTOR_TYPE)
    return n;

  ASTVec v;
  for (int i = 0; i < n.Degree(); i++)
    v.push_back(rewrite(n[i],original_rule,seen));

  assert(v.size() > 0);
  ASTNode n2;

  if (v!=n.GetChildren())
    n2 = mgr->CreateTerm(n.GetKind(), n.GetValueWidth(), v);
  else
    n2 = n;

  ASTNodeMap fromTo;

  vector<Rewrite_rule>& rr =
      n[0].Degree() > 0 ?
      (rewrite_system.kind_kind_to_rr[n.GetKind()][n[0].GetKind()]) :
      (rewrite_system.kind_to_rr[n.GetKind()]) ;


  for (int i = 0; i < rr.size(); i++)
    {
      // If they are the same rule. Then don't match them.
      if (original_rule.sameID(rr[i]))
        continue;

      if (fromTo.size() > 0)
        fromTo.clear();

      const ASTNode& f = rr[i].getFrom();

      if (unifyNode(f, n2, fromTo,1))
        {
          /*
          cerr << "Unifying" << f;
          cerr << "with:" << n2;

          cerr << "Now" << rr[i].getTo();
          cerr << "reducing rule" << rr[i].getN();

          for (ASTNodeMap::iterator it = fromTo.begin(); it != fromTo.end(); it++)
            {
              cerr << it->first << "to" << it->second << endl;
            }

          cerr << "--------------";
           */

          if (seen.find(n) != seen.end())
            return seen.find(n)->second;

          seen.insert(make_pair(n,rr[i].getTo()));
          ASTNodeMap cache;
          ASTNode r=  SubstitutionMap::replace(rr[i].getTo(), fromTo, cache, nf, false, true);
          seen.erase(n);

          seen.insert(make_pair(n,r));
          r= rewrite(r,original_rule,seen);
          seen.erase(n);
          seen.insert(make_pair(n,r));
          return r;
        }
    }

  return n2;
}

int smt2_scan_string(const char *yy_str);

// http://stackoverflow.com/questions/3418231/c-replace-part-of-a-string-with-another-string
bool replace(std::string& str, const std::string& from, const std::string& to) {
    size_t start_pos = str.find(from);
    if(start_pos == std::string::npos)
        return false;
    str.replace(start_pos, from.length(), to);
    return true;
}


void
loadNewRules()
{
  FILE * in;
  bool opended= false;
  string fileName = "rules_new.smt2"

  if(!ifstream(fileName.c_str())) /// use stdin if the default file is not found.
    in = stdin;
  else
    {
      in = fopen(fileName.c_str(), "r");
      opended = true; // so we know to fclose it.
    }

  // We store references to "v" and "w", so we need to removed the
  // definitions from the input we parse.

  v = mgr->LookupOrCreateSymbol("v");
  v.SetValueWidth(bits);
  w = mgr->LookupOrCreateSymbol("w");
  w.SetValueWidth(bits);

  TypeChecker nfTypeCheckDefault(*mgr->hashingNodeFactory, *mgr);
  Cpp_interface piTypeCheckDefault(*mgr, &nfTypeCheckDefault);
  mgr->UserFlags.print_STPinput_back_SMTLIB2_flag = true;
  parserInterface = &piTypeCheckDefault;

  stringstream v_ss, w_ss;
  v_ss << "(declare-fun v () (_ BitVec " << bits << "))";
  string v_string = v_ss.str();

  w_ss << "(declare-fun w () (_ BitVec " << bits << "))";
  string w_string = w_ss.str();

  // This file I/O code: 1) Is terrible  2) I'm in a big rush so just getting it working 3) am embarised by it.
  while (!feof(in))
    {
      int id, verified_to_bits, time_used, from_v, to_v;

      string s;
      char line [63000];

      bool first = true;
      bool done = false;
      while (true)
        {
        fgets ( line, sizeof line, in );
        if (first)
          {
            int rv = sscanf(line, ";id:%d\tverified_to:%d\ttime:%d\tfrom_difficulty:%d\tto_difficulty:%d\n", &id, &verified_to_bits, &time_used, &from_v, &to_v);
            if (rv !=5)
              {
                done = true;
                break;
              }
            first = false;
            continue;
          }
        s+= line;
        if (!strcmp(line,"(exit)\n"))
          break;
        }
      if (done)
        break;

      mgr->GetRunTimes()->start(RunTimes::Parsing);

      replace(s,v_string,"");
      replace(s,w_string,"");

      // Load it into a string because other wise the parser reads in big blocks way past where we want it to.
      smt2_scan_string(s.c_str());
      smt2parse();
      ASTVec values = piTypeCheckDefault.GetAsserts();
      values = FlattenKind(AND, values);

      assert(values.size() ==1);

      ASTNode from = values[0][0];
      ASTNode to = values[0][1];

      // Rule should be orderable.
      bool ok = orderEquivalence(from, to);
      if (!ok)
        {
          cout << "discarding rule that can't be ordered";
          cout << from << to;
          cout << "----";
          continue;
        }

      Rewrite_rule r(mgr, from, to, 0, id);
      r.setVerified(verified_to_bits,time_used);

      assert(r.isOK());
      rewrite_system.push_back(r);

      mgr->PopQuery();
      parserInterface->popToFirstLevel();
    }

  parserInterface->cleanUp();
  if (opended)
   fclose(in);

  cout << "New Style Rules Loaded:" << rewrite_system.size() << endl;
}

//read from stdin, then tests it until the timeout.
void
expandRules(int timeout_ms)
{
  loadNewRules();
  createVariables();

  for (Rewrite_system::RewriteRuleContainer::iterator it = rewrite_system.begin(); it!= rewrite_system.end();it++)
    {
      if ((*it).timedCheck(timeout_ms))
        it->writeOut(cout); // omit failed.
    }
}

// loads the already existing rules.
void loadExistingRules(string fileName)
{
  if(!ifstream(fileName.c_str()))
     return; // file doesn't exist.

  extern FILE *smt2in;

  smt2in = fopen(fileName.c_str(), "r");
  TypeChecker nfTypeCheckDefault(*mgr->hashingNodeFactory, *mgr);
  Cpp_interface piTypeCheckDefault(*mgr, &nfTypeCheckDefault);
  parserInterface = &piTypeCheckDefault;

  parserInterface->push(); // so the rules can be de-asserted.

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

      if (r.isOK());
        rewrite_system.push_back(r);
    }

  mgr->PopQuery();
  parserInterface->popToFirstLevel();
  parserInterface->cleanUp();

  rewrite_system.buildLookupTable();

  ASTVec vvv = mgr->GetAsserts();
  for (int i=0; i < vvv.size() ;i++)
    cout << vvv[i];

  // So we don't output as soon as one is discovered...
  lastOutput = rewrite_system.size();
}

void
testProps()
{
  ASTNode a = mgr->CreateSymbol("a", 0, 0);
  ASTNode b = mgr->CreateSymbol("b", 0, 0);

  /////////////////////////// ITE(bv,bv,bv)
  doIte(a);

  /////////////////////////// Prop, Prop -> Prop
  Kind propKinds[] =
    { AND, OR, IMPLIES, XOR, IFF };
  int number_types = sizeof(propKinds) / sizeof(Kind);

  // Check that the propositions don't evaluate to true/false.
  for (int k = 0; k < number_types; k++)
    doProp(propKinds[k], a);
}

int test()
{
  // Test code.
  loadExistingRules("test.smt2");

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

void
createVariables()
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

int
main(int argc, const char* argv[])
{
  startup();

  if (argc == 1) // Read the current rule set, find new rules.
    {
        loadExistingRules("array.smt2");
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
  else if (argc == 3 && !strcmp("expand",argv[1])) // expand the bit-widths rules are tested at.
    {
      int timeout_ms = atoi(argv[2]);
      assert(timeout_ms > 0);
      expandRules(timeout_ms);
    }
  else if (argc == 2 && !strcmp("verify-all",argv[1]))
    {
      loadNewRules();
      createVariables();
      rewrite_system.verifyAllwithSAT();
      writeOutRules(); // have the times now..
    }
  else if (argc == 2 && !strcmp("write-out",argv[1]))
    {
      loadNewRules();
      createVariables();
      rewrite_system.rewriteAll();
      writeOutRules(); // have the times now..
    }
  else if (argc == 2 && !strcmp("test",argv[1]))
    {
      testProps();
    }
  else if (argc == 2 && !strcmp("delete-failed",argv[1]))
    {
      loadNewRules();
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
}



// Term variables have a specified width!!!
bool
unifyNode(const ASTNode& n0, const ASTNode& n1,  ASTNodeMap& fromTo, const int term_variable_width)
{
  // Pointers to the same value. OK.
  if (n0 == n1)
    return true;

  if (n0.GetKind() == SYMBOL && strlen(n0.GetName()) == term_variable_width)
    {
      if (fromTo.find(n0) != fromTo.end())
        return unifyNode(fromTo.find(n0)->second, n1, fromTo, term_variable_width);

      fromTo.insert(make_pair(n0, n1));
      return unifyNode(fromTo.find(n0)->second, n1, fromTo, term_variable_width);
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
      if (!unifyNode(n0[i], n1[i], fromTo, term_variable_width))
        return false;
    }

  return true;
}
