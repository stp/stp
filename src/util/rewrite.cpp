// This generates C++ code that implements automatically discovered rewrite rules.
// Expressions are generated, then pairwise checked over a range of bit-widths to see if they are the same.
// If they are the same, then C++ code is written out that implements the rule.

#include <ctime>
#include <vector>
#include <algorithm>
#include <iostream>
#include <fstream>

#include "../AST/AST.h"
#include "../printer/printers.h"

#include "../STPManager/STPManager.h"
#include "../to-sat/AIG/ToSATAIG.h"
#include "../sat/MinisatCore.h"
#include "../STPManager/STP.h"
#include "../STPManager/DifficultyScore.h"
#include "../simplifier/BigRewriter.h"


using namespace std;
using namespace BEEV;

// Asynchronously stop solving.
bool finished = false;

// Holds the rewrite that was disproved at the largest bitwidth.
ASTNode highestDisproved;
int highestLevel =0;

//////////////////////////////////
const int bits = 6;
const int widen_to = 10;
const int values_in_hash = 64 / bits;
const int mask = (1 << (bits)) - 1;
//////////////////////////////////

// Saves a little bit of time. The vectors are saved between invocations.
vector<ASTVec> saved_array;

// Stores the difficulties that have already been generated.
map<ASTNode, int> difficulty_cache;

void
clearSAT();

bool
isConstantToSat(const ASTNode & query);

string
containsNode(const ASTNode& n, const ASTNode& hunting, string& current);

void
writeOutRules();

void applyBigRewrite(ASTVec& functions);

typedef HASHMAP<ASTNode, string, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> ASTNodeString;

BEEV::STPMgr* mgr;
NodeFactory* nf;
SATSolver * ss;
ASTNodeSet stored; // Store nodes so they aren't garbage collected.
Simplifier *simp;

ASTNode zero, one, maxNode, v, w;

struct ToWrite
{
  ASTNode from;
  ASTNode to;
  ASTNode n;
  int time;

  ToWrite()
  {
  }

  ToWrite(ASTNode from_, ASTNode to_, int t)
  {
    from = from_;
    to = to_;
    time = t;
    n = mgr->CreateNode(EQ,to,from);
  }

  bool isEmpty()
  {
    return (n == mgr->ASTUndefined);
  }

  bool
  operator==(const ToWrite t) const
  {
    return (n == t.n);
  }

  bool
  operator<(const ToWrite t) const
  {
    return (n < t.n);
  }
};

// Rules to write out when we get the chance.
vector<ToWrite> toWrite;

// Width of the rewrite rules that were output last time.
int lastOutput = 0;


struct Assignment
{
private:
  ASTNode v;
  ASTNode w;

public:
  ASTNode
  getV() const
  {
    assert(v.isConstant());
    return v;
  }

  ASTNode
  getW() const
  {
    assert(w.isConstant());
    return w;
  }

  void
  setV(const ASTNode& nv)
  {
    assert(nv.isConstant());
    v = nv;
  }

  void
  setW(const ASTNode& nW)
  {
    assert(nW.isConstant());
    w = nW;
  }

  bool isEmpty()
  {
    return (v == mgr->ASTUndefined || w == mgr->ASTUndefined);
  }

  Assignment()
  {
  }

  // Generate w from v a bit randomly.
  explicit
  Assignment(const ASTNode & n)
  {
    setV(n);
    srand(v.GetUnsignedConst());
    w = BEEV::ParserBM->CreateBVConst(n.GetValueWidth(), rand());
  }

  Assignment(ASTNode & n0, ASTNode & n1)
  {
    setV(n0);
    setV(n1);
  }
};

bool
checkAndStoreRule(const ASTNode & from, const ASTNode & to, Assignment& ass);


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

  if(n.Degree() == 0 )
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
isConstant(const ASTNode& n, Assignment& different)
{
  if (isConstantToSat(n))
    return true;
  else
    {
      vector<ASTNode> symbols;
      ASTNodeSet visited;
      getVariables(n,symbols,visited);
      assert(symbols.size() > 0);

      // Both of them might not be contained in the assignment.
      different.setV(mgr->CreateBVConst(symbols[0].GetValueWidth(),0));
      different.setW(mgr->CreateBVConst(symbols[0].GetValueWidth(),0));

      // It might have been widened.
      for (int i =0; i < symbols.size();i++)
        {
          if (strncmp(symbols[i].GetName(), "v", 1) ==0)
            different.setV(GlobalSTP->Ctr_Example->GetCounterExample(true, symbols[i]));
          else if (strncmp(symbols[i].GetName(), "w", 1) ==0)
            different.setW(GlobalSTP->Ctr_Example->GetCounterExample(true, symbols[i]));
        }
      return false;
    }
}

// Widens terms from "bits" to "width".
ASTNode
widen(const ASTNode& w, int width)
{
  assert(bits >=3);

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

  ASTNode result;
  if (w.GetType() == BOOLEAN_TYPE)
    result = nf->CreateNode(w.GetKind(), ch);
  else if (w.GetKind() == BVEXTRACT)
    {
      int new_width = ch[1].GetUnsignedConst() - ch[2].GetUnsignedConst() + 1;
      result = nf->CreateTerm(w.GetKind(), new_width, ch);
    }
  else
    result = nf->CreateTerm(w.GetKind(), width, ch);

        BVTypeCheck(result);
  return result;
}


ASTNode
rewriteThroughWithAIGS(const ASTNode &n)
{
  assert(n.GetKind() == EQ);

  BBNodeManagerAIG nm;
  BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&nm, simp, mgr->defaultNodeFactory, &mgr->UserFlags);
  ASTNode input = n;
  ASTNodeMap fromTo;
  ASTNodeMap equivs;
  bb.getConsts(input, fromTo,equivs);

  if (equivs.size() > 0)
    {
      ASTNodeMap cache;
      input = SubstitutionMap::replace(input, equivs, cache,nf,false,true);
    }

  if (fromTo.size() > 0)
    {
      ASTNodeMap cache;
      input = SubstitutionMap:: replace(input, fromTo, cache,nf);
    }

  return input;
}

int
getDifficulty(const ASTNode& n_)
{
  assert(n_.GetType() == BITVECTOR_TYPE);

  if (difficulty_cache.find(n_) != difficulty_cache.end())
    return difficulty_cache.find(n_)->second;

  // Calculate the difficulty over the widened version.
  ASTNode n = widen(n_,widen_to);
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

  Cnf_ClearMemory();
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


void
getAllFunctions(ASTNode v, ASTNode w, ASTVec& result)
{

  Kind types[] =
    { BVMULT , BVDIV, SBVDIV, SBVREM, SBVMOD, BVPLUS, BVMOD, BVRIGHTSHIFT, BVLEFTSHIFT, BVOR, BVAND, BVXOR, BVSRSHIFT };
  int number_types = sizeof(types) / sizeof(Kind);

  // all two argument functions.
  for (int i = 0; i < number_types; i++)
    result.push_back(create(types[i], v, w));
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

  nf = new SimplifyingNodeFactory(*(mgr->hashingNodeFactory), *mgr);
  mgr->defaultNodeFactory =nf;

  mgr->UserFlags.stats_flag = false;
  mgr->UserFlags.optimize_flag = true;

  ss = new MinisatCore<Minisat::Solver>(finished);

  // Prime the cache with 100..
  for (int i = 0; i < 100; i++)
    {
      saved_array.push_back(ASTVec());
    }

  zero = mgr->CreateZeroConst(bits);
  one = mgr->CreateOneConst(bits);
  maxNode = mgr->CreateMaxConst(bits);

  v = mgr->CreateSymbol("v", 0, bits);
  w = mgr->CreateSymbol("w", 0, bits);

  srand(time(NULL));
}

void
clearSAT()
{
  delete ss;
  ss = new MinisatCore<Minisat::Solver>(finished);
}

// Return true if the negation of the query is unsatisfiable.
bool
isConstantToSat(const ASTNode & query)
{
  assert(query.GetType() == BOOLEAN_TYPE);
  cerr << "to";

  GlobalSTP->ClearAllTables();
  clearSAT();

  ASTNode query2 = nf->CreateNode(NOT, query);

  SOLVER_RETURN_TYPE r = GlobalSTP->Ctr_Example->CallSAT_ResultCheck(*ss, query2, query2, GlobalSTP->tosat, false);

  cerr << "from";
  return (r == SOLVER_VALID); // unsat, always true
}


// Replaces the symbols in n, by each of the values, and concatenates them
// to turn it into a single 64-bit value.
uint64_t
getHash(const ASTNode& n_, const vector<Assignment>& values)
{
  assert(values.size() > 0);
  const int ass_bitwidth =values[0].getV().GetValueWidth();
  assert (ass_bitwidth >= bits);

  ASTNode n = n_;

  // The values might be at a higher bit-width.
  if (ass_bitwidth > bits)
    n = widen(n_,ass_bitwidth);

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
          if (strncmp(symbols[j].GetName(), "v", 1) ==0)
            {
              mapToVal.insert(make_pair(symbols[j], values[i].getV()));
              assert(symbols[j].GetValueWidth() == values[i].getV().GetValueWidth() );
            }
          else if (strncmp(symbols[j].GetName(), "w", 1) ==0)
            {
              mapToVal.insert(make_pair(symbols[j], values[i].getW()));
              assert(symbols[j].GetValueWidth() == values[i].getW().GetValueWidth() );
            }
          else
            {
              cerr << "Unknown symbol!" << symbols[j];
              FatalError("f");
            }
          assert(symbols[j].GetValueWidth() == ass_bitwidth );
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

  for (int i = 0; i < to.Degree(); i++)
    if (contained_in(from, to[i]))
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
  return (((unsigned) n1.GetNodeNum()) < ((unsigned) n2.GetNodeNum()));
}



// Breaks the expressions into buckets recursively, then pairwise checks that they are equivalent.
void
findRewrites(ASTVec& expressions, const vector<Assignment>& values, const int depth = 0)
{
  if (expressions.size() < 2)
    return;

  cout << '\n' <<  "depth:" << depth << ", size:" << expressions.size()  << " values:" << values.size() << " found: " << toWrite.size() << '\n';

  assert(expressions.size() >0);

  if (values.size() > 0)
    {
      // Put the functions in buckets based on their results on the values.
      HASHMAP<uint64_t, ASTVec> map;
      for (int i = 0; i < expressions.size(); i++)
        {
          if (expressions[i] == mgr->ASTUndefined)
            continue; // omit undefined.

          if (i % 50000 == 49999)
            cerr << ".";
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
          vector<Assignment> a;
          findRewrites(equiv, a, depth + 1);
          equiv.clear();
        }
      return;
    }
  ASTVec& equiv = expressions;

  // Sort so that constants, and smaller expressions will be checked first.
  sort(equiv.begin(), equiv.end(), lessThan);

  for (int i = 0; i < equiv.size(); i++)
    {
      if (equiv[i].GetKind() == UNDEFINED)
        continue;

      for (int j = i + 1; j < equiv.size(); j++) /// commutative so skip some.
        {
          if (equiv[i].GetKind() == UNDEFINED || equiv[j].GetKind() == UNDEFINED)
            continue;

          ASTNode n = nf->CreateNode(EQ, equiv[i], equiv[j]);
          if (n.GetKind() != EQ)
            continue;

          n = rewriteThroughWithAIGS(n);

          if (n.GetKind() != EQ)
            continue;

          ASTNode from, to;
          if (getDifficulty(n[0]) < getDifficulty(n[1]))
            {
              to = n[0];
              from = n[1];
            }
          else if (getDifficulty(n[0]) > getDifficulty(n[1]))
            {
              from = n[0];
              to = n[1];
            }
          else
            {
              // Difficulty is equal. Try it both ways and see if it's a candidate.
              if (is_candidate(n[0], n[1]))
                {
                  from = n[0];
                  to = n[1];
                }
              else
                {
                  from = n[1];
                  to = n[0];
                }
            }

          Assignment different;
          if (checkAndStoreRule(from,to, different))
            {
              // Remove the more difficult expression.
              if (from == equiv[i])
                equiv[i] = mgr->ASTUndefined;
              if (from == equiv[j])
                equiv[j] = mgr->ASTUndefined;
            }
          else if (!different.isEmpty())
            {
              vector<Assignment> ass;
              ass.push_back(different);

              // Discard the ones we've checked entirely.
              ASTVec newEquiv(equiv.begin() + std::max(i - 1, 0), equiv.end());
              equiv.clear();

              findRewrites(newEquiv, ass, depth + 1);
              return;
            }

          // Write out the rules intermitently.
          if (lastOutput + 500 < toWrite.size())
            {
              writeOutRules();
              lastOutput = toWrite.size();
            }

        }
    }
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

  if (n.isConstant() && (n.GetValueWidth() == bits || n.GetValueWidth() == bits-1))
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
checkAndStoreRule(const ASTNode & from, const ASTNode & to, Assignment& assignment)
{
  const ASTNode  n = create(EQ,from,to);

  assert(n.GetKind() == BEEV::EQ);
  assert(widen_to > bits);

  const int st = getCurrentTime();

  for (int i = bits; i < widen_to; i++)
    {
      const ASTNode& widened = widen(n, i);

      // Can't widen (usually because of CONCAT or a BVCONST).
      if (widened == mgr->ASTUndefined)
        {
          cerr << "can't widen";
          cerr << n;
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
          cerr << "*" << i - bits << "*";
          return false;
        }
    }

  toWrite.push_back(ToWrite(from,to,getCurrentTime() - st));
  return true;
}

template<class T>
  void
  removeDuplicates(T & big)
  {
    cerr << "Before removing duplicates:" << big.size();
    std::sort(big.begin(), big.end());
    typename T::iterator it = std::unique(big.begin(), big.end());
    big.resize(it - big.begin());
    cerr << ".After removing duplicates:" << big.size() << endl;
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
  assert(n.GetValueWidth() ==32); // Widen a constant used in an extract only.

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

  string result ="";

  if (n.GetKind() == BVCONST)
    {
      if (n.isConstant() && n.GetValueWidth() == 1 && n == mgr->CreateZeroConst(1))
        {
          result  = "bm->CreateZeroConst(1";

        }
      if (n.isConstant() && n.GetValueWidth() == 1 && n == mgr->CreateOneConst(1))
        {
          result  = "bm->CreateOneConst(1";
        }

      if (n.isConstant() && (n.GetValueWidth() == bits || n.GetValueWidth() == bits-1))
        {
          stringstream constant;
          constant << "bm->CreateBVConst(" << bits << "," << n.GetUnsignedConst() << ")";
          result += "bm->CreateTerm(BVSX,width," + constant.str() + "";
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
              result =  "  bm->CreateBVConst(32, width-2 ";
        }

      if (result =="")
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
      ss << "bm->CreateBVConst(32," << name(n[1]) << "),";  // top then bottom.
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
std::string to_string(T i)
{
    std::stringstream ss;
    ss << i;
    return ss.str();
}



// Write out all the rules that have been discovered to file.
void
writeOutRules()
{
  removeDuplicates(toWrite);

  vector<string> output;

  for (int i = 0; i < toWrite.size(); i++)
    {
      if (toWrite[i].isEmpty())
        continue;

      ASTNode to = toWrite[i].to;
      ASTNode from = toWrite[i].from;

      if (getDifficulty(to) > getDifficulty(from))
        {
          // Want the easier one on the lhs. Which is the opposite of what you expect..
          ASTNode t = to;
          to = from;
          from = t;
        }

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
          visit_all(from, val, "children");

          to_name = createString(to, val);
        }

      ASTNodeString names;
      string current = "n";
      string sofar = "if ( width >= " + to_string(bits) + " " ;

      rule_to_string(from, names, current, sofar);
      sofar += ")    set(result,  " + to_name + ");";

//      if (sofar.find("!!!") == std::string::npos && sofar.length() < 500)
        {
          assert(getDifficulty(from) >= getDifficulty(to));

          if (mgr->ASTTrue == rewriteThroughWithAIGS(toWrite[i].n))
              {
              toWrite[i] = ToWrite(mgr->ASTUndefined,mgr->ASTUndefined,0);
              continue;
              }

            {
              char buf[100];
              sprintf(buf, "//%d -> %d | %d ms\n", getDifficulty(from), getDifficulty(to), 0 /*toWrite[i].time*/);
              sofar += buf;
              output.push_back(sofar);
            }
        }
    }

  // Remove the duplicates from output.
  removeDuplicates(output);

  cerr << "Rules Discovered in total: " << toWrite.size() << endl;

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

  ofstream outputFileSMT2;
  outputFileSMT2.open("rewrite_data.smt2", ios::trunc);

      for (int i = 0; i < toWrite.size(); i++)
        {
          if (toWrite[i].isEmpty())
            continue;

          outputFileSMT2 << ";  " << "bits:" << bits << "->" << widen_to << " time to verify:" << toWrite[i].time << '\n';
          for (int j= widen_to; j < widen_to+ 5;j++)
            {
              outputFileSMT2 << "(push 1)\n";
              printer::SMTLIB2_PrintBack(outputFileSMT2, mgr->CreateNode(NOT, widen(toWrite[i].n,j)),true,false);
              outputFileSMT2 << "(pop 1)\n";
            }
        }

      outputFileSMT2.close();

      outputFileSMT2.open("array.smt2", ios::trunc);
      ASTVec v;
      for (int i = 0; i < toWrite.size(); i++)
              {
                if (toWrite[i].isEmpty())
                  continue;

                v.push_back(toWrite[i].n);
              }

      if (v.size() > 0)
      {
          ASTNode n = mgr->CreateNode(AND,v);
          printer::SMTLIB2_PrintBack(outputFileSMT2, n,true);
      }
      outputFileSMT2.close();

}

// Triples the number of functions by adding all the unary ones.
void
allUnary(ASTVec& functions)
{
  for (int i = 0, size = functions.size(); i < size; i++)
    {
      if (functions[i] == mgr->ASTUndefined)
        continue;

      functions.push_back(nf->CreateTerm(BEEV::BVNEG, bits, functions[i]));
      functions.push_back(nf->CreateTerm(BEEV::BVUMINUS, bits, functions[i]));
    }
}

void
removeNonWidened(ASTVec & functions)
{
  for (int i = 0; i < functions.size(); i++)
    {
      if (mgr->ASTUndefined == functions[i])
        continue;

      if (mgr->ASTUndefined == widen(functions[i], bits + 1))
        {
          functions[i] = mgr->ASTUndefined; // We can't widen it later. So remove it.
          continue;
        }
    }
}

// If there only w variables in the problem. We can delete it because
// we will have another with just v's.
// NB: Can only apply at the top level.
void
removeSingleVariable(ASTVec & functions)
{
  for (int i = 0; i < functions.size(); i++)
    {
      vector<ASTNode> symbols;
      ASTNodeSet visited;

      getVariables(functions[i], symbols, visited);
      if (symbols.size() == 1 && symbols[0] == w)
        {
          functions[i] = mgr->ASTUndefined; // We can't widen it later. So remove it.
          continue;
        }
    }
}

void
removeSingleUndefined(ASTVec& functions)
{
  for (int i = 0; i < functions.size(); i++)
    {
      if (functions[i] == mgr->ASTUndefined)
        {
          functions.erase(functions.begin() + i);
          break;
        }
    }
}

void applyBigRewrite(ASTVec& functions)
{
  BEEV::BigRewriter b;

  for (int i = 0; i < functions.size(); i++)
    {
      if (functions[i] == mgr->ASTUndefined)
        continue;

      ASTNodeMap fromTo;
      ASTNode s = b.rewrite(functions[i], fromTo, nf, mgr);
      if (s != functions[i])
        {
          functions[i] = s;
        }
    }
}


int
main(void)
{
  startup();

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

  /////////////////////////// BV, BV -> BV.
  ASTVec functions;

  functions.push_back(w);
  functions.push_back(v);
  functions.push_back(mgr->CreateBVConst(bits, 0));
  functions.push_back(mgr->CreateBVConst(bits, 1));
  functions.push_back(mgr->CreateMaxConst(bits));

  // All unary of the leaves.
  allUnary(functions);
  removeDuplicates(functions);
  cerr << "Leaves:" << functions.size() << endl;

  // We've got the leaves, and their unary operations,
  // now get the binary operations of all of those.
  int size = functions.size();
  for (int i = 0; i < size; i++)
    for (int j = 0; j < size; j++)
      getAllFunctions(functions[i], functions[j], functions);

  allUnary(functions);

  // Duplicates removed, rewrite rules applied, non-widenable removed,
  //removeNonWidened(functions);
  //applyBigRewrite(functions);
  removeDuplicates(functions);
  removeSingleUndefined(functions);

  cerr << "One Level:" << functions.size() << endl;
  applyBigRewrite(functions);
  removeDuplicates(functions);
  cerr << "After rewrite:" << functions.size() << endl;

  const bool two_level = true;

  if (two_level)
    {
      int last = 0;
      ASTVec functions_copy(functions);
      size = functions_copy.size();
      for (int i = 0; i < size; i++)
        for (int j = 0; j < size; j++)
          getAllFunctions(functions_copy[i], functions_copy[j], functions);

      //applyBigRewrite(functions);
      removeSingleVariable(functions);
      removeDuplicates(functions);
      removeSingleUndefined(functions);

      // All the unary combinations of the binaries.
      //allUnary(functions);
      //removeNonWidened(functions);
      //removeDuplicates(functions);
      cerr << "Two Level:" << functions.size() << endl;
    }

  // The hash is generated on these values.
  vector<Assignment> values;
  findRewrites(functions, values);
  writeOutRules();

  cerr << "Initial:" << bits << " widening to :" << widen_to << endl;
  cerr << "Highest disproved @ level: " << highestLevel << endl;
  cerr << highestDisproved << endl;

  return 0;
}


#if 0
// Shortcut. Don't examine the rule if it isn't a candidate.
bool
isCandidateSizePreserving(const ASTNode& n)
{
  if (n.GetKind() != EQ)
    return false;

  if (n[0].isConstant())
    return true;

  visited.clear();
  if (lhsInRHS(n[1], n[0]))
    return true;

  return false;
}

ASTNodeSet visited;

bool
lhsInRHS(const ASTNode& n, const ASTNode& lookFor)
{
  if (lookFor == n)
    return true;

  if (visited.find(n) != visited.end())
    return false;

  for (int i = 0; i < n.Degree(); i++)
    if (lhsInRHS(n[i], lookFor))
      return true;

  visited.insert(n);
  return false;
}

int
getDifficulty_approximate(const ASTNode&n)
{
  if (difficulty_cache.find(n) != difficulty_cache.end())
    return difficulty_cache.find(n)->second;

  DifficultyScore ds;
  int score = ds.score(n);
  difficulty_cache.insert(make_pair(n, score));
  return score;
}

// Shortcut. Don't examine the rule if it isn't a candidate.
bool
isCandidateDifficultyPreserving(const ASTNode& n)
{
  if (n.GetKind() != EQ)
    return false;

  if (getDifficulty(n[0]) != getDifficulty(n[1]))
    return true;

  return false;
}

void
getSomeFunctions(ASTNode v, ASTNode w, ASTVec& result)
{

  Kind types[] =
    { BVMULT, BVDIV, SBVDIV, SBVREM, SBVMOD, BVPLUS, BVMOD };
  int number_types = sizeof(types) / sizeof(Kind);

  // all two argument functions.
  for (int i = 0; i < number_types; i++)
    result.push_back(create(types[i], v, w));
}

// True if "to" is a single function of "n"
bool
single_fn_of(ASTNode from, ASTNode to)
{
  for (int i = 0; i < to.Degree(); i++)
    {
      if (to[i].isConstant())
        continue;

      // Special case equalities are cheap so allow them through.
      if (to[i].GetKind() == EQ && to[i][0].isConstant())
        {
          if (!contained_in(to[i][1], from))
            return false;
        }
      else if (!contained_in(to[i], from))
        return false;
    }
  return true;
}


#endif
