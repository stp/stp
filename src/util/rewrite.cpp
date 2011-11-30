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
#include "../simplifier/BigRewriter.h"

using namespace std;
using namespace BEEV;

extern int
smtparse(void*);
extern FILE *smtin;

//////////////////////////////////
const int bits = 8;
const int widen_to = 13;
const int values_in_hash = 64 / bits;
const int mask = (1 << (bits)) - 1;
const int unique_vars = 1 << bits;
//////////////////////////////////

// Saves a little bit of time. The vectors are saved between invocations.
vector<ASTVec> saved_array;

bool
isConstantToSat(const ASTNode & query);

string
containsNode(const ASTNode& n, const ASTNode& hunting, string& current);

void
writeOutRules();

bool
checkAndStoreRule(const ASTNode & n);

typedef HASHMAP<ASTNode, string, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> ASTNodeString;

BEEV::STPMgr* mgr;
NodeFactory* nf;
SATSolver * ss;
ASTNodeSet stored; // Store nodes so they aren't garbage collected.

ASTNode zero, one, maxNode, v, w;

ASTVec toWrite; // Rules to write out when we get the chance.

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

  Assignment()
  {
  }

  // Generate w from v a bit randomly.
  explicit
  Assignment(const ASTNode & n)
  {
    setV(n);
    srand(v.GetUnsignedConst());
    w = BEEV::ParserBM->CreateBVConst(bits, rand());
  }

  Assignment(ASTNode & n0, ASTNode & n1)
  {
    setV(n0);
    setV(n1);
  }
};

// Helper functions. Don't need to specify the width.
ASTNode
create(Kind k, const ASTNode& n0, const ASTNode& n1)
{
  if (is_Term_kind(k))
    return nf->CreateTerm(k, bits, n0, n1);
  else
    return nf->CreateNode(k, n0, n1);
}

ASTNode
create(Kind k, ASTVec& c)
{
  if (is_Term_kind(k))
    return nf->CreateTerm(k, bits, c);
  else
    return nf->CreateNode(k, c);
}

// Gets the name of the lhs in terms of the rhs.
// If it's a constant it's the name of the constant,
// otherwise it's the position of the lhs in the rhs. Otherwise empty.
string
getLHSName(const ASTNode& lhs, const ASTNode& rhs)
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
  if (n.isConstant())
    return n;

  if (map.find(n) != map.end())
    return (*map.find(n)).second;

  // We have an array of arrays already created to store the children.
  // This reduces the number of objects created/destroyed.
  if (count >= saved_array.size())
    saved_array.push_back(ASTVec());

  ASTVec& new_children = saved_array[count];
  new_children.clear();

  for (int i = 0; i < n.Degree(); i++)
    new_children.push_back(eval(n[i], map, count + 1));

  ASTNode r = NonMemberBVConstEvaluator(mgr, n.GetKind(), new_children, bits);
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
      different.setV(GlobalSTP->Ctr_Example->GetCounterExample(true, v));
      different.setW(GlobalSTP->Ctr_Example->GetCounterExample(true, w));
      return false;
    }
}

// Intended to widen the problem from "bits" to "width".
ASTNode
widen(const ASTNode& w, int width)
{
  if (w.isConstant() && w.GetValueWidth() == bits && (w == one))
    return (BEEV::ParserBM->CreateOneConst(width));

  if (w.isConstant() && w.GetValueWidth() == bits && (w == zero))
    return (BEEV::ParserBM->CreateZeroConst(width));

  if (w.isConstant() && w.GetValueWidth() == bits && (w == maxNode))
    return (BEEV::ParserBM->CreateMaxConst(width));

  if (w.isConstant() /*&& w.GetValueWidth() == 1*/)
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

  ASTNode result;
  if (w.GetType() == BOOLEAN_TYPE)
    result = nf->CreateNode(w.GetKind(), ch);
  else if (w.GetKind() == BVEXTRACT && w.GetValueWidth() == 1)
    {
      result = nf->CreateTerm(BVEXTRACT, 1, ch[0], BEEV::ParserBM->CreateBVConst(32, width - 1),
          BEEV::ParserBM->CreateBVConst(32, width - 1));
    }
  else if (w.GetKind() == BVCONCAT)
    {
      cerr << "don't do thisyerT" << w;
      return mgr->ASTUndefined;
    }
  else
    result = nf->CreateTerm(w.GetKind(), width, ch);

  BVTypeCheck(result);
  return result;
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

// Shortcut. Don't examine the rule if it isn't a candidate.
bool
isCandidate(const ASTNode& n)
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
    { BVMULT, BVDIV, SBVDIV, SBVREM, SBVMOD, BVPLUS, BVMOD, BVRIGHTSHIFT, BVLEFTSHIFT, BVOR, BVAND, BVXOR, BVSRSHIFT };
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

  Simplifier * simplifier = new Simplifier(mgr);
  ArrayTransformer * at = new ArrayTransformer(mgr, simplifier);
  AbsRefine_CounterExample* abs = new AbsRefine_CounterExample(mgr, simplifier, at);
  ToSAT* tosat = new ToSAT(mgr);

  GlobalSTP = new STP(mgr, simplifier, at, tosat, abs);

  nf = new SimplifyingNodeFactory(*(mgr->hashingNodeFactory), *mgr);

  mgr->UserFlags.stats_flag = false;
  mgr->UserFlags.optimize_flag = true;

  ss = new MinisatCore<Minisat::Solver>();

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
  ss = new MinisatCore<Minisat::Solver>();
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

  query2 = GlobalSTP->arrayTransformer->TransformFormula_TopLevel(query2);
  SOLVER_RETURN_TYPE r = GlobalSTP->Ctr_Example->CallSAT_ResultCheck(*ss, query2, query2, GlobalSTP->tosat, false);

  cerr << "from";
  return (r == SOLVER_VALID); // unsat, always true
}

// Replaces the symbols in n, by each of the values, and concatenates them
// to turn it into a single 64-bit value.
uint64_t
getHash(const ASTNode& n, const vector<Assignment>& values)
{
  vector<ASTNode> symbols; // The variables in the n node.
  ASTNodeSet visited;
  getVariables(n, symbols, visited);

  uint64_t hash = 0;

  for (int i = 0; i < values.size(); i++)
    {
      ASTNodeMap mapToVal;
      for (int j = 0; j < symbols.size(); j++)
        {
          if (symbols[j] == v)
            mapToVal.insert(make_pair(v, values[i].getV()));
          else if (symbols[j] == w)
            mapToVal.insert(make_pair(w, values[i].getW()));
          else
            cerr << "Unknown symbol!" << symbols[j];
        }
      ASTNode r = eval(n, mapToVal);
      assert(r.isConstant());
      hash <<= bits;
      hash += r.GetUnsignedConst();
    }
  return hash;
}

bool
lessThan(const ASTNode& n1, const ASTNode& n2)
{
  return (((unsigned) n1.GetNodeNum()) < ((unsigned) n2.GetNodeNum()));
}

// Breaks the expressions into buckets recursively, then pairwise checks that they are equivalent.
void
findRewrites(const ASTVec& expressions, const vector<Assignment>& values, const int depth = 0)
{
  assert(expressions.size() >0);

  // Put the functions in buckets based on their results on the values.
  HASHMAP<uint64_t, ASTVec> map;
  for (int i = 0; i < expressions.size(); i++)
    {
      if (i % 50000 == 49999)
        cerr << ".";
      uint64_t hash = getHash(expressions[i], values);
      if (map.find(hash) == map.end())
        map.insert(make_pair(hash, ASTVec()));
      map[hash].push_back(expressions[i]);
    }

  HASHMAP<uint64_t, ASTVec>::iterator it2;
  static int lastOutput = 0;
  int id = 1;
  for (it2 = map.begin(); it2 != map.end(); it2++)
    {
      ASTVec& equiv = it2->second;

      // fast shortcut.
      if (equiv.size() == 1)
        continue;

      cerr << "[" << id++ << " of " << map.size() << "] depth:" << depth << ", size:" << equiv.size() << endl;

      // We don't want to keep splitting if it's having no effect.
      // In particular we bound the maximum depth, and don't split again,
      // if the last time we tried it didn't split at all..
      if (equiv.size() > 50 && depth <= 50 && (map.size() != 1))
        {
          vector<Assignment> newValues;

          int max_iterations = std::max(values_in_hash * 2, (int) equiv.size() / 1000);

          for (int j = 0; (j < max_iterations) && (newValues.size() < values_in_hash); j++)
            {
              ASTNode lhs = equiv[rand() % equiv.size()];
              ASTNode rhs = equiv[rand() % equiv.size()];
              ASTNode n = mgr->CreateNode(EQ, lhs, rhs);

              Assignment different;
              bool con = isConstant(n, different);

              if (con)
                continue; // always same.

              // nb: We may find the same values multiple times, but don't currently care..
              newValues.push_back(different);
            }
          cerr << "Found:" << newValues.size() << endl;

          if (newValues.size() > 0)
            {
              findRewrites(equiv, newValues, depth + 1);
              continue;
            }
        }

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

              const ASTNode n = nf->CreateNode(EQ, equiv[i], equiv[j]);
              if (isCandidate(n) && checkAndStoreRule(n))
                {
                  // We remove the LHS from the list. Other equivalent expressions will match
                  // the RHS anyway.
                  if (n[1] == equiv[i])
                    equiv[i] = mgr->ASTUndefined;
                  if (n[1] == equiv[j])
                    equiv[j] = mgr->ASTUndefined;
                }

              // Write out the rules intermitently.
              if (lastOutput + 500 < toWrite.size())
                {
                  lastOutput = toWrite.size();
                  writeOutRules();
                }

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

  if (n.isConstant() && n.GetValueWidth() == 32 && n == mgr->CreateZeroConst(1)) // extract probably.
    {
      sofar += "&& " + current + " == bm->CreateZeroConst(32) ";
      return;
    }

  if (n.isConstant() && n.GetValueWidth() == 32 && n == mgr->CreateBVConst(32, bits - 1)) // extract probably.
    {
      sofar += "&& " + current + " == mgr->CreateBVConst(32, width-1) ";
      return;
    }

  if (n.isConstant() && n == mgr->CreateMaxConst(n.GetValueWidth()))
    {
      sofar += "&& " + current + " == max ";
      return;
    }

  if (n.isConstant() && n == mgr->CreateOneConst(n.GetValueWidth()))
    {
      sofar += "&& " + current + " == one ";
      return;
    }

  if (n.isConstant() && n == mgr->CreateZeroConst(n.GetValueWidth()))
    {
      sofar += "&& " + current + " == zero";
      return;
    }

  if (n.isConstant() && n == mgr->CreateBVConst(n.GetValueWidth(), n.GetValueWidth()))
    {
      sofar += "&& " + current + " == zero ";
      return;
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
checkAndStoreRule(const ASTNode & n)
{
  assert(n.GetKind() == BEEV::EQ);

  assert(widen_to > bits);

  for (int i = bits; i < widen_to; i++)
    {
      const ASTNode& widened = widen(n, i);

      // Can't widen (usually because of CONCAT or a BVCONST).
      if (widened == mgr->ASTUndefined)
        {
          cerr << ")";
          return false;
        }

      // Send it to the SAT solver to verify that the widening has the same answer.
      bool result = isConstantToSat(widened);

      if (!result)
        {
          // Detected it's not a constant, or is constant FALSE.
          cerr << "*" << i - bits << "*";
          return false;
        }
    }

  toWrite.push_back(n);
  return true;
}

template<class T>
  void
  removeDuplicates(T & big)
  {
    cerr << "Before removing duplicates:" << big.size();
    std::sort(big.begin(), big.end());
    ASTVec::iterator it = std::unique(big.begin(), big.end());
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
          current = current.replace(from, to - from + 2, "/*" + val + " && */"); // Remove what we've searched for.
          buckets[val].push_back(current);
        }
    }
}

// Write out all the rules that have been discovered to file.
void
writeOutRules()
{
  vector<string> output;

  removeDuplicates(toWrite);
  cerr << "Writing out " << toWrite.size() << " rules." << endl;

  ofstream outputFile;
  outputFile.open("rewrite_data.cpp", ios::trunc);


  for (int i = 0; i < toWrite.size(); i++)
    {
      const ASTNode& n = toWrite[i];
      const ASTNode& lhs = n[0];
      const ASTNode& rhs = n[1];

      string name = getLHSName(n[0], n[1]);
      if (name == "")
        {
          cerr << "Attempting to write out non name!" << n;
          continue;
        }
      ASTNodeString names;
      string current = "n";
      string sofar = "if (1==1 ";
      rule_to_string(n[1], names, current, sofar);
      sofar += " && 1==1)    set(output," + name + ", __LINE__ );\n";

      if (sofar.find("!!!") == std::string::npos && sofar.length() < 500)
        {
          output.push_back(sofar);
          //printer::SMTLIB2_PrintBack(outputFile,toWrite[i]);
        }
    }

  // Group functions of the same kind all together.
  hash_map<string, vector<string>, hashF<std::string> > buckets;
  bucket("n.GetKind() ==", output, buckets);

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
}

// Triples the number of functions by adding all the unary ones.
void
allUnary(ASTVec& functions)
{
  for (int i = 0, size = functions.size(); i < size; i++)
    {
      functions.push_back(nf->CreateTerm(BEEV::BVNEG, bits, functions[i]));
      functions.push_back(nf->CreateTerm(BEEV::BVUMINUS, bits, functions[i]));
    }

}

// If we can't widen it remove it. Very slow.
void
removeNonWidened(ASTVec & functions)
{
  for (int i = 0; i < functions.size(); i++)
    {
      if (mgr->ASTUndefined == widen(functions[i], bits + 1))
        {
          functions.erase(functions.begin() +i);
          i--;
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

  removeDuplicates(functions);
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
  removeDuplicates(functions);
  removeNonWidened(functions);
  cerr << "One Level:" << functions.size() << endl;

  const bool two_level = true;
  if (two_level)
    {
      int last = 0;
      ASTVec functions_copy(functions);
      size = functions_copy.size();
      for (int i = 0; i < size; i++)
        for (int j = 0; j < size; j++)
          {
            getAllFunctions(functions_copy[i], functions_copy[j], functions);
            if (functions.size() > last + 5000000) // lots are duplicates.
              {
                removeSingleVariable(functions);
                last = functions.size();
              }
          }

      // All the unary combinations of the binaries.
      allUnary(functions);

      // This is an agressive filter.
      removeSingleVariable(functions);
      cerr << "Two Level:" << functions.size() << endl;
    }

  BBNodeManagerAIG bbnm;
  SimplifyingNodeFactory nf(*(mgr->hashingNodeFactory), *mgr);

  BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&bbnm, GlobalSTP->simp, &nf, &(mgr->UserFlags));

    {
      SimplifyingNodeFactory nf(*(mgr->hashingNodeFactory), *mgr);
      BEEV::BigRewriter b;

      for (int i = 0; i < functions.size(); i++)
        {
          if (false)
            {
              ASTNodeMap fromTo;
              ASTNode s = b.rewrite(functions[i], fromTo, &nf, mgr);
              if (s != functions[i])
                functions[i] = s;
            }

        }
      removeDuplicates(functions);

      // There may be a single undefined element now.. remove it.
      for (int i = 0; i < functions.size(); i++)
        {
          if (functions[i] == mgr->ASTUndefined)
            {
              functions.erase(functions.begin() + i);
              break;
            }
        }
    }

  // The hash is generated on these values.
  vector<Assignment> values;
  values.push_back(Assignment(BEEV::ParserBM->CreateMaxConst(bits)));
  values.push_back(Assignment(BEEV::ParserBM->CreateZeroConst(bits)));
  while (values.size() < values_in_hash)
    values.push_back(Assignment(BEEV::ParserBM->CreateBVConst(bits, rand())));

  findRewrites(functions, values);
  writeOutRules();

  return 1;
}

