/********************************************************************
 * AUTHORS: Vijay Ganesh, Andrew Teylu
 *
 * BEGIN DATE: November, 2005
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
#include "stp/c_interface.h"

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include "stp/Interface/fdstream.h"
#include "stp/Parser/parser.h"
#include "stp/Printer/printers.h"
#include "stp/cpp_interface.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/Util/GitSHA1.h"

// From ABC
#include "sat/cnf/cnf.h"

#include "stp/ToSat/ToSATAIG.h"


using std::cout;
using std::ostream;
using std::stringstream;
using std::string;
using std::fdostream;
using std::endl;

// Defined further down, but used by the boolean expression builders above it.
Expr createBinaryNode(VC vc, Kind k, Expr left, Expr right);

namespace /* anonymous namespace for static */
{

// The packed bit width laid under a scalar type node: the declared width of
// a BITVECTOR, the packed width of a FLOATINGPOINT, five for ROUNDINGMODE.
unsigned int scalarTypeNodeWidth(const stp::ASTNode& t)
{
  switch (t.GetKind())
  {
    case stp::BITVECTOR:
      return t[0].GetUnsignedConst();
    case stp::FLOATINGPOINT:
      return t[0].GetUnsignedConst() + t[1].GetUnsignedConst();
    case stp::ROUNDINGMODE:
      return 5;
    default:
      stp::FatalError("CInterface: expected a bitvector, floating-point or "
                      "RoundingMode type node: ",
                      t);
      return 0;
  }
}

/* this method is purposefully not public! */
std::pair<unsigned int, unsigned int> getTypeSizes(Type type)
{
  unsigned int indexWidth = 0;
  unsigned int valueWidth = 0;

  stp::ASTNode* a = (stp::ASTNode*)type;

  switch (a->GetKind())
  {
    case stp::BITVECTOR:
      indexWidth = 0;
      valueWidth = (*a)[0].GetUnsignedConst();
      break;
    case stp::ARRAY:
      // The children are the index and element type nodes themselves (see
      // vc_arrayType), each BITVECTOR, FLOATINGPOINT or ROUNDINGMODE.
      indexWidth = scalarTypeNodeWidth((*a)[0]);
      valueWidth = scalarTypeNodeWidth((*a)[1]);
      break;
    case stp::BOOLEAN:
      indexWidth = 0;
      valueWidth = 0;
      break;
    case stp::FLOATINGPOINT:
      // A floating-point type node carries its exponent and significand widths
      // as its two children (see vc_fpType). The packed value width is their
      // sum; exp/sig are stamped onto the symbol separately, in vc_varExpr.
      indexWidth = 0;
      valueWidth = (*a)[0].GetUnsignedConst() + (*a)[1].GetUnsignedConst();
      break;
    case stp::ROUNDINGMODE:
      // A rounding mode is carried as a 5-bit bitvector; vc_varExpr
      // additionally pins the symbol to the five legal encodings.
      indexWidth = 0;
      valueWidth = 5;
      break;
    default:
      stp::FatalError("CInterface: vc_varExpr: Unsupported type", *a);
      assert(false);
      exit(-1);
      break;
  }
  return std::make_pair(valueWidth, indexWidth);
}
} // namespace

// GLOBAL FUNCTION: parser
extern int cvcparse(void*);
extern int smtparse(void*);

/* wraps get_git_version_sha in stp namespace */
const char* get_git_version_sha(void)
{
  return stp::get_git_version_sha();
}

/* wraps get_git_version_tag in stp namespace */
const char* get_git_version_tag(void)
{
  return stp::get_git_version_tag();
}

/* wraps get_compilation_env in stp namespace */
const char* get_compilation_env(void)
{
  return stp::get_compilation_env();
}

// TODO remove this, it's really ugly
void vc_setFlags(VC vc, char c, int /*param_value*/)
{
  process_argument(c, vc);
}

// TODO remove this, it's really ugly
void vc_setFlag(VC vc, char c)
{
  process_argument(c, vc);
}

void vc_setInterfaceFlags(VC vc, enum ifaceflag_t f, int param_value)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  switch (f)
  {
    case EXPRDELETE:
      b->UserFlags.cinterface_exprdelete_on_flag = param_value != 0;
      break;
    case MS:
      b->UserFlags.solver_to_use = stp::UserDefinedFlags::MINISAT_SOLVER;
      break;
    case SMS:
      b->UserFlags.solver_to_use =
          stp::UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER;
      break;
    case CMS4:
      b->UserFlags.solver_to_use = stp::UserDefinedFlags::CRYPTOMINISAT5_SOLVER;
      break;
    case RISS:
      b->UserFlags.solver_to_use = stp::UserDefinedFlags::RISS_SOLVER;
      break;
    case MSP:
      //Array-based Minisat has been replaced with normal MiniSat
      b->UserFlags.solver_to_use = stp::UserDefinedFlags::MINISAT_SOLVER;
      break;
    case CADICAL:
      b->UserFlags.solver_to_use = stp::UserDefinedFlags::CADICAL_SOLVER;
      break;
    default:
      stp::FatalError("C_interface: vc_setInterfaceFlags: Unrecognized flag\n");
      break;
  }
}

// Division is now always total
void make_division_total(VC /*vc*/)
{
}

// Create a validity Checker.
VC vc_createValidityChecker(void)
{
  // Boot the bitvector library before allocating anything, so the failure
  // path leaks nothing.
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (0 != c)
  {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  return vc_createValidityCheckerReuse(new stp::STPMgr());
}

// Create a validity checker over an existing manager (an stp::STPMgr*), so a
// client mixing the C API with the C++ objects can solve over nodes it built
// directly.
VC vc_createValidityCheckerReuse(void* _bm)
{
  stp::STPMgr* bm = (stp::STPMgr*)_bm;

  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (0 != c)
  {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  // A fresh manager starts out with its plain hashing factory; upgrade it to
  // the simplifying one. A reused manager that was already given a factory
  // keeps it (this used to replace -- and leak -- whatever was installed).
  if (bm->defaultNodeFactory == bm->hashingNodeFactory)
    bm->defaultNodeFactory =
        new SimplifyingNodeFactory(*(bm->hashingNodeFactory), *bm);

  // The parser-facing helpers read GlobalParserBM; point it at this manager
  // so a C-API client that never parses still has it aimed at a live one.
  // (Floating-point blasting itself takes the manager explicitly and does
  // not consult this.)
  stp::GlobalParserBM = bm;

  stp::STP* stpObj =
      new stp::STP(bm);

  // created_exprs.clear();
  vc_setFlags(stpObj, 'd');
  return (VC)stpObj;
}

// Expr I/O
void vc_printExpr(VC vc, Expr e)
{
  // do not print in lisp mode
  stp::STP* stp_i = (stp::STP*)vc;
  stp::ASTNode q = (*(stp::ASTNode*)e);
  stp::STPMgr* b = stp_i->bm;
  q.PL_Print(cout, b);
}

char* vc_printSMTLIB(VC vc, Expr e)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stringstream ss;
  printer::SMTLIB1_PrintBack(ss, *((stp::ASTNode*)e), b);
  string s = ss.str();
  char* copy = strdup(s.c_str());
  return copy;
}

// prints Expr 'e' to stdout as C code
void vc_printExprCCode(VC vc, Expr e)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode q = (*(stp::ASTNode*)e);

  // print variable declarations
  stp::ASTVec declsFromParser = (stp::ASTVec)b->decls;

  for (stp::ASTVec::iterator it = declsFromParser.begin(),
                             itend = declsFromParser.end();
       it != itend; it++)
  {
    if (stp::BITVECTOR_TYPE == it->GetType())
    {
      const char* name = it->GetName();
      unsigned int bitWidth = it->GetValueWidth();
      assert(bitWidth % 8 == 0);
      unsigned int byteWidth = bitWidth / 8;
      cout << "unsigned char " << name << "[" << byteWidth << "];" << endl;
    }
    else
    {
      // vc_printExprCCode: unsupported decl. type
      assert(0);
    }
  }

  cout << endl;

  // print constraints and assert
  printer::C_Print(cout, q, b);
}

void vc_printExprFile(VC vc, Expr e, int fd)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  fdostream os(fd);

  ((stp::ASTNode*)e)->PL_Print(os, b);
  // os.flush();
}

static void vc_printVarDeclsToStream(VC vc, ostream& os)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  for (stp::ASTVec::iterator i = b->decls.begin(), iend = b->decls.end();
       i != iend; i++)
  {
    stp::ASTNode a = *i;
    switch (a.GetType())
    {
      case stp::BITVECTOR_TYPE:
        a.PL_Print(os, b);
        os << " : BITVECTOR(" << a.GetValueWidth() << ");" << endl;
        break;
      case stp::ARRAY_TYPE:
        a.PL_Print(os, b);
        os << " : ARRAY "
           << "BITVECTOR(" << a.GetIndexWidth() << ") OF ";
        os << "BITVECTOR(" << a.GetValueWidth() << ");" << endl;
        break;
      case stp::BOOLEAN_TYPE:
        a.PL_Print(os, b);
        os << " : BOOLEAN;" << endl;
        break;
      default:
        stp::FatalError("vc_printDeclsToStream: Unsupported type", a);
        break;
    }
  }
}

void vc_printVarDecls(VC vc)
{
  vc_printVarDeclsToStream(vc, cout);
}

void vc_clearDecls(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  b->decls.clear();
}

static void vc_printAssertsToStream(VC vc, ostream& os, int simplify_print)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTVec v = b->GetAsserts();

  stp::SubstitutionMap sm (b);
  stp::Simplifier simp(b, &sm );
  for (stp::ASTVec::iterator i = v.begin(), iend = v.end(); i != iend; i++)
  {
    stp::ASTNode q =
        (simplify_print == 1) ? simp.SimplifyFormula_TopLevel(*i, false) : *i;
    q = (simplify_print == 1) ? simp.SimplifyFormula_TopLevel(q, false) : q;
    os << "ASSERT( ";
    q.PL_Print(os, b);
    os << ");" << endl;
  }
}

void vc_printAsserts(VC vc, int simplify_print)
{
  vc_printAssertsToStream(vc, cout, simplify_print);
}

void vc_printQueryStateToBuffer(VC vc, Expr e, char** buf, unsigned long* len,
                                int simplify_print)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  assert(vc);
  assert(e);
  assert(buf);
  assert(len);

  stp::SubstitutionMap sm (b);
  stp::Simplifier simp(b, &sm );

  // formate the state of the query
  stringstream os;
  vc_printVarDeclsToStream(vc, os);
  os << "%----------------------------------------------------" << endl;
  vc_printAssertsToStream(vc, os, simplify_print);
  os << "%----------------------------------------------------" << endl;
  os << "QUERY( ";
  stp::ASTNode q =
      (simplify_print == 1)
          ? simp.SimplifyFormula_TopLevel(*((stp::ASTNode*)e), false)
          : *(stp::ASTNode*)e;
  q.PL_Print(os, b);
  os << " );" << endl;

  // convert to a c buffer
  string s = os.str();
  const char* cstr = s.c_str();
  unsigned long size = s.size() + 1; // number of chars + terminating null
  *buf = (char*)malloc(size);
  if (!(*buf))
  {
    fprintf(stderr, "malloc(%lu) failed.", size);
    assert(*buf);
  }
  *len = size;
  memcpy(*buf, cstr, size);
}

void vc_printCounterExampleToBuffer(VC vc, char** buf, unsigned long* len)
{
  assert(vc);
  assert(buf);
  assert(len);

  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  // formate the state of the query
  std::ostringstream os;
  bool currentPrint = b->UserFlags.print_counterexample_flag;
  b->UserFlags.print_counterexample_flag = true;
  os << "COUNTEREXAMPLE BEGIN: \n";
  ce->PrintCounterExample(true, os);
  os << "COUNTEREXAMPLE END: \n";
  b->UserFlags.print_counterexample_flag = currentPrint;

  // convert to a c buffer
  string s = os.str();
  const char* cstr = s.c_str();
  unsigned long size = s.size() + 1; // number of chars + terminating null
  *buf = (char*)malloc(size);
  if (!(*buf))
  {
    fprintf(stderr, "malloc(%lu) failed.", size);
    assert(*buf);
  }
  *len = size;
  memcpy(*buf, cstr, size);
}

void vc_printExprToBuffer(VC vc, Expr e, char** buf, unsigned long* len)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode q = *((stp::ASTNode*)e);

  stringstream os;
  q.PL_Print(os, b);
  string s = os.str();
  const char* cstr = s.c_str();
  unsigned long size = s.size() + 1; // number of chars + terminating null
  *buf = (char*)malloc(size);
  *len = size;
  memcpy(*buf, cstr, size);
}

void vc_printQuery(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  ostream& os = std::cout;
  os << "QUERY(";
  stp::ASTNode q = b->GetQuery();
  q.PL_Print(os, b);
  os << ");" << endl;
}

stp::ASTNode* persistNode(VC vc, stp::ASTNode n)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::ASTNode* np = new stp::ASTNode(n);
  if (b->UserFlags.cinterface_exprdelete_on_flag)
    b->persist.push_back(np);
  return np;
}

/////////////////////////////////////////////////////////////////////////////
// Array-related methods                                                   //
/////////////////////////////////////////////////////////////////////////////
//! Create an array type
Type vc_arrayType(VC vc, Type typeIndex, Type typeData)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* ti = (stp::ASTNode*)typeIndex;
  stp::ASTNode* td = (stp::ASTNode*)typeData;

  // Index and element may each be a bitvector, a floating-point format, or
  // RoundingMode. The type node keeps the child type nodes whole, so
  // vc_varExpr can lay the right widths and formats onto the symbol.
  const auto scalar = [](const stp::ASTNode& t) {
    return t.GetKind() == stp::BITVECTOR ||
           t.GetKind() == stp::FLOATINGPOINT ||
           t.GetKind() == stp::ROUNDINGMODE;
  };
  if (!scalar(*ti))
  {
    stp::FatalError("CInterface: vc_arrayType: the index type must be a "
                    "bitvector, floating-point or RoundingMode type: ",
                    *ti);
  }
  if (!scalar(*td))
  {
    stp::FatalError("CInterface: vc_arrayType: the element type must be a "
                    "bitvector, floating-point or RoundingMode type: ",
                    *td);
  }
  stp::ASTNode output = b->CreateNode(stp::ARRAY, *ti, *td);

  return persistNode(vc, output);
}

// A rounding-mode-sorted term, for the array boundary checks. The sort has
// no type index of its own -- the carrier is a plain 5-bit bitvector -- so
// recognise the shapes that denote a mode: the five one-hot constants, a
// declared RoundingMode symbol, a read from a RoundingMode-element array,
// and an ite over those.
static bool isRoundingModeSortedTerm(stp::STPMgr* b, const stp::ASTNode& n)
{
  if (n.GetValueWidth() != 5 || n.GetIndexWidth() != 0)
    return false;

  switch (n.GetKind())
  {
    case stp::BVCONST:
    {
      const unsigned v = n.GetUnsignedConst();
      return v == 1 || v == 2 || v == 4 || v == 8 || v == 16;
    }
    case stp::SYMBOL:
      return b->isRoundingModeSymbol(n);
    case stp::READ:
      return b->arrayHasRmElement(n[0]);
    case stp::ITE:
      return isRoundingModeSortedTerm(b, n[1]) &&
             isRoundingModeSortedTerm(b, n[2]);
    default:
      return false;
  }
}

// The index of an array access must have the array's declared index sort:
// a float of the right format for a float-indexed array, a rounding mode
// for a RoundingMode-indexed one, and a plain bitvector otherwise. Mixing
// sorts of one width is not merely ill-sorted -- a raw index alongside
// canonicalised ones would break the array's congruence (see FpTotalise).
static void checkArrayIndexSort(const char* who, stp::STPMgr* b,
                                const stp::ASTNode& arr,
                                const stp::ASTNode& index)
{
  unsigned int exp_width = 0;
  unsigned int sig_width = 0;
  if (b->arrayHasFpIndex(arr, exp_width, sig_width))
  {
    if (index.GetType() != stp::FLOATINGPOINT_TYPE ||
        index.GetExpWidth() != exp_width || index.GetSigWidth() != sig_width)
      stp::FatalError((std::string("CInterface: ") + who +
                       ": the array is indexed by a floating-point sort, but "
                       "the index is not a float of that format: ")
                          .c_str(),
                      index);
  }
  else if (b->arrayHasRmIndex(arr))
  {
    if (!isRoundingModeSortedTerm(b, index))
      stp::FatalError((std::string("CInterface: ") + who +
                       ": the array is indexed by RoundingMode, but the index "
                       "is not a rounding mode: ")
                          .c_str(),
                      index);
  }
  else if (index.GetType() == stp::FLOATINGPOINT_TYPE)
  {
    stp::FatalError((std::string("CInterface: ") + who +
                     ": a float index over a bitvector-indexed array: ")
                        .c_str(),
                    index);
  }
}

// The value stored by vc_writeExpr must have the array's element sort, by
// the same reasoning.
static void checkArrayValueSort(stp::STPMgr* b, const stp::ASTNode& arr,
                                const stp::ASTNode& value)
{
  if (arr.GetExpWidth() != 0)
  {
    if (value.GetType() != stp::FLOATINGPOINT_TYPE ||
        value.GetExpWidth() != arr.GetExpWidth() ||
        value.GetSigWidth() != arr.GetSigWidth())
      stp::FatalError("CInterface: vc_writeExpr: the array's elements are "
                      "floats, but the stored value is not a float of that "
                      "format: ",
                      value);
  }
  else if (b->arrayHasRmElement(arr))
  {
    if (!isRoundingModeSortedTerm(b, value))
      stp::FatalError("CInterface: vc_writeExpr: the array's elements are "
                      "rounding modes, but the stored value is not one: ",
                      value);
  }
  else if (value.GetType() == stp::FLOATINGPOINT_TYPE)
  {
    stp::FatalError("CInterface: vc_writeExpr: storing a float into a "
                    "bitvector-element array: ",
                    value);
  }
}

//! Create an expression for the value of array at the given index
Expr vc_readExpr(VC vc, Expr array, Expr index)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)array;
  stp::ASTNode* i = (stp::ASTNode*)index;

  assert(BVTypeCheck(*a));
  assert(BVTypeCheck(*i));
  checkArrayIndexSort("vc_readExpr", b, *a, *i);
  stp::ASTNode o = b->CreateTerm(stp::READ, a->GetValueWidth(), *a, *i);
  assert(BVTypeCheck(o));

  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

// //! Array update; equivalent to "array WITH [index] := newValue"
Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)array;
  stp::ASTNode* i = (stp::ASTNode*)index;
  stp::ASTNode* n = (stp::ASTNode*)newValue;

  assert(BVTypeCheck(*a));
  assert(BVTypeCheck(*i));
  assert(BVTypeCheck(*n));
  checkArrayIndexSort("vc_writeExpr", b, *a, *i);
  checkArrayValueSort(b, *a, *n);
  stp::ASTNode o = b->CreateTerm(stp::WRITE, a->GetValueWidth(), *a, *i, *n);
  o.SetIndexWidth(a->GetIndexWidth());
  assert(BVTypeCheck(o));

  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

/////////////////////////////////////////////////////////////////////////////
// Context-related methods                                                 //
/////////////////////////////////////////////////////////////////////////////
//! Assert a new formula in the current context.
/*! The formula must have Boolean type. */
void vc_assertFormula(VC vc, Expr e)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (!stp::is_Form_kind(a->GetKind()))
    stp::FatalError("Trying to assert a NON formula: ", *a);

  assert(BVTypeCheck(*a));
  b->AddAssert(*a);
}

//! Check validity of e in the current context. e must be a FORMULA
//
// if returned 0 then input is INVALID.
//
// if returned 1 then input is VALID
//
// if returned 2 then ERROR
//
//! Check validity of e in the current context.
/*! If the result is true, then the resulting context is the same as
 * the starting context.  If the result is false, then the resulting
 * context is a context in which e is false.  e must have Boolean
 * type. */
int vc_query(VC vc, Expr e)
{
  return vc_query_with_timeout(vc, e, -1, -1);
}

int vc_query_with_timeout(VC vc, Expr e, int timeout_max_conflicts, int timeout_max_time)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::ASTNode* a = (stp::ASTNode*)e;
  stp::STPMgr* b = stp_i->bm;

  // Make this checker's manager current so floating-point blasting during the
  // solve targets it, not whichever checker was created or solved last.
  stp::GlobalParserBM = b;

  /*
   * -1 is the only negative value that means anything ("no limit"). Reject
   * the rest rather than silently running unlimited, which is the dangerous
   * direction for a caller that computed a budget and got the sign wrong.
   */
  if (timeout_max_conflicts < -1)
  {
    std::cerr << "CInterface: timeout_max_conflicts must be -1 (no limit) or "
                 "greater"
              << std::endl;
    return 2;
  }

  if (timeout_max_time < -1)
  {
    std::cerr << "CInterface: timeout_max_time must be -1 (no limit) or greater"
              << std::endl;
    return 2;
  }

  if (!stp::is_Form_kind(a->GetKind()))
  {
    stp::FatalError("CInterface: Trying to QUERY a NON formula: ", *a);
  }

  assert(BVTypeCheck(*a));
  // Cached in case someone runs PrintQuery()
  b->SetQuery(*a);

  stp_i->ClearAllTables();

  const stp::ASTVec v = b->GetAsserts();
  stp::ASTNode o;
  int output;
  stp_i->bm->UserFlags.timeout_max_conflicts = timeout_max_conflicts;
  stp_i->bm->UserFlags.timeout_max_time = timeout_max_time;
  if (!v.empty())
  {
    if (v.size() == 1)
    {
      output = stp_i->TopLevelSTP(v[0], *a);
    }
    else
    {
      output = stp_i->TopLevelSTP(b->CreateNode(stp::AND, v), *a);
    }
  }
  else
  {
    output = stp_i->TopLevelSTP(b->CreateNode(stp::TRUE), *a);
  }

  return output;
}

// int vc_absRefineQuery(VC vc, Expr e) {
//   stp::STP* stp_i = (stp::STP*)vc;
//   stp::ASTNode* a = (stp::ASTNode*)e;
//   stp::STPMgr* b   = stp_i->bm;

//   if(!stp::is_Form_kind(a->GetKind()))
//     stp::FatalError("CInterface: Trying to QUERY a NON formula: ",*a);

//   //a->LispPrint(cout, 0);
//   //printf("##################################################\n");
//   BVTypeCheck(*a);
//   b->AddQuery(*a);

//   const stp::ASTVec v = b->GetAsserts();
//   stp::ASTNode o;
//   if(!v.empty()) {
//     if(v.size()==1)
//       return b->TopLevelSTP(v[0],*a);
//     else
//       return b->TopLevelSTP(b->CreateNode(stp::AND,v),*a);
//   }
//   else
//     return b->TopLevelSTP(b->CreateNode(stp::TRUE),*a);
// }

void vc_push(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp_i->ClearAllTables();
  b->Push();
}

//NB, doesn't remove symbols from decls, so they will be kept alive.
void vc_pop(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  b->Pop();
}

void vc_printCounterExample(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  bool currentPrint = b->UserFlags.print_counterexample_flag;
  b->UserFlags.print_counterexample_flag = true;
  cout << "COUNTEREXAMPLE BEGIN: \n";
  ce->PrintCounterExample(true);
  cout << "COUNTEREXAMPLE END: \n";
  b->UserFlags.print_counterexample_flag = currentPrint;
}

// //! Return the counterexample after a failed query.
// /*! This method should only be called after a query which returns
//  * false.  It will try to return the simplest possible set of
//  * assertions which are sufficient to make the queried expression
//  * false.  The caller is responsible for freeing the array when
//  * finished with it.
//  */

Expr vc_getCounterExample(VC vc, Expr e)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::ASTNode* a = (stp::ASTNode*)e;

  // Reading a floating-point value blasts the term, so this checker's manager
  // must be current (see vc_query_with_timeout).
  stp::GlobalParserBM = stp_i->bm;

  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);
  stp::ASTNode* output = new stp::ASTNode(ce->GetCounterExample(*a));
  return output;
}

void vc_getCounterExampleArray(VC vc, Expr e, Expr** indices, Expr** values,
                               int* size)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::ASTNode* a = (stp::ASTNode*)e;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  bool t = false;
  if (ce->CounterExampleSize())
    t = true;

  vector<std::pair<ASTNode, ASTNode>> entries =
      ce->GetCounterExampleArray(t, *a);
  *size = entries.size();
  if (*size != 0)
  {
    *indices = (Expr*)malloc(*size * sizeof(Expr*));
    assert(*indices);
    *values = (Expr*)malloc(*size * sizeof(Expr*));
    assert(*values);

    for (int i = 0; i < *size; ++i)
    {
      (*indices)[i] = new stp::ASTNode(entries[i].first);
      (*values)[i] = new stp::ASTNode(entries[i].second);
    }
  }
}

void vc_deleteCounterExampleArray(Expr* indices, Expr* values, int size)
{
  if (size <= 0)
    return;
  for (int i = 0; i < size; ++i)
  {
    delete (stp::ASTNode*)indices[i];
    delete (stp::ASTNode*)values[i];
  }
  free(indices);
  free(values);
}

int vc_counterexample_size(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);
  return ce->CounterExampleSize();
}

WholeCounterExample vc_getWholeCounterExample(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  stp::CompleteCounterExample* c =
      new stp::CompleteCounterExample(ce->GetCompleteCounterExample(), b);
  return c;
}

Expr vc_getTermFromCounterExample(VC /*vc*/, Expr e, WholeCounterExample cc)
{
  stp::ASTNode* n = (stp::ASTNode*)e;
  stp::CompleteCounterExample* c = (stp::CompleteCounterExample*)cc;

  stp::ASTNode* output = new stp::ASTNode(c->GetCounterExample(*n));
  return output;
}

void vc_deleteWholeCounterExample(WholeCounterExample cc)
{
  stp::CompleteCounterExample* c = (stp::CompleteCounterExample*)cc;

  delete c;
}

int vc_getBVLength(VC /*vc*/, Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;

  if (stp::BITVECTOR_TYPE != e->GetType())
  {
    stp::FatalError("c_interface: vc_GetBVLength: "
                    "Input expression must be a bit-vector");
  }
  return e->GetValueWidth();
}

/////////////////////////////////////////////////////////////////////////////
// Expr Creation methods                                                   //
/////////////////////////////////////////////////////////////////////////////
//! Create a variable with a given name and type
/*! The type cannot be a function type. */
Expr vc_varExpr1(VC vc, const char* name, int indexwidth, int valuewidth)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::ASTNode o = b->CreateSymbol(name, indexwidth, valuewidth);

  stp::ASTNode* output = new stp::ASTNode(o);
  ////if(cinterface_exprdelete_on) created_exprs.push_back(output);
  assert(BVTypeCheck(*output));

  // store the decls in a vector for printing purposes
  b->decls.push_back(o);
  return output;
}

Expr vc_varExpr(VC vc, const char* name, Type type)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  std::pair<unsigned int, unsigned int> typeSizes(getTypeSizes(type));
  unsigned int valueWidth = typeSizes.first;
  unsigned int indexWidth = typeSizes.second;
  stp::ASTNode o = b->CreateSymbol(name, indexWidth, valueWidth);

  // A floating-point variable additionally carries its format (exponent and
  // significand widths); getTypeSizes above only gave the packed value width.
  stp::ASTNode* typeNode = (stp::ASTNode*)type;
  if (typeNode->GetKind() == stp::FLOATINGPOINT)
  {
    o.SetExpWidth((*typeNode)[0].GetUnsignedConst());
    o.SetSigWidth((*typeNode)[1].GetUnsignedConst());
  }

  // A RoundingMode variable must range over exactly the five modes: pin the
  // 5-bit carrier to the one-hot encodings (asserted at the current
  // assertion level) and register the symbol so counterexamples print its
  // value by mode name -- exactly as the parser declares one.
  if (typeNode->GetKind() == stp::ROUNDINGMODE)
  {
    b->rounding_mode_symbols.insert(o);
    b->AddAssert(b->roundingModeValidConstraint(o));
  }

  // An array symbol records what its widths cannot say, exactly as the
  // parser's declarations do: a float element's format rides on the node
  // (reads inherit it -- see deriveFPFormat), while a float index format
  // and RoundingMode on either side go into the manager's registries.
  // Reads from a RoundingMode-element array are pinned to the five legal
  // encodings at solve time (see FpTotalise), so no assertion is needed
  // here.
  if (typeNode->GetKind() == stp::ARRAY)
  {
    const stp::ASTNode& indexType = (*typeNode)[0];
    const stp::ASTNode& dataType = (*typeNode)[1];

    if (dataType.GetKind() == stp::FLOATINGPOINT)
    {
      o.SetExpWidth(dataType[0].GetUnsignedConst());
      o.SetSigWidth(dataType[1].GetUnsignedConst());
    }
    if (dataType.GetKind() == stp::ROUNDINGMODE)
      b->rm_element_arrays.insert(o);
    if (indexType.GetKind() == stp::FLOATINGPOINT)
      b->fp_index_arrays[o] = std::make_pair(
          indexType[0].GetUnsignedConst(), indexType[1].GetUnsignedConst());
    if (indexType.GetKind() == stp::ROUNDINGMODE)
      b->rm_index_arrays.insert(o);
  }

  stp::ASTNode* output = new stp::ASTNode(o);
  ////if(cinterface_exprdelete_on) created_exprs.push_back(output);
  assert(BVTypeCheck(*output));

  // store the decls in a vector for printing purposes
  b->decls.push_back(o);
  return output;
}

//! Create an equality expression.  The two children must have the
// same type.
Expr vc_eqExpr(VC vc, Expr ccc0, Expr ccc1)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::ASTNode* a = (stp::ASTNode*)ccc0;
  stp::ASTNode* aa = (stp::ASTNode*)ccc1;
  assert(BVTypeCheck(*a));
  assert(BVTypeCheck(*aa));

  // SMT-LIB '=' over floats is FP_SMT_EQ, not the generic EQ, mirroring the
  // parser's (= ...) rule: +0 and -0 stay distinct, and every NaN equals
  // every NaN. A plain EQ over floating-point operands is a node the later
  // passes cannot discharge -- the solve died without a conclusion (found
  // by murxla; vc_fpEqExpr's doc sends '=' callers here, so this is the
  // documented route). With only one float operand, FP_SMT_EQ's typecheck
  // then rejects the float/bitvector mix, exactly as the parser does.
  const stp::Kind k = (a->GetType() == stp::FLOATINGPOINT_TYPE ||
                       aa->GetType() == stp::FLOATINGPOINT_TYPE)
                          ? stp::FP_SMT_EQ
                          : stp::EQ;
  stp::ASTNode o = b->CreateNode(k, *a, *aa);

  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_boolType(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::ASTNode output = b->CreateNode(stp::BOOLEAN);
  return persistNode(vc, output);
}

// ---------------------------------------------------------------------------
// Floating point
// ---------------------------------------------------------------------------

Type vc_fpType(VC vc, int exp_bits, int sig_bits)
{
#ifndef STP_ENABLE_FLOATING_POINT
  // Refuse at the API's natural entry point. Anything that slips past --
  // this is the only vc_fp* call that neither takes nor produces a
  // floating-point term -- is caught when SetExpWidth/CreateFPConst first
  // stamp a format.
  (void)vc;
  (void)exp_bits;
  (void)sig_bits;
  stp::FatalError("CInterface: vc_fpType: this STP was built without "
                  "floating-point support; reconfigure with "
                  "-DENABLE_FLOATING_POINT=ON");
#else
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  if (exp_bits < 2 || sig_bits < 2)
  {
    stp::FatalError("CInterface: vc_fpType: a floating-point format needs at "
                    "least 2 exponent and 2 significand bits");
  }

  // Mirror vc_bvType/vc_arrayType: a type is a node whose children hold the
  // widths -- here the exponent and significand widths.
  stp::ASTNode e = b->CreateBVConst(32, exp_bits);
  stp::ASTNode s = b->CreateBVConst(32, sig_bits);
  stp::ASTNode output = b->CreateNode(stp::FLOATINGPOINT, e, s);
  return persistNode(vc, output);
#endif
}

Type vc_fpRoundingModeType(VC vc)
{
#ifndef STP_ENABLE_FLOATING_POINT
  // Refused at the entry point, like vc_fpType: a type node neither takes
  // nor produces a floating-point term, so the STPMgr format funnels would
  // never catch it.
  (void)vc;
  stp::FatalError("CInterface: vc_fpRoundingModeType: this STP was built "
                  "without floating-point support; reconfigure with "
                  "-DENABLE_FLOATING_POINT=ON");
#else
  stp::STPMgr* b = ((stp::STP*)vc)->bm;

  // The sort has no parameters, so the type node is childless; vc_varExpr
  // recognises it and builds the constrained 5-bit variable.
  return persistNode(vc, b->CreateNode(stp::ROUNDINGMODE));
#endif
}

int vc_getExpWidth(Expr e)
{
  return (int)((stp::ASTNode*)e)->GetExpWidth();
}

int vc_getSigWidth(Expr e)
{
  return (int)((stp::ASTNode*)e)->GetSigWidth();
}

Expr vc_fpConstFromBits(VC vc, int exp_bits, int sig_bits, Expr bv)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* bits = (stp::ASTNode*)bv;

  if (bits->GetKind() != stp::BVCONST)
  {
    stp::FatalError("CInterface: vc_fpConstFromBits: the bits argument must be "
                    "a bitvector constant: ",
                    *bits);
  }
  if ((int)bits->GetValueWidth() != exp_bits + sig_bits)
  {
    stp::FatalError("CInterface: vc_fpConstFromBits: the bitvector width must "
                    "equal exp_bits + sig_bits: ",
                    *bits);
  }

  stp::ASTNode output = b->CreateFPConst(*bits, exp_bits, sig_bits);
  return persistNode(vc, output);
}

Expr vc_fpEqExpr(VC vc, Expr a, Expr b)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* bm = stp_i->bm;
  stp::ASTNode* l = (stp::ASTNode*)a;
  stp::ASTNode* r = (stp::ASTNode*)b;

  stp::ASTNode output = bm->CreateNode(stp::FP_EQ, *l, *r);
  assert(BVTypeCheck(output));
  return persistNode(vc, output);
}

// A floating-point operation returns a value of the same format as its
// operands, so the result node carries the format taken from `fmt` (as the
// parser's setFPFormat does).
static Expr fpTermResult(VC vc, stp::Kind k, const stp::ASTNode& fmt,
                         const stp::ASTVec& children)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  if (fmt.GetType() != stp::FLOATINGPOINT_TYPE)
  {
    stp::FatalError("CInterface: floating-point operation applied to a "
                    "non-float operand: ",
                    fmt);
  }
  stp::ASTNode r = b->CreateTerm(k, fmt.GetValueWidth(), children);
  r.SetExpWidth(fmt.GetExpWidth());
  r.SetSigWidth(fmt.GetSigWidth());
  assert(BVTypeCheck(r));
  return persistNode(vc, r);
}

// A floating-point predicate returns a Boolean and carries no format.
static Expr fpPredResult(VC vc, stp::Kind k, const stp::ASTVec& children)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  stp::ASTNode r = b->CreateNode(k, children);
  assert(BVTypeCheck(r));
  return persistNode(vc, r);
}

Expr vc_fpRoundingMode(VC vc, enum VCRoundingMode mode)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;

  // The enum's values are one-hot (they mirror the internal encoding), so a
  // plausible-looking OR of two modes is not a mode; anything but the five
  // exact values would silently fall through symfpu's mode dispatch.
  switch (mode)
  {
    case VC_RM_RNE:
    case VC_RM_RTP:
    case VC_RM_RTN:
    case VC_RM_RTZ:
    case VC_RM_RNA:
      break;
    default:
      stp::FatalError("CInterface: vc_fpRoundingMode: not one of the five "
                      "rounding modes");
  }

  // A rounding mode is a 5-bit one-hot bitvector constant.
  return persistNode(vc, b->CreateBVConst(5, (unsigned long long)mode));
}

Expr vc_fpRoundingModeVar(VC vc, const char* name)
{
  // Convenience for vc_varExpr over vc_fpRoundingModeType, which does the
  // real work: a 5-bit symbol pinned to the five one-hot encodings and
  // registered so counterexamples print its value by mode name. (Without
  // the constraint the carrier's 27 junk values would be satisfiable
  // "modes", which is also why a plain 5-bit vc_varExpr is no substitute.)
  return vc_varExpr(vc, name, vc_fpRoundingModeType(vc));
}

Expr vc_fpAbsExpr(VC vc, Expr f)
{
  stp::ASTNode* x = (stp::ASTNode*)f;
  return fpTermResult(vc, stp::FP_ABS, *x, {*x});
}

Expr vc_fpNegExpr(VC vc, Expr f)
{
  stp::ASTNode* x = (stp::ASTNode*)f;
  return fpTermResult(vc, stp::FP_NEG, *x, {*x});
}

Expr vc_fpAddExpr(VC vc, Expr rm, Expr a, Expr b)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  return fpTermResult(vc, stp::FP_ADD, *x, {*m, *x, *y});
}

Expr vc_fpSubExpr(VC vc, Expr rm, Expr a, Expr b)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  return fpTermResult(vc, stp::FP_SUB, *x, {*m, *x, *y});
}

Expr vc_fpMulExpr(VC vc, Expr rm, Expr a, Expr b)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  return fpTermResult(vc, stp::FP_MUL, *x, {*m, *x, *y});
}

Expr vc_fpDivExpr(VC vc, Expr rm, Expr a, Expr b)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  return fpTermResult(vc, stp::FP_DIV, *x, {*m, *x, *y});
}

Expr vc_fpFMAExpr(VC vc, Expr rm, Expr a, Expr b, Expr c)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  stp::ASTNode* z = (stp::ASTNode*)c;
  return fpTermResult(vc, stp::FP_FMA, *x, {*m, *x, *y, *z});
}

Expr vc_fpSqrtExpr(VC vc, Expr rm, Expr f)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)f;
  return fpTermResult(vc, stp::FP_SQRT, *x, {*m, *x});
}

Expr vc_fpRoundToIntegralExpr(VC vc, Expr rm, Expr f)
{
  stp::ASTNode* m = (stp::ASTNode*)rm;
  stp::ASTNode* x = (stp::ASTNode*)f;
  return fpTermResult(vc, stp::FP_ROUNDTOINTEGRAL, *x, {*m, *x});
}

Expr vc_fpRemExpr(VC vc, Expr a, Expr b)
{
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  // The remainder circuit's unrolling is exponential in the exponent width;
  // refuse at term creation, where the caller can see it, rather than
  // during solving (the parser does the same for SMT-LIB input).
  if (!stp::FloatBlaster::remSupported(x->GetExpWidth(), x->GetSigWidth()))
  {
    stp::FatalError("CInterface: vc_fpRemExpr: fp.rem is not supported at "
                    "this format: its circuit unrolls one divide step per "
                    "representable exponent difference, which is exponential "
                    "in the exponent width; use a format no larger than "
                    "binary64");
  }
  return fpTermResult(vc, stp::FP_REM, *x, {*x, *y});
}

Expr vc_fpMinExpr(VC vc, Expr a, Expr b)
{
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  return fpTermResult(vc, stp::FP_MIN, *x, {*x, *y});
}

Expr vc_fpMaxExpr(VC vc, Expr a, Expr b)
{
  stp::ASTNode* x = (stp::ASTNode*)a;
  stp::ASTNode* y = (stp::ASTNode*)b;
  return fpTermResult(vc, stp::FP_MAX, *x, {*x, *y});
}

Expr vc_fpLtExpr(VC vc, Expr a, Expr b)
{
  return fpPredResult(vc, stp::FP_LT, {*(stp::ASTNode*)a, *(stp::ASTNode*)b});
}

Expr vc_fpLeqExpr(VC vc, Expr a, Expr b)
{
  return fpPredResult(vc, stp::FP_LEQ, {*(stp::ASTNode*)a, *(stp::ASTNode*)b});
}

Expr vc_fpGtExpr(VC vc, Expr a, Expr b)
{
  return fpPredResult(vc, stp::FP_GT, {*(stp::ASTNode*)a, *(stp::ASTNode*)b});
}

Expr vc_fpGeqExpr(VC vc, Expr a, Expr b)
{
  return fpPredResult(vc, stp::FP_GEQ, {*(stp::ASTNode*)a, *(stp::ASTNode*)b});
}

Expr vc_fpIsNormalExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISNORMAL, {*(stp::ASTNode*)f});
}

Expr vc_fpIsSubnormalExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISSUBNORMAL, {*(stp::ASTNode*)f});
}

Expr vc_fpIsZeroExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISZERO, {*(stp::ASTNode*)f});
}

Expr vc_fpIsInfiniteExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISINFINITE, {*(stp::ASTNode*)f});
}

Expr vc_fpIsNaNExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISNAN, {*(stp::ASTNode*)f});
}

Expr vc_fpIsNegativeExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISNEGATIVE, {*(stp::ASTNode*)f});
}

Expr vc_fpIsPositiveExpr(VC vc, Expr f)
{
  return fpPredResult(vc, stp::FP_ISPOSITIVE, {*(stp::ASTNode*)f});
}

// Some entry points take the format as raw ints rather than a type node;
// apply vc_fpType's floor so they cannot produce degenerate widths.
static void checkFpWidths(int eb, int sb)
{
  if (eb < 2 || sb < 2)
  {
    stp::FatalError("CInterface: a floating-point format needs at least 2 "
                    "exponent and 2 significand bits");
  }
}

// Extract (eb, sb) from a floating-point type node (see vc_fpType).
static void fpTypeWidths(Type fpType, unsigned& eb, unsigned& sb)
{
  stp::ASTNode* t = (stp::ASTNode*)fpType;
  if (t->GetKind() != stp::FLOATINGPOINT)
  {
    // Reading children of, say, a bitvector type would index out of bounds.
    stp::FatalError("CInterface: expected a floating-point type "
                    "(from vc_fpType): ",
                    *t);
  }
  eb = (*t)[0].GetUnsignedConst();
  sb = (*t)[1].GetUnsignedConst();
}

static Expr fpSpecial(VC vc, stp::FPSpecial which, Type fpType)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  unsigned eb, sb;
  fpTypeWidths(fpType, eb, sb);
  return persistNode(vc, b->CreateFPSpecialConst(which, eb, sb));
}

Expr vc_fpNaN(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::NaN, fpType);
}
Expr vc_fpPlusInfinity(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::PlusInfinity, fpType);
}
Expr vc_fpMinusInfinity(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::MinusInfinity, fpType);
}
Expr vc_fpPlusZero(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::PlusZero, fpType);
}
Expr vc_fpMinusZero(VC vc, Type fpType)
{
  return fpSpecial(vc, stp::FPSpecial::MinusZero, fpType);
}

// Build a to_fp node: the (eb,sb) width children the blaster reads, an
// optional rounding mode, then the source. The result is a float of (eb, sb).
// `k` is FP_TOFP for the bits and float-to-float forms and FP_TOFP_SIGNED for
// the integer one. SMT-LIB spells all three `to_fp` and tells them apart by
// the source's sort, but a float is carried as its packed bits, so the sort
// stops being readable the moment the source is lowered. Each entry point
// below knows which operation the caller asked for; the kind records it.
static Expr fpToFP(VC vc, stp::Kind k, int eb, int sb, const stp::ASTNode* rm,
                   const stp::ASTNode& src)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  checkFpWidths(eb, sb);
  stp::ASTVec kids;
  kids.push_back(b->CreateBVConst(32, eb));
  kids.push_back(b->CreateBVConst(32, sb));
  if (rm != NULL)
    kids.push_back(*rm);
  kids.push_back(src);
  stp::ASTNode r = b->CreateTerm(k, eb + sb, kids);
  r.SetExpWidth(eb);
  r.SetSigWidth(sb);
  return persistNode(vc, r);
}

Expr vc_fpToFPFromIEEEBV(VC vc, int eb, int sb, Expr bv)
{
  return fpToFP(vc, stp::FP_TOFP, eb, sb, NULL, *(stp::ASTNode*)bv);
}

Expr vc_fpToFPFromFP(VC vc, int eb, int sb, Expr rm, Expr f)
{
  return fpToFP(vc, stp::FP_TOFP, eb, sb, (stp::ASTNode*)rm, *(stp::ASTNode*)f);
}

Expr vc_fpToFPFromSignedBV(VC vc, int eb, int sb, Expr rm, Expr bv)
{
  return fpToFP(vc, stp::FP_TOFP_SIGNED, eb, sb, (stp::ASTNode*)rm,
                *(stp::ASTNode*)bv);
}

Expr vc_fpToFPFromUnsignedBV(VC vc, int eb, int sb, Expr rm, Expr bv)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  checkFpWidths(eb, sb);
  stp::ASTVec kids;
  kids.push_back(b->CreateBVConst(32, eb));
  kids.push_back(b->CreateBVConst(32, sb));
  kids.push_back(*(stp::ASTNode*)rm);
  kids.push_back(*(stp::ASTNode*)bv);
  stp::ASTNode r = b->CreateTerm(stp::FP_TOFP_UNSIGNED, eb + sb, kids);
  r.SetExpWidth(eb);
  r.SetSigWidth(sb);
  return persistNode(vc, r);
}

// fp.to_ubv / fp.to_sbv: a float in, a `width`-bit bitvector out. The result is
// a bitvector, so it carries no floating-point format.
static Expr fpToBV(VC vc, stp::Kind k, int width, const stp::ASTNode& rm,
                   const stp::ASTNode& f)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  if (width < 1)
  {
    stp::FatalError("CInterface: fp.to_ubv/fp.to_sbv need a positive "
                    "target width");
  }
  if (f.GetType() != stp::FLOATINGPOINT_TYPE)
  {
    stp::FatalError("CInterface: fp.to_ubv/fp.to_sbv applied to a "
                    "non-float: ",
                    f);
  }
  stp::ASTVec kids;
  kids.push_back(b->CreateBVConst(32, width));
  kids.push_back(rm);
  kids.push_back(f);
  return persistNode(vc, b->CreateTerm(k, width, kids));
}

Expr vc_fpToUBVExpr(VC vc, int width, Expr rm, Expr f)
{
  return fpToBV(vc, stp::FP_TO_UBV, width, *(stp::ASTNode*)rm,
                *(stp::ASTNode*)f);
}

Expr vc_fpToSBVExpr(VC vc, int width, Expr rm, Expr f)
{
  return fpToBV(vc, stp::FP_TO_SBV, width, *(stp::ASTNode*)rm,
                *(stp::ASTNode*)f);
}

Expr vc_fpToIEEEBV(VC vc, Expr f)
{
  stp::STPMgr* b = ((stp::STP*)vc)->bm;
  stp::ASTNode* x = (stp::ASTNode*)f;
  if (x->GetType() != stp::FLOATINGPOINT_TYPE)
  {
    stp::FatalError("CInterface: vc_fpToIEEEBV applied to a non-float: ", *x);
  }
  const unsigned width = x->GetExpWidth() + x->GetSigWidth();
  // The result is a bitvector (the packed bits), so it carries no fp format.
  return persistNode(vc, b->CreateTerm(stp::FP_TO_IEEE_BV, width, *x));
}

Expr vc_fpConstFromDouble(VC vc, Type target, Expr rm, double d)
{
  uint64_t bits;
  std::memcpy(&bits, &d, sizeof(bits)); // d is already IEEE-754 binary64
  Expr dbl =
      vc_fpConstFromBits(vc, 11, 53, vc_bvConstExprFromLL(vc, 64, bits));
  unsigned eb, sb;
  fpTypeWidths(target, eb, sb);
  if (eb == 11 && sb == 53)
    return dbl; // target is binary64: the reinterpret is exact
  return vc_fpToFPFromFP(vc, eb, sb, rm, dbl);
}

Expr vc_fpConstFromFloat(VC vc, Type target, Expr rm, float f)
{
  uint32_t bits;
  std::memcpy(&bits, &f, sizeof(bits)); // f is already IEEE-754 binary32
  Expr single =
      vc_fpConstFromBits(vc, 8, 24, vc_bvConstExprFromLL(vc, 32, bits));
  unsigned eb, sb;
  fpTypeWidths(target, eb, sb);
  if (eb == 8 && sb == 24)
    return single; // target is binary32: the reinterpret is exact
  return vc_fpToFPFromFP(vc, eb, sb, rm, single);
}

/////////////////////////////////////////////////////////////////////////////
// BOOLEAN EXPR Creation methods                                           //
/////////////////////////////////////////////////////////////////////////////
// The following functions create Boolean expressions.  The children
// provided as arguments must be of type Boolean.
Expr vc_trueExpr(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode c = b->CreateNode(stp::TRUE);

  stp::ASTNode* d = new stp::ASTNode(c);
  // if(cinterface_exprdelete_on) created_exprs.push_back(d);
  return d;
}

Expr vc_falseExpr(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode c = b->CreateNode(stp::FALSE);

  stp::ASTNode* d = new stp::ASTNode(c);
  // if(cinterface_exprdelete_on) created_exprs.push_back(d);
  return d;
}

Expr vc_notExpr(VC vc, Expr ccc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;

  stp::ASTNode o = b->CreateNode(stp::NOT, *a);
  assert(BVTypeCheck(o));

  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_andExpr(VC vc, Expr left, Expr right)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  stp::ASTNode o = b->CreateNode(stp::AND, *l, *r);
  assert(BVTypeCheck(o));

  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_orExpr(VC vc, Expr left, Expr right)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  stp::ASTNode o = b->CreateNode(stp::OR, *l, *r);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_xorExpr(VC vc, Expr left, Expr right)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  stp::ASTNode o = b->CreateNode(stp::XOR, *l, *r);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_nandExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::NAND, left, right);
}

Expr vc_norExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::NOR, left, right);
}

Expr vc_andExprN(VC vc, Expr* cc, int n)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode** c = (stp::ASTNode**)cc;
  assert(n > 0);

  stp::ASTVec d;
  for (int i = 0; i < n; i++)
  {
    d.push_back(*c[i]);
  }

  stp::ASTNode o = b->CreateNode(stp::AND, d);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);

  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_orExprN(VC vc, Expr* cc, int n)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode** c = (stp::ASTNode**)cc;
  stp::ASTVec d;

  for (int i = 0; i < n; i++)
    d.push_back(*c[i]);

  stp::ASTNode o = b->CreateNode(stp::OR, d);
  assert(BVTypeCheck(o));

  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvPlusExprN(VC vc, int n_bits, Expr* cc, int n)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode** c = (stp::ASTNode**)cc;
  stp::ASTVec d;

  for (int i = 0; i < n; i++)
    d.push_back(*c[i]);

  stp::ASTNode o = b->CreateTerm(stp::BVPLUS, n_bits, d);
  assert(BVTypeCheck(o));

  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_iteExpr(VC vc, Expr cond, Expr thenpart, Expr elsepart)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* c = (stp::ASTNode*)cond;
  stp::ASTNode* t = (stp::ASTNode*)thenpart;
  stp::ASTNode* e = (stp::ASTNode*)elsepart;

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));
  assert(BVTypeCheck(*e));
  stp::ASTNode o;
  // if the user asks for a formula then produce a formula, else
  // prodcue a term
  if (stp::BOOLEAN_TYPE == t->GetType())
    o = b->CreateNode(stp::ITE, *c, *t, *e);
  else
  {
    o = b->CreateTerm(stp::ITE, t->GetValueWidth(), *c, *t, *e);
    o.SetIndexWidth(t->GetIndexWidth());
  }
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_impliesExpr(VC vc, Expr antecedent, Expr consequent)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* c = (stp::ASTNode*)antecedent;
  stp::ASTNode* t = (stp::ASTNode*)consequent;

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));
  stp::ASTNode o;

  o = b->CreateNode(stp::IMPLIES, *c, *t);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_iffExpr(VC vc, Expr e0, Expr e1)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* c = (stp::ASTNode*)e0;
  stp::ASTNode* t = (stp::ASTNode*)e1;

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));
  stp::ASTNode o;

  o = b->CreateNode(stp::IFF, *c, *t);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_boolToBVExpr(VC vc, Expr form)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* c = (stp::ASTNode*)form;

  assert(BVTypeCheck(*c));
  if (!is_Form_kind(c->GetKind()))
  {
    stp::FatalError("CInterface: vc_BoolToBVExpr: "
                    "You have input a NON formula:",
                    *c);
  }

  stp::ASTNode o;
  stp::ASTNode one = b->CreateOneConst(1);
  stp::ASTNode zero = b->CreateZeroConst(1);
  o = b->CreateTerm(stp::ITE, 1, *c, one, zero);

  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_paramBoolExpr(VC vc, Expr boolvar, Expr parameter)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* c = (stp::ASTNode*)boolvar;
  stp::ASTNode* t = (stp::ASTNode*)parameter;

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));
  stp::ASTNode o;

  o = b->CreateNode(stp::PARAMBOOL, *c, *t);
  // BVTypeCheck(o);
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

/////////////////////////////////////////////////////////////////////////////
// BITVECTOR EXPR Creation methods                                         //
/////////////////////////////////////////////////////////////////////////////
Type vc_bvType(VC vc, int num_bits)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  if (!(0 < num_bits))
  {
    stp::FatalError("CInterface: number of bits in a bvtype"
                    " must be a positive integer:",
                    b->CreateNode(stp::UNDEFINED));
  }

  stp::ASTNode e = b->CreateBVConst(32, num_bits);
  stp::ASTNode output = (b->CreateNode(stp::BITVECTOR, e));
  return persistNode(vc, output);
}

Type vc_bv32Type(VC vc)
{
  return vc_bvType(vc, 32);
}

int vc_getValueSize(VC /* vc */, Type type)
{
  std::pair<unsigned int, unsigned int> typeSizes(getTypeSizes(type));
  unsigned int valueWidth = typeSizes.first;
  return valueWidth;
}

int vc_getIndexSize(VC /* vc */, Type type)
{
  std::pair<unsigned int, unsigned int> typeSizes(getTypeSizes(type));
  unsigned int indexWidth = typeSizes.second;
  return indexWidth;
}

Expr vc_bvConstExprFromDecStr(VC vc, int width, const char* decimalInput)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  std::string str(decimalInput);
  stp::ASTNode n = b->CreateBVConst(str, 10, width);
  assert(BVTypeCheck(n));
  stp::ASTNode* output = new stp::ASTNode(n);
  return output;
}

Expr vc_bvConstExprFromStr(VC vc, const char* binary_repr)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::ASTNode n = b->CreateBVConst(binary_repr, 2);
  assert(BVTypeCheck(n));
  stp::ASTNode* output = new stp::ASTNode(n);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvConstExprFromInt(VC vc, int n_bits, unsigned int value)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  unsigned long long int v = (unsigned long long int)value;

  // Only check that the value fits when the width is narrow enough for the
  // question to be interesting. At 64 bits and above every unsigned int fits,
  // and the shift below would be by a negative amount -- which is undefined,
  // and in practice wraps to a small max, rejecting perfectly good constants.
  // Widths above 64 are reachable: symfpu works internally at widths derived
  // from the format, and the x87 extended format (15, 64) takes it past 64.
  if (n_bits < 64)
  {
    const unsigned long long int max_n_bits =
        0xFFFFFFFFFFFFFFFFULL >> (64 - n_bits);
    if (v > max_n_bits)
    {
      printf("CInterface: vc_bvConstExprFromInt: "
             "Cannot construct a constant %llu >= %llu,\n",
             v, max_n_bits);
      stp::FatalError("FatalError");
    }
  }
  stp::ASTNode n = b->CreateBVConst(n_bits, v);
  assert(BVTypeCheck(n));
  return persistNode(vc, n);
}

Expr vc_bvConstExprFromLL(VC vc, int n_bits, unsigned long long value)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::ASTNode n = b->CreateBVConst(n_bits, value);
  assert(BVTypeCheck(n));
  stp::ASTNode* output = new stp::ASTNode(n);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvConcatExpr(VC vc, Expr left, Expr right)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));
  stp::ASTNode o = b->CreateTerm(
      stp::BVCONCAT, l->GetValueWidth() + r->GetValueWidth(), *l, *r);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr createBinaryTerm(VC vc, int n_bits, Kind k, Expr left, Expr right)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));
  stp::ASTNode o = b->CreateTerm(k, n_bits, *l, *r);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvPlusExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVPLUS, left, right);
}

Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right)
{
  return vc_bvPlusExpr(vc, 32, left, right);
}

Expr vc_bvMinusExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVSUB, left, right);
}

Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right)
{
  return vc_bvMinusExpr(vc, 32, left, right);
}

Expr vc_bvMultExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVMULT, left, right);
}

Expr vc_bvDivExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVDIV, left, right);
}

Expr vc_bvModExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVMOD, left, right);
}

Expr vc_bvRemExpr(VC vc, int n_bits, Expr left, Expr right)
{
  /*
   * bvurem gets mapped to BVMOD -- this is a wrapper to
   * allow for API consistency
   */
  return createBinaryTerm(vc, n_bits, stp::BVMOD, left, right);
}

Expr vc_sbvDivExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::SBVDIV, left, right);
}

Expr vc_sbvModExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::SBVMOD, left, right);
}

Expr vc_sbvRemExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::SBVREM, left, right);
}

Expr vc_bv32MultExpr(VC vc, Expr left, Expr right)
{
  return vc_bvMultExpr(vc, 32, left, right);
}

Expr createBinaryNode(VC vc, Kind k, Expr left, Expr right)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;
  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));
  stp::ASTNode o = b->CreateNode(k, *l, *r);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on)
  //  created_exprs.push_back(output);
  return output;
}

// unsigned comparators
Expr vc_bvLtExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVLT, left, right);
}
Expr vc_bvLeExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVLE, left, right);
}
Expr vc_bvGtExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVGT, left, right);
}
Expr vc_bvGeExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVGE, left, right);
}
// signed comparators
Expr vc_sbvLtExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSLT, left, right);
}
Expr vc_sbvLeExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSLE, left, right);
}
Expr vc_sbvGtExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSGT, left, right);
}
Expr vc_sbvGeExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSGE, left, right);
}

// overflow predicates
Expr vc_bvUnsignedAddOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVUADDO, left, right);
}
Expr vc_bvSignedAddOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSADDO, left, right);
}
Expr vc_bvUnsignedSubOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVUSUBO, left, right);
}
Expr vc_bvSignedSubOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSSUBO, left, right);
}
Expr vc_bvUnsignedMulOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVUMULO, left, right);
}
Expr vc_bvSignedMulOverflowExpr(VC vc, Expr left, Expr right)
{
  return createBinaryNode(vc, stp::BVSMULO, left, right);
}

Expr vc_bvLeftShiftExprExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVLEFTSHIFT, left, right);
}

Expr vc_bvRightShiftExprExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVRIGHTSHIFT, left, right);
}

Expr vc_bvSignedRightShiftExprExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits, stp::BVSRSHIFT, left, right);
}

Expr vc_bvUMinusExpr(VC vc, Expr ccc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  stp::ASTNode* a = (stp::ASTNode*)ccc;
  assert(BVTypeCheck(*a));

  stp::ASTNode o = b->CreateTerm(stp::BVUMINUS, a->GetValueWidth(), *a);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

// Expr createBinaryTerm(VC vc, int n_bits, Kind k, Expr left, Expr right){

// bitwise operations: these are terms not formulas
Expr vc_bvAndExpr(VC vc, Expr left, Expr right)
{
  return createBinaryTerm(vc, (*((stp::ASTNode*)left)).GetValueWidth(),
                          stp::BVAND, left, right);
}

Expr vc_bvOrExpr(VC vc, Expr left, Expr right)
{
  return createBinaryTerm(vc, (*((stp::ASTNode*)left)).GetValueWidth(),
                          stp::BVOR, left, right);
}

Expr vc_bvXorExpr(VC vc, Expr left, Expr right)
{
  return createBinaryTerm(vc, (*((stp::ASTNode*)left)).GetValueWidth(),
                          stp::BVXOR, left, right);
}

/*
 * The bitwise nand/nor/xnor below are built as a negated and/or/xor rather
 * than as the BVNAND/BVNOR/BVXNOR kinds their names suggest. Those kinds are
 * vestigial: no parser produces them -- the SMT-LIB2 grammar expands bvnand,
 * bvnor and bvxnor exactly this way, see lib/Parser/smt2.y -- so while the
 * bit-blaster handles them, constant folding (BVConstEvaluator) and printing
 * (functionToSMTLIBName has no BVXNOR) do not. Building them here would make
 * those kinds reachable for the first time and abort on a constant operand.
 */
static Expr createNegatedBinaryTerm(VC vc, Kind k, Expr left, Expr right)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* l = (stp::ASTNode*)left;
  stp::ASTNode* r = (stp::ASTNode*)right;

  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));

  const unsigned int width = l->GetValueWidth();
  stp::ASTNode o =
      b->CreateTerm(stp::BVNOT, width, b->CreateTerm(k, width, *l, *r));
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  return output;
}

Expr vc_bvNandExpr(VC vc, Expr left, Expr right)
{
  return createNegatedBinaryTerm(vc, stp::BVAND, left, right);
}

Expr vc_bvNorExpr(VC vc, Expr left, Expr right)
{
  return createNegatedBinaryTerm(vc, stp::BVOR, left, right);
}

Expr vc_bvXnorExpr(VC vc, Expr left, Expr right)
{
  return createNegatedBinaryTerm(vc, stp::BVXOR, left, right);
}

Expr vc_bvNotExpr(VC vc, Expr ccc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;

  assert(BVTypeCheck(*a));
  stp::ASTNode o = b->CreateTerm(stp::BVNOT, a->GetValueWidth(), *a);
  assert(BVTypeCheck(o));
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvLeftShiftExpr(VC vc, int sh_amt, Expr ccc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  assert(BVTypeCheck(*a));

  // convert leftshift to bvconcat
  if (0 != sh_amt)
  {
    stp::ASTNode len = b->CreateBVConst(sh_amt, 0);
    stp::ASTNode o =
        b->CreateTerm(stp::BVCONCAT, a->GetValueWidth() + sh_amt, *a, len);
    assert(BVTypeCheck(o));
    stp::ASTNode* output = new stp::ASTNode(o);
    // if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return output;
  }
  else
    return a;
}

Expr vc_bvRightShiftExpr(VC vc, int sh_amt, Expr ccc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  assert(BVTypeCheck(*a));

  unsigned int w = a->GetValueWidth();
  // the amount by which you are rightshifting
  // is less-than/equal-to the length of input
  // bitvector
  if (0 < (unsigned)sh_amt && (unsigned)sh_amt < w)
  {
    stp::ASTNode len = b->CreateBVConst(sh_amt, 0);
    stp::ASTNode hi = b->CreateBVConst(32, w - 1);
    stp::ASTNode low = b->CreateBVConst(32, sh_amt);
    stp::ASTNode extract =
        b->CreateTerm(stp::BVEXTRACT, w - sh_amt, *a, hi, low);

    stp::ASTNode n = b->CreateTerm(stp::BVCONCAT, w, len, extract);
    BVTypeCheck(n);
    stp::ASTNode* output = new stp::ASTNode(n);
    // if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return output;
  }
  else if ((unsigned)sh_amt == w)
  {
    stp::ASTNode* output = new stp::ASTNode(b->CreateBVConst(w, 0));
    return output;
  }
  else if (sh_amt == 0)
    return a;
  else
  {
    if (0 == w)
    {
      stp::FatalError("CInterface: vc_bvRightShiftExpr: "
                      "cannot have a bitvector of length 0:",
                      *a);
    }
    stp::ASTNode* output = new stp::ASTNode(b->CreateBVConst(w, 0));
    // if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return output;
  }
}

/* Same as vc_bvLeftShift only that the answer in 32 bits long */
Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child)
{
  return vc_bvExtract(vc, vc_bvLeftShiftExpr(vc, sh_amt, child), 31, 0);
}

/* Same as vc_bvRightShift only that the answer in 32 bits long */
Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child)
{
  return vc_bvExtract(vc, vc_bvRightShiftExpr(vc, sh_amt, child), 31, 0);
}

Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child)
{
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);
  int child_width = vc_getBVLength(vc, child);
  int shift_width = vc_getBVLength(vc, sh_amt);

  assert(child_width > 0);

  for (int count = 32; count >= 0; count--)
  {
    if (count != 32)
    {
      ifpart =
          vc_eqExpr(vc, sh_amt, vc_bvConstExprFromInt(vc, shift_width, count));
      thenpart = vc_bvExtract(vc, vc_bvLeftShiftExpr(vc, count, child),
                              child_width - 1, 0);

      ite = vc_iteExpr(vc, ifpart, thenpart, elsepart);
      elsepart = ite;
    }
    else
    {
      elsepart = vc_bvConstExprFromInt(vc, child_width, 0);
    }
  }
  return ite;
}

Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs)
{
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);

  for (int count = 32; count >= 0; count--)
  {
    if (count != 32)
    {
      ifpart = vc_eqExpr(vc, rhs, vc_bvConstExprFromInt(vc, 32, 1 << count));
      thenpart = vc_bvRightShiftExpr(vc, count, child);
      ite = vc_iteExpr(vc, ifpart, thenpart, elsepart);
      elsepart = ite;
    }
    else
    {
      elsepart = vc_bvConstExprFromInt(vc, 32, 0);
    }
  }
  return ite;
}

Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child)
{
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);

  int child_width = vc_getBVLength(vc, child);
  int shift_width = vc_getBVLength(vc, sh_amt);

  assert(child_width > 0);

  for (int count = 32; count >= 0; count--)
  {
    if (count != 32)
    {
      ifpart =
          vc_eqExpr(vc, sh_amt, vc_bvConstExprFromInt(vc, shift_width, count));
      thenpart = vc_bvRightShiftExpr(vc, count, child);
      ite = vc_iteExpr(vc, ifpart, thenpart, elsepart);
      elsepart = ite;
    }
    else
    {
      elsepart = vc_bvConstExprFromInt(vc, child_width, 0);
    }
  }
  return ite;
}

Expr vc_bvExtract(VC vc, Expr ccc, int hi_num, int low_num)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  BVTypeCheck(*a);

  stp::ASTNode hi = b->CreateBVConst(32, hi_num);
  stp::ASTNode low = b->CreateBVConst(32, low_num);
  stp::ASTNode o =
      b->CreateTerm(stp::BVEXTRACT, hi_num - low_num + 1, *a, hi, low);
  BVTypeCheck(o);
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvBoolExtract(VC vc, Expr ccc, int bit_num)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  BVTypeCheck(*a);

  stp::ASTNode bit = b->CreateBVConst(32, bit_num);
  // stp::ASTNode o = b->CreateNode(stp::BVGETBIT,*a,bit);
  stp::ASTNode zero = b->CreateBVConst(1, 0);
  stp::ASTNode oo = b->CreateTerm(stp::BVEXTRACT, 1, *a, bit, bit);
  stp::ASTNode o = b->CreateNode(stp::EQ, oo, zero);
  BVTypeCheck(o);
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvBoolExtract_Zero(VC vc, Expr ccc, int bit_num)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  BVTypeCheck(*a);

  stp::ASTNode bit = b->CreateBVConst(32, bit_num);
  // stp::ASTNode o = b->CreateNode(stp::BVGETBIT,*a,bit);
  stp::ASTNode zero = b->CreateBVConst(1, 0);
  stp::ASTNode oo = b->CreateTerm(stp::BVEXTRACT, 1, *a, bit, bit);
  stp::ASTNode o = b->CreateNode(stp::EQ, oo, zero);
  BVTypeCheck(o);
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvBoolExtract_One(VC vc, Expr ccc, int bit_num)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;
  BVTypeCheck(*a);

  stp::ASTNode bit = b->CreateBVConst(32, bit_num);
  // stp::ASTNode o = b->CreateNode(stp::BVGETBIT,*a,bit);
  stp::ASTNode one = b->CreateBVConst(1, 1);
  stp::ASTNode oo = b->CreateTerm(stp::BVEXTRACT, 1, *a, bit, bit);
  stp::ASTNode o = b->CreateNode(stp::EQ, oo, one);
  BVTypeCheck(o);
  stp::ASTNode* output = new stp::ASTNode(o);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvSignExtend(VC vc, Expr ccc, int nbits)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;

  // width of the expr which is being sign extended. nbits is the
  // resulting length of the signextended expr
  BVTypeCheck(*a);

  unsigned exprlen = a->GetValueWidth();
  unsigned outputlen = nbits;
  stp::ASTNode n;
  if (exprlen >= outputlen)
  {
    // extract
    stp::ASTNode hi = b->CreateBVConst(32, outputlen - 1);
    stp::ASTNode low = b->CreateBVConst(32, 0);
    n = b->CreateTerm(stp::BVEXTRACT, nbits, *a, hi, low);
    BVTypeCheck(n);
  }
  else
  {
    // sign extend
    stp::ASTNode width = b->CreateBVConst(32, nbits);
    n = b->CreateTerm(stp::BVSX, nbits, *a, width);
  }

  BVTypeCheck(n);
  stp::ASTNode* output = new stp::ASTNode(n);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvZeroExtend(VC vc, Expr ccc, int nbits)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* a = (stp::ASTNode*)ccc;

  // width of the expr which is being zero extended. nbits is the
  // resulting length of the zeroextended expr
  BVTypeCheck(*a);

  if (nbits <= 0)
    stp::FatalError("vc_bvZeroExtend: the new width must be positive");

  unsigned exprlen = a->GetValueWidth();
  unsigned outputlen = nbits;
  stp::ASTNode n;
  if (exprlen >= outputlen)
  {
    // extract
    stp::ASTNode hi = b->CreateBVConst(32, outputlen - 1);
    stp::ASTNode low = b->CreateBVConst(32, 0);
    n = b->CreateTerm(stp::BVEXTRACT, nbits, *a, hi, low);
  }
  else
  {
    // zero extend
    stp::ASTNode width = b->CreateBVConst(32, nbits);
    n = b->CreateTerm(stp::BVZX, nbits, *a, width);
  }

  BVTypeCheck(n);
  stp::ASTNode* output = new stp::ASTNode(n);
  // if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

//! Return an int from a constant bitvector expression
int getBVInt(Expr e)
{
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (stp::BVCONST != a->GetKind())
  {
    stp::FatalError("CInterface: getBVInt: Attempting to "
                    "extract int value from a NON-constant BITVECTOR: ",
                    *a);
  }
  return (int)a->GetUnsignedConst();
}

//! Return an unsigned int from a constant bitvector expression
unsigned int getBVUnsigned(Expr e)
{
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (stp::BVCONST != a->GetKind())
  {
    stp::FatalError("getBVUnsigned: Attempting to extract int "
                    "value from a NON-constant BITVECTOR: ",
                    *a);
  }
  return (unsigned int)a->GetUnsignedConst();
}

//! Return an unsigned long long int from a constant bitvector expression
unsigned long long int getBVUnsignedLongLong(Expr e)
{
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (stp::BVCONST != a->GetKind())
    stp::FatalError("getBVUnsigned: Attempting to extract int value"
                    "from a NON-constant BITVECTOR: ",
                    *a);
  unsigned* bv = a->GetBVConst();

  char* str_bv = (char*)CONSTANTBV::BitVector_to_Bin(bv);
  unsigned long long int tmp = std::strtoull(str_bv, NULL, 2);
  CONSTANTBV::BitVector_Dispose((unsigned char*)str_bv);
  return tmp;
}

void vc_printBVBitStringToBuffer(Expr e, char** buf, unsigned long* len)
{
  assert(buf);
  assert(len);

  // get the current value for the BV
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (stp::BVCONST != a->GetKind())
    stp::FatalError("vc_printBVToBuffer: Attempting to extract bit string"
                    "from a NON-constant BITVECTOR: ",
                    *a);
  unsigned* bv = a->GetBVConst();

  // Convert it to a bit string
  char* char_bv = (char*)CONSTANTBV::BitVector_to_Bin(bv);

  // Ensure our bit string is allocated string
  assert(char_bv);

  // Convert the char* to a c-style string
  string string_bv(char_bv);

  // Free the char* bit string
  CONSTANTBV::BitVector_Dispose((unsigned char*)char_bv);

  // convert to a c buffer
  const char* cstr = string_bv.c_str();
  unsigned long size = string_bv.size() + 1; // number of chars + terminating null
  *buf = (char*)malloc(size);
  if (!(*buf))
  {
    fprintf(stderr, "malloc(%lu) failed.", size);
    assert(*buf);
  }
  *len = size;
  memcpy(*buf, cstr, size);
}

Expr vc_simplify(VC vc, Expr e)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::Simplifier* simp = (stp::Simplifier*)(stp_i->simp);
  stp::ASTNode* a = (stp::ASTNode*)e;

  if (stp::BOOLEAN_TYPE == a->GetType())
  {
    stp::ASTNode* round1 =
        new stp::ASTNode(simp->SimplifyFormula_TopLevel(*a, false));
    stp::ASTNode* output =
        new stp::ASTNode(simp->SimplifyFormula_TopLevel(*round1, false));
    delete round1;
    return output;
  }
  else
  {
    stp::ASTNode* round1 = new stp::ASTNode(simp->SimplifyTerm(*a));
    stp::ASTNode* output = new stp::ASTNode(simp->SimplifyTerm(*round1));
    delete round1;
    return output;
  }
}

/* C pointer support: C interface to support C memory arrays in CVCL */
Expr vc_bvCreateMemoryArray(VC vc, const char* arrayName)
{
  Type bv8 = vc_bvType(vc, 8);
  Type bv32 = vc_bvType(vc, 32);

  Type malloced_mem0 = vc_arrayType(vc, bv32, bv8);
  return vc_varExpr(vc, arrayName, malloced_mem0);
}

Expr vc_bvReadMemoryArray(VC vc, Expr array, Expr byteIndex, int numOfBytes)
{
  if (!(numOfBytes > 0))
    stp::FatalError("numOfBytes must be greater than 0");

  if (numOfBytes == 1)
    return vc_readExpr(vc, array, byteIndex);
  else
  {
    int count = 1;
    Expr a = vc_readExpr(vc, array, byteIndex);
    while (--numOfBytes > 0)
    {
      Expr b = vc_readExpr(vc, array,
                           /*vc_simplify(vc, */
                           vc_bvPlusExpr(vc, 32, byteIndex,
                                         vc_bvConstExprFromInt(vc, 32, count)));
      a = vc_bvConcatExpr(vc, b, a);
      count++;
    }
    return a;
  }
}

Expr vc_bvWriteToMemoryArray(VC vc, Expr array, Expr byteIndex, Expr element,
                             int numOfBytes)
{
  if (!(numOfBytes > 0))
    stp::FatalError("numOfBytes must be greater than 0");

  if (numOfBytes == 1)
    return vc_writeExpr(vc, array, byteIndex, element);
  else
  {
    int count = 1;
    int low_elem = 0;
    int hi_elem = low_elem + 7;
    Expr c = vc_bvExtract(vc, element, hi_elem, low_elem);
    Expr newarray = vc_writeExpr(vc, array, byteIndex, c);
    while (--numOfBytes > 0)
    {
      low_elem = low_elem + 8;
      hi_elem = low_elem + 7;

      c = vc_bvExtract(vc, element, hi_elem, low_elem);
      newarray = vc_writeExpr(
          vc, newarray, vc_bvPlusExpr(vc, 32, byteIndex,
                                      vc_bvConstExprFromInt(vc, 32, count)),
          c);
      count++;
    }
    return newarray;
  }
}

Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value)
{
  return vc_bvConstExprFromInt(vc, 32, value);
}

#if 0
static char *val_to_binary_str(unsigned nbits, unsigned long long val) {
  char s[65];

  assert(nbits < sizeof s);
  strcpy(s, "");
  while(nbits-- > 0) {
    if((val >> nbits) & 1)
      strcat(s, "1");
    else
      strcat(s, "0");
  }
  return strdup(s);
}
#endif

Expr vc_parseExpr(VC vc, const char* infile)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  extern FILE *cvcin, *smtin;
  cvcin = fopen(infile, "r");
  if (cvcin == NULL)
  {
    fprintf(stderr, "STP: Error: cannot open %s\n", infile);
    stp::FatalError("Cannot open file");
    return 0;
  }

  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (0 != c)
  {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  stp::Cpp_interface cpp_inter(*b, b->defaultNodeFactory);
  stp::GlobalParserInterface = &cpp_inter;

  stp::ASTVec* AssertsQuery = new stp::ASTVec;
  if (b->UserFlags.smtlib1_parser_flag)
  {
    smtin = cvcin;
    cvcin = NULL;
    stp::GlobalSTP = stp_i;
    stp::GlobalParserBM = b;
    smtparse((void*)AssertsQuery);
    stp::GlobalSTP = NULL;
    stp::GlobalParserBM = NULL;
  }
  else
  {
    stp::GlobalSTP = stp_i;
    stp::GlobalParserBM = b;
    stp::GlobalParserInterface->letMgr->frameMode = false;
    cvcparse((void*)AssertsQuery);
    stp::GlobalSTP = NULL;
    stp::GlobalParserBM = NULL;
  }

  stp::ASTNode asserts = (*(stp::ASTVec*)AssertsQuery)[0];
  stp::ASTNode query = (*(stp::ASTVec*)AssertsQuery)[1];

  stp::ASTNode oo = b->CreateNode(stp::NOT, query);
  stp::ASTNode o = b->CreateNode(stp::AND, asserts, oo);
  stp::ASTNode* output = new stp::ASTNode(o);
  delete AssertsQuery;
  return output;
}

char* exprString(Expr e)
{
  stringstream ss;
  ((stp::ASTNode*)e)->PL_Print(ss, 0);
  string s = ss.str();
  char* copy = strdup(s.c_str());
  return copy;
}

char* typeString(Type t)
{
  stringstream ss;
  ((stp::ASTNode*)t)->PL_Print(ss, 0);

  string s = ss.str();
  char* copy = strdup(s.c_str());
  return copy;
}

Expr getChild(Expr e, int i)
{
  stp::ASTNode* a = (stp::ASTNode*)e;

  const stp::ASTChildren c = a->GetChildren();
  if (0 <= i && (unsigned)i < c.size())
  {
    stp::ASTNode o = c[i];
    stp::ASTNode* output = new stp::ASTNode(o);
    // if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return output;
  }
  else
  {
    stp::FatalError("getChild: Error accessing childNode "
                    "in expression: ",
                    *a);
  }
  return a;
}

void vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg))
{
  stp::vc_error_hdlr = error_hdlr;
}

int vc_getHashQueryStateToBuffer(VC vc, Expr query)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* qry = (stp::ASTNode*)query;
  assert(vc);
  assert(query);

  stp::ASTVec v = b->GetAsserts();
  stp::ASTNode out = b->CreateNode(stp::AND, b->CreateNode(stp::NOT, *qry), v);
  return out.Hash();
}

Type vc_getType(VC vc, Expr ex)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  stp::ASTNode* e = (stp::ASTNode*)ex;

  switch (e->GetType())
  {
    case stp::BOOLEAN_TYPE:
      return vc_boolType(vc);
      break;
    case stp::BITVECTOR_TYPE:
      // A rounding mode's carrier is a 5-bit bitvector; only a declared
      // RoundingMode symbol can be told apart from one.
      if (e->GetKind() == stp::SYMBOL && b->isRoundingModeSymbol(*e))
        return vc_fpRoundingModeType(vc);
      return vc_bvType(vc, e->GetValueWidth());
      break;
    case stp::FLOATINGPOINT_TYPE:
      return vc_fpType(vc, (int)e->GetExpWidth(), (int)e->GetSigWidth());
      break;
    case stp::ARRAY_TYPE:
    {
      // Rebuild the index and element types the array was declared with:
      // the element's float format is on the node, the rest comes from the
      // manager's array registries.
      unsigned int exp_width = 0;
      unsigned int sig_width = 0;

      Type typeindex;
      if (b->arrayHasFpIndex(*e, exp_width, sig_width))
        typeindex = vc_fpType(vc, (int)exp_width, (int)sig_width);
      else if (b->arrayHasRmIndex(*e))
        typeindex = vc_fpRoundingModeType(vc);
      else
        typeindex = vc_bvType(vc, e->GetIndexWidth());

      Type typedata;
      if (e->GetExpWidth() != 0)
        typedata = vc_fpType(vc, (int)e->GetExpWidth(), (int)e->GetSigWidth());
      else if (b->arrayHasRmElement(*e))
        typedata = vc_fpRoundingModeType(vc);
      else
        typedata = vc_bvType(vc, e->GetValueWidth());

      return vc_arrayType(vc, typeindex, typedata);
      break;
    }
    default:
      stp::FatalError("c_interface: vc_GetType: "
                      "expression with bad typing: "
                      "please check your expression construction");
      return vc_boolType(vc);
      break;
  }
}

//!if e is TRUE then return 1; if e is FALSE then return 0; otherwise
// return -1
int vc_isBool(Expr e)
{
  stp::ASTNode* input = (stp::ASTNode*)e;
  if (stp::TRUE == input->GetKind())
  {
    return 1;
  }

  if (stp::FALSE == input->GetKind())
  {
    return 0;
  }

  return -1;
}

void vc_Destroy(VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  if (b->UserFlags.cinterface_exprdelete_on_flag)
  {
    for (vector<stp::ASTNode*>::iterator it = b->persist.begin();
         it != b->persist.end(); it++)
      delete *it;
    b->persist.clear();
  }

  Cnf_ManFree();
  vc_clearDecls(vc);
  stp_i->deleteObjects();

  // Never leave the global aimed at a dead manager.
  if (stp::GlobalParserBM == b)
    stp::GlobalParserBM = NULL;

  delete stp_i;
  if (b->defaultNodeFactory != b->hashingNodeFactory)
    delete b->defaultNodeFactory;
  delete b;
}

void vc_DeleteExpr(Expr e)
{
  stp::ASTNode* input = (stp::ASTNode*)e;
  delete input;
}

// exprkind_t mirrors stp::Kind, which is generated from ASTKind.kinds, and
// getExprKind is a raw cast -- so the two enums must stay in numeric
// lockstep. These anchors catch a kind added to one side but not the other.
static_assert((int)UNDEFINED == (int)stp::UNDEFINED, "exprkind_t drift");
static_assert((int)BVCONST == (int)stp::BVCONST, "exprkind_t drift");
static_assert((int)FP_ABS == (int)stp::FP_ABS, "exprkind_t drift");
static_assert((int)FP_TO_IEEE_BV == (int)stp::FP_TO_IEEE_BV,
              "exprkind_t drift");
static_assert((int)FP_SMT_EQ == (int)stp::FP_SMT_EQ, "exprkind_t drift");
static_assert((int)BOOLEAN_TYPE == (int)stp::BOOLEAN_TYPE &&
                  (int)FLOATINGPOINT_TYPE == (int)stp::FLOATINGPOINT_TYPE &&
                  (int)UNKNOWN_TYPE == (int)stp::UNKNOWN_TYPE,
              "type_t drift");

exprkind_t getExprKind(Expr e)
{
  stp::ASTNode* input = (stp::ASTNode*)e;
  return (exprkind_t)(input->GetKind());
}

int getDegree(Expr e)
{
  stp::ASTNode* input = (stp::ASTNode*)e;
  return input->Degree();
}

int getBVLength(Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;

  if (stp::BITVECTOR_TYPE != e->GetType())
  {
    stp::FatalError("c_interface: vc_GetBVLength: "
                    "Input expression must be a bit-vector");
  }

  return e->GetValueWidth();
}

type_t getType(Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;
  return (type_t)(e->GetType());
}

int getVWidth(Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;
  return e->GetValueWidth();
}

int getIWidth(Expr ex)
{
  stp::ASTNode* e = (stp::ASTNode*)ex;
  return e->GetIndexWidth();
}

void vc_printCounterExampleFile(VC vc, int fd)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

  fdostream os(fd);
  stp::AbsRefine_CounterExample* ce =
      (stp::AbsRefine_CounterExample*)(stp_i->Ctr_Example);

  bool currentPrint = b->UserFlags.print_counterexample_flag;
  b->UserFlags.print_counterexample_flag = true;
  os << "COUNTEREXAMPLE BEGIN: \n";
  ce->PrintCounterExample(true, os);
  os << "COUNTEREXAMPLE END: \n";
  b->UserFlags.print_counterexample_flag = currentPrint;
}

const char* exprName(Expr e)
{
  return ((stp::ASTNode*)e)->GetName();
}

int getExprID(Expr ex)
{
  stp::ASTNode q = (*(stp::ASTNode*)ex);
  return q.GetNodeNum();
}

void process_argument(const char ch, VC vc)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* bm = stp_i->bm;

  switch (ch)
  {
    case 'a':
      bm->UserFlags.optimize_flag = false;
      break;
    case 'c':
      bm->UserFlags.construct_counterexample_flag = true;
      break;
    case 'd':
      bm->UserFlags.construct_counterexample_flag = true;
      bm->UserFlags.check_counterexample_flag = true;
      break;

    case 'h':
      assert(0 && "This API is dumb, don't use it!");
      exit(-1);
      break;
    case 'm':
      bm->UserFlags.smtlib1_parser_flag = true;
      if (bm->UserFlags.smtlib2_parser_flag)
        stp::FatalError("Can't use both the smtlib and smtlib2 parsers");
      break;
    case 'n':
      bm->UserFlags.print_output_flag = true;
      break;
    case 'p':
      bm->UserFlags.print_counterexample_flag = true;
      break;
    case 'q':
      bm->UserFlags.print_arrayval_declaredorder_flag = true;
      break;
    case 'r':
      bm->UserFlags.ackermannisation = true;
      break;
    case 's':
      bm->UserFlags.stats_flag = true;
      break;
    case 't':
      bm->UserFlags.quick_statistics_flag = true;
      break;
    case 'v':
      bm->UserFlags.print_nodes_flag = true;
      break;
    case 'w':
      bm->UserFlags.wordlevel_solve_flag = false;
      break;
    case 'x':
      // Decide whole-array equality/disequality (the extensional
      // theory of arrays) with the lemmas-on-demand procedure of
      // Brummayer & Biere. Array equalities are abstracted when the
      // AST is built, so this must be set before any term of the
      // query is created.
      bm->UserFlags.enable_array_equality = true;
      break;
    case 'y':
      bm->UserFlags.print_binary_flag = true;
      break;
    default:
      // fprintf(stderr,usage,prog);
      // cout << helpstring;
      assert(0 && "Unrecognised option");
      exit(-1);
      break;
  }
}

//////////////////////////////////////////////////////////////////////////
// extended version

int vc_parseMemExpr(VC vc, const char* s, Expr* oquery, Expr* oasserts)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;

#if 0
 stp::GlobalSTP = (stp::STP*)vc;
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if(0 != c) {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }
#endif

  stp::Cpp_interface pi(*b, b->defaultNodeFactory);
  stp::GlobalParserInterface = &pi;

  stp::ASTVec AssertsQuery;
  if (b->UserFlags.smtlib1_parser_flag)
  {
    // YY_BUFFER_STATE bstat = smt_scan_string(s);
    // smt_switch_to_buffer(bstat);
    stp::GlobalSTP = stp_i;
    stp::GlobalParserBM = b;
    stp::SMTScanString(s);
    smtparse((void*)&AssertsQuery);
    // smt_delete_buffer(bstat);
    stp::GlobalSTP = NULL;
    stp::GlobalParserBM = NULL;
  }
  else
  {
    // YY_BUFFER_STATE bstat = cvc_scan_string(s);
    // cvc_switch_to_buffer(bstat);
    stp::GlobalSTP = stp_i;
    stp::GlobalParserBM = b;
    stp::CVCScanString(s);
    cvcparse((void*)&AssertsQuery);
    // cvc_delete_buffer(bstat);
    stp::GlobalSTP = NULL;
    stp::GlobalParserBM = NULL;
  }

  if (oquery)
  {
    *(stp::ASTNode**)oquery = new stp::ASTNode(AssertsQuery[1]);
  }
  if (oasserts)
  {
    *(stp::ASTNode**)oasserts = new stp::ASTNode(AssertsQuery[0]);
  }
  return 1;
}

void _vc_useSolver(VC vc, stp::UserDefinedFlags::SATSolvers solver)
{
  /* Helper method to encapsulate setting a solver */
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  b->UserFlags.solver_to_use = solver;
}

bool _vc_isUsingSolver(VC vc, stp::UserDefinedFlags::SATSolvers solver)
{
  /* Helper method to encapsulate getting a solver */
  stp::STP* stp_i = (stp::STP*)vc;
  stp::STPMgr* b = stp_i->bm;
  return b->UserFlags.solver_to_use == solver;
}

bool vc_supportsMinisat(VC /*vc*/)
{
  return true;
}

bool vc_useMinisat(VC vc)
{
  _vc_useSolver(vc, stp::UserDefinedFlags::MINISAT_SOLVER);
  return true;
}

bool vc_isUsingMinisat(VC vc)
{
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::MINISAT_SOLVER);
}

bool vc_supportsSimplifyingMinisat(VC /*vc*/)
{
  return true;
}

bool vc_useSimplifyingMinisat(VC vc)
{
  _vc_useSolver(vc, stp::UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER);
  return true;
}

bool vc_isUsingSimplifyingMinisat(VC vc)
{
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER);
}

bool vc_supportsCryptominisat(VC /*vc*/)
{
#ifdef USE_CRYPTOMINISAT
  return true;
#else
  return false;
#endif
}

bool vc_useCryptominisat(VC
#ifdef USE_CRYPTOMINISAT
vc
#endif
)
{
#ifdef USE_CRYPTOMINISAT
  _vc_useSolver(vc, stp::UserDefinedFlags::CRYPTOMINISAT5_SOLVER);
  return true;
#else
  return false;
#endif
}

bool vc_isUsingCryptominisat(VC
#ifdef USE_CRYPTOMINISAT
vc
#endif
)
{
#ifdef USE_CRYPTOMINISAT
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::CRYPTOMINISAT5_SOLVER);
#else
  return false;
#endif
}

bool vc_supportsRiss(VC /*vc*/ )
{
#ifdef USE_RISS
  return true;
#else
  return false;
#endif
}

bool vc_useRiss(VC
#ifdef USE_RISS
vc
#endif
)
{
#ifdef USE_RISS
  _vc_useSolver(vc, stp::UserDefinedFlags::RISS_SOLVER);
  return true;
#else
  return false;
#endif
}

bool vc_isUsingRiss(VC
#ifdef USE_RISS
vc
#endif
)
{
#ifdef USE_RISS
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::RISS_SOLVER);
#else
  return false;
#endif
}

bool vc_supportsCadical(VC /*vc*/)
{
#ifdef USE_CADICAL
  return true;
#else
  return false;
#endif
}

bool vc_useCadical(VC
#ifdef USE_CADICAL
vc
#endif
)
{
#ifdef USE_CADICAL
  _vc_useSolver(vc, stp::UserDefinedFlags::CADICAL_SOLVER);
  return true;
#else
  return false;
#endif
}

bool vc_isUsingCadical(VC
#ifdef USE_CADICAL
vc
#endif
)
{
#ifdef USE_CADICAL
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::CADICAL_SOLVER);
#else
  return false;
#endif
}

