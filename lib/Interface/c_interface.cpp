/********************************************************************
 * AUTHORS: Vijay Ganesh, Andrew V. Jones
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
#include <cstdio>
#include <cstdlib>

#include "stp/Interface/fdstream.h"
#include "stp/Parser/parser.h"
#include "stp/Printer/printers.h"
#include "stp/cpp_interface.h"
#include "stp/Util/GitSHA1.h"
// FIXME: External library
#include "extlib-abc/cnf_short.h"

using std::cout;
using std::ostream;
using std::stringstream;
using std::string;
using std::fdostream;
using std::endl;

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
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if (0 != c)
  {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  stp::STPMgr* bm = new stp::STPMgr();

  bm->defaultNodeFactory =
      new SimplifyingNodeFactory(*(bm->hashingNodeFactory), *bm);

  stp::Simplifier* simp = new stp::Simplifier(bm);
  stp::BVSolver* bvsolver = new stp::BVSolver(bm, simp);
  stp::ToSAT* tosat = new stp::ToSAT(bm);
  stp::ArrayTransformer* arrayTransformer = new stp::ArrayTransformer(bm, simp);
  stp::AbsRefine_CounterExample* Ctr_Example =
      new stp::AbsRefine_CounterExample(bm, simp, arrayTransformer);

  stp::STP* stpObj =
      new stp::STP(bm, simp, bvsolver, arrayTransformer, tosat, Ctr_Example);

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
  stp::Simplifier* simp = new stp::Simplifier(b);
  for (stp::ASTVec::iterator i = v.begin(), iend = v.end(); i != iend; i++)
  {
    stp::ASTNode q =
        (simplify_print == 1) ? simp->SimplifyFormula_TopLevel(*i, false) : *i;
    q = (simplify_print == 1) ? simp->SimplifyFormula_TopLevel(q, false) : q;
    os << "ASSERT( ";
    q.PL_Print(os, b);
    os << ");" << endl;
  }
  delete simp;
  simp = NULL;
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

  stp::Simplifier* simp = new stp::Simplifier(b);

  // formate the state of the query
  stringstream os;
  vc_printVarDeclsToStream(vc, os);
  os << "%----------------------------------------------------" << endl;
  vc_printAssertsToStream(vc, os, simplify_print);
  os << "%----------------------------------------------------" << endl;
  os << "QUERY( ";
  stp::ASTNode q =
      (simplify_print == 1)
          ? simp->SimplifyFormula_TopLevel(*((stp::ASTNode*)e), false)
          : *(stp::ASTNode*)e;
  q.PL_Print(os, b);
  os << " );" << endl;

  delete simp;
  simp = NULL;

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

  if (!(ti->GetKind() == stp::BITVECTOR && (*ti)[0].GetKind() == stp::BVCONST))
  {
    stp::FatalError("Tyring to build array whose"
                    "indextype i is not a BITVECTOR, where i = ",
                    *ti);
  }
  if (!(td->GetKind() == stp::BITVECTOR && (*td)[0].GetKind() == stp::BVCONST))
  {
    stp::FatalError("Trying to build an array whose"
                    "valuetype v is not a BITVECTOR. where a = ",
                    *td);
  }
  stp::ASTNode output = b->CreateNode(stp::ARRAY, (*ti)[0], (*td)[0]);

  return persistNode(vc, output);
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
  return vc_query_with_timeout(vc, e, -1);
}

int vc_query_with_timeout(VC vc, Expr e, int timeout_ms)
{
  stp::STP* stp_i = (stp::STP*)vc;
  stp::ASTNode* a = (stp::ASTNode*)e;
  stp::STPMgr* b = stp_i->bm;

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
  stp_i->bm->UserFlags.timeout_max_conflicts = timeout_ms;
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
  stp::ASTNode* a = (stp::ASTNode*)type;

  unsigned indexWidth;
  unsigned valueWidth;

  switch (a->GetKind())
  {
    case stp::BITVECTOR:
      indexWidth = 0;
      valueWidth = (*a)[0].GetUnsignedConst();
      break;
    case stp::ARRAY:
      indexWidth = (*a)[0].GetUnsignedConst();
      valueWidth = (*a)[1].GetUnsignedConst();
      break;
    case stp::BOOLEAN:
      indexWidth = 0;
      valueWidth = 0;
      break;
    default:
      stp::FatalError("CInterface: vc_varExpr: Unsupported type", *a);
      assert(false);
      exit(-1);
      break;
  }
  stp::ASTNode o = b->CreateSymbol(name, indexWidth, valueWidth);

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
  stp::ASTNode o = b->CreateNode(stp::EQ, *a, *aa);

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
  unsigned long long int max_n_bits = 0xFFFFFFFFFFFFFFFFULL >> (64 - n_bits);
  // printf("%ull", max_n_bits);
  if (v > max_n_bits)
  {
    printf("CInterface: vc_bvConstExprFromInt: "
           "Cannot construct a constant %llu >= %llu,\n",
           v, max_n_bits);
    stp::FatalError("FatalError");
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

  int newBitsPerElem = numOfBytes * 8;
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

  stp::ASTVec c = a->GetChildren();
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
  stp::ASTNode* e = (stp::ASTNode*)ex;

  switch (e->GetType())
  {
    case stp::BOOLEAN_TYPE:
      return vc_boolType(vc);
      break;
    case stp::BITVECTOR_TYPE:
      return vc_bvType(vc, e->GetValueWidth());
      break;
    case stp::ARRAY_TYPE:
    {
      Type typeindex = vc_bvType(vc, e->GetIndexWidth());
      Type typedata = vc_bvType(vc, e->GetValueWidth());
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

  Cnf_ClearMemory();
  vc_clearDecls(vc);
  stp_i->deleteObjects();

  delete stp_i;
  delete b->defaultNodeFactory;
  delete b;
}

void vc_DeleteExpr(Expr e)
{
  stp::ASTNode* input = (stp::ASTNode*)e;
  delete input;
}

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

bool vc_supportsMinisat(VC vc)
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

bool vc_supportsSimplifyingMinisat(VC vc )
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

bool vc_supportsCryptominisat(VC vc )
{
#ifdef USE_CRYPTOMINISAT
  return true;
#else
  return false;
#endif
}

bool vc_useCryptominisat(VC vc
#ifndef USE_CRYPTOMINISAT

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

bool vc_isUsingCryptominisat(VC vc
#ifndef USE_CRYPTOMINISAT

#endif
)
{
#ifdef USE_CRYPTOMINISAT
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::CRYPTOMINISAT5_SOLVER);
#else
  return false;
#endif
}

bool vc_supportsRiss(VC vc )
{
#ifdef USE_RISS
  return true;
#else
  return false;
#endif
}

bool vc_useRiss(VC vc
#ifndef USE_RISS

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

bool vc_isUsingRiss(VC vc
#ifndef USE_RISS

#endif
)
{
#ifdef USE_RISS
  return _vc_isUsingSolver(vc, stp::UserDefinedFlags::RISS_SOLVER);
#else
  return false;
#endif
}

