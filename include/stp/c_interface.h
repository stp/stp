/********************************************************************
 * AUTHORS: Michael Katelman, Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: Apr, 2008
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

#ifndef _cvcl__include__c_interface_h_
#define _cvcl__include__c_interface_h_

#ifdef __cplusplus
#define _CVCL_DEFAULT_ARG(v) = v
#else
#define _CVCL_DEFAULT_ARG(v)
#endif

#include "stp/stp_export.h"

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>

#ifdef STP_STRONG_TYPING
#else
// This gives absolutely no pointer typing at compile-time. Most C
// users prefer this over stronger typing. User is the king. A
// stronger typed interface is in the works.
typedef void* VC;
typedef void* Expr;
typedef void* Type;
typedef void* WholeCounterExample;
#endif

// o  : optimizations
// c  : check counterexample
// p  : print counterexample
// h  : help
// s  : stats
// v  : print nodes

// The "num_absrefine" argument isn't used at all. It's left for compatibility
// with existing code.
// TODO remove these two functions, it's an ugly way of controlling settings
LIBSTP_EXPORT void vc_setFlags(VC vc, char c, int num_absrefine _CVCL_DEFAULT_ARG(0));
LIBSTP_EXPORT void vc_setFlag(VC vc, char c);

//! Interface-only flags.
enum ifaceflag_t
{
  /*! EXPRDELETE: boolean, default true. For objects created by
    vc_arrayType, vc_boolType, vc_bvType, vc_bv32Type, vc_bvConstExprFromInt, if
    this flag is set both at the time the objects are created and at
    the time that vc_Destroy is called, vc_Destroy will automatically
    delete them. */
  EXPRDELETE,
  MS,
  SMS,
  CMS4,
  MSP

};
LIBSTP_EXPORT void vc_setInterfaceFlags(VC vc, enum ifaceflag_t f, int param_value);

// defines division by zero to equal 1, x%0 to equal x.
// avoids division by zero errors.
LIBSTP_EXPORT void make_division_total(VC vc);

//! Flags can be NULL
LIBSTP_EXPORT VC vc_createValidityChecker(void);

// Basic types
LIBSTP_EXPORT Type vc_boolType(VC vc);

//! Create an array type
LIBSTP_EXPORT Type vc_arrayType(VC vc, Type typeIndex, Type typeData);

/////////////////////////////////////////////////////////////////////////////
// Expr manipulation methods                                               //
/////////////////////////////////////////////////////////////////////////////

//! Create a variable with a given name and type
/*! The type cannot be a function type. The var name can contain
  only variables, numerals and underscore. If you use any other
  symbol, you will get a segfault. */
LIBSTP_EXPORT Expr vc_varExpr(VC vc, const char* name, Type type);

// The var name can contain only variables, numerals and
// underscore. If you use any other symbol, you will get a segfault.
LIBSTP_EXPORT Expr vc_varExpr1(VC vc, const char* name, int indexwidth, int valuewidth);

//! Get the expression and type associated with a name.
/*!  If there is no such Expr, a NULL Expr is returned. */
// Expr vc_lookupVar(VC vc, char* name, Type* type);

//! Get the type of the Expr.
LIBSTP_EXPORT Type vc_getType(VC vc, Expr e);

LIBSTP_EXPORT int vc_getBVLength(VC vc, Expr e);

//! Create an equality expression.  The two children must have the same type.
LIBSTP_EXPORT Expr vc_eqExpr(VC vc, Expr child0, Expr child1);

// Boolean expressions

// The following functions create Boolean expressions.  The children
// provided as arguments must be of type Boolean (except for the
// function vc_iteExpr(). In the case of vc_iteExpr() the
// conditional must always be Boolean, but the ifthenpart
// (resp. elsepart) can be bit-vector or Boolean type. But, the
// ifthenpart and elsepart must be both of the same type)
LIBSTP_EXPORT Expr vc_trueExpr(VC vc);
LIBSTP_EXPORT Expr vc_falseExpr(VC vc);
LIBSTP_EXPORT Expr vc_notExpr(VC vc, Expr child);
LIBSTP_EXPORT Expr vc_andExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_andExprN(VC vc, Expr* children, int numOfChildNodes);
LIBSTP_EXPORT Expr vc_orExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_xorExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_orExprN(VC vc, Expr* children, int numOfChildNodes);
LIBSTP_EXPORT Expr vc_impliesExpr(VC vc, Expr hyp, Expr conc);
LIBSTP_EXPORT Expr vc_iffExpr(VC vc, Expr left, Expr right);
// The output type of vc_iteExpr can be Boolean (formula-level ite)
// or bit-vector (word-level ite)
LIBSTP_EXPORT Expr vc_iteExpr(VC vc, Expr conditional, Expr ifthenpart, Expr elsepart);

// Boolean to single bit BV Expression
LIBSTP_EXPORT Expr vc_boolToBVExpr(VC vc, Expr form);

// Parameterized Boolean Expression (PARAMBOOL, Boolean_Var, parameter)
LIBSTP_EXPORT Expr vc_paramBoolExpr(VC vc, Expr var, Expr param);

// Arrays

//! Create an expression for the value of array at the given index
LIBSTP_EXPORT Expr vc_readExpr(VC vc, Expr array, Expr index);

//! Array update; equivalent to "array WITH [index] := newValue"
LIBSTP_EXPORT Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue);

// Expr I/O: Parses directly from file in the c_interface. pretty cool!!
LIBSTP_EXPORT Expr vc_parseExpr(VC vc, const char* s);

//! Prints 'e' to stdout.
LIBSTP_EXPORT void vc_printExpr(VC vc, Expr e);

//! Prints 'e' to stdout as C code
LIBSTP_EXPORT void vc_printExprCCode(VC vc, Expr e);

//! print in smtlib format
LIBSTP_EXPORT char* vc_printSMTLIB(VC vc, Expr e);

//! Prints 'e' into an open file descriptor 'fd'
LIBSTP_EXPORT void vc_printExprFile(VC vc, Expr e, int fd);

//! Prints state of 'vc' into malloc'd buffer '*buf' and stores the
//  length into '*len'.  It is the responsibility of the caller to
//  free the buffer.
// void vc_printStateToBuffer(VC vc, char **buf, unsigned long *len);

//! Prints 'e' to malloc'd buffer '*buf'.  Sets '*len' to the length of
//  the buffer. It is the responsibility of the caller to free the buffer.
LIBSTP_EXPORT void vc_printExprToBuffer(VC vc, Expr e, char** buf, unsigned long* len);

//! Prints counterexample to stdout.
LIBSTP_EXPORT void vc_printCounterExample(VC vc);

//! Prints variable declarations to stdout.
LIBSTP_EXPORT void vc_printVarDecls(VC vc);

//! Clear the internal list of variables to declare maintained for
//  vc_printVarDecls. Do this after you've printed them, or if you
//  never want to print them, to prevent a memory leak.
LIBSTP_EXPORT void vc_clearDecls(VC vc);

//! Prints asserts to stdout. The flag simplify_print must be set to
//"1" if you wish simplification to occur dring printing. It must be
// set to "0" otherwise
LIBSTP_EXPORT void vc_printAsserts(VC vc, int simplify_print _CVCL_DEFAULT_ARG(0));

//! Prints the state of the query to malloc'd buffer '*buf' and
// stores ! the length of the buffer to '*len'.  It is the
// responsibility of the caller to free the buffer. The flag
// simplify_print must be set to "1" if you wish simplification to
// occur dring printing. It must be set to "0" otherwise
LIBSTP_EXPORT void vc_printQueryStateToBuffer(VC vc, Expr e, char** buf, unsigned long* len,
                                int simplify_print);

//! Similar to vc_printQueryStateToBuffer()
LIBSTP_EXPORT void vc_printCounterExampleToBuffer(VC vc, char** buf, unsigned long* len);

//! Prints query to stdout.
LIBSTP_EXPORT void vc_printQuery(VC vc);

/////////////////////////////////////////////////////////////////////////////
// Context-related methods                                                 //
/////////////////////////////////////////////////////////////////////////////

//! Assert a new formula in the current context.
/*! The formula must have Boolean type. */
LIBSTP_EXPORT void vc_assertFormula(VC vc, Expr e);

//! Simplify e with respect to the current context
LIBSTP_EXPORT Expr vc_simplify(VC vc, Expr e);

//! Check validity of e in the current context. e must be a FORMULA
// returns 0 -> the input is INVALID
// returns 1 -> the input is VALID
// returns 2 -> then ERROR
// returns 3 -> then TIMEOUT

// NB. The timeout is a soft timeout, use the -g flag for a hard timeout that
// will abort automatically. The soft timeout is checked sometimes in the code,
// and if the time has passed, then "timeout" will be returned. It's only
// checked
// sometimes though, so the actual timeout may be larger. Cryptominisat doesn't
// check
// the timeout yet..

// The C-language doesn't allow default arguments, so to get it compiling, I've
// split it into two functions.
LIBSTP_EXPORT int vc_query_with_timeout(VC vc, Expr e, int timeout_ms);
LIBSTP_EXPORT int vc_query(VC vc, Expr e);

//! Return the counterexample after a failed query.
LIBSTP_EXPORT Expr vc_getCounterExample(VC vc, Expr e);

//! Return an array from a counterexample after a failed query.
LIBSTP_EXPORT void vc_getCounterExampleArray(VC vc, Expr e, Expr** indices, Expr** values,
                               int* size);

//! get size of counterexample, i.e. the number of variables/array
// locations in the counterexample.
LIBSTP_EXPORT int vc_counterexample_size(VC vc);

//! Checkpoint the current context and increase the scope level
LIBSTP_EXPORT void vc_push(VC vc);

//! Restore the current context to its state at the last checkpoint
LIBSTP_EXPORT void vc_pop(VC vc);

//! Return an int from a constant bitvector expression
LIBSTP_EXPORT int getBVInt(Expr e);
//! Return an unsigned int from a constant bitvector expression
LIBSTP_EXPORT unsigned int getBVUnsigned(Expr e);
//! Return an unsigned long long int from a constant bitvector expressions
LIBSTP_EXPORT unsigned long long int getBVUnsignedLongLong(Expr e);

/**************************/
/* BIT VECTOR OPERATIONS  */
/**************************/
LIBSTP_EXPORT Type vc_bvType(VC vc, int no_bits);
LIBSTP_EXPORT Type vc_bv32Type(VC vc);

//Const expressions for string, int, long-long, etc
LIBSTP_EXPORT Expr vc_bvConstExprFromDecStr(VC vc, int width, const char* decimalInput);
LIBSTP_EXPORT Expr vc_bvConstExprFromStr(VC vc, const char* binary_repr);
LIBSTP_EXPORT Expr vc_bvConstExprFromInt(VC vc, int n_bits, unsigned int value);
LIBSTP_EXPORT Expr vc_bvConstExprFromLL(VC vc, int n_bits, unsigned long long value);
LIBSTP_EXPORT Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value);

LIBSTP_EXPORT Expr vc_bvConcatExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvPlusExpr(VC vc, int n_bits, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvPlusExprN(VC vc, int n_bits, Expr* children, int numOfChildNodes);
LIBSTP_EXPORT Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvMinusExpr(VC vc, int n_bits, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvMultExpr(VC vc, int n_bits, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bv32MultExpr(VC vc, Expr left, Expr right);
// left divided by right i.e. left/right
LIBSTP_EXPORT Expr vc_bvDivExpr(VC vc, int n_bits, Expr left, Expr right);
// left modulo right i.e. left%right
LIBSTP_EXPORT Expr vc_bvModExpr(VC vc, int n_bits, Expr left, Expr right);
// signed left divided by right i.e. left/right
LIBSTP_EXPORT Expr vc_sbvDivExpr(VC vc, int n_bits, Expr left, Expr right);
// signed left modulo right i.e. left%right
LIBSTP_EXPORT Expr vc_sbvModExpr(VC vc, int n_bits, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_sbvRemExpr(VC vc, int n_bits, Expr left, Expr right);

LIBSTP_EXPORT Expr vc_bvLtExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvLeExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvGtExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvGeExpr(VC vc, Expr left, Expr right);

LIBSTP_EXPORT Expr vc_sbvLtExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_sbvLeExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_sbvGtExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_sbvGeExpr(VC vc, Expr left, Expr right);

LIBSTP_EXPORT Expr vc_bvUMinusExpr(VC vc, Expr child);

// bitwise operations: these are terms not formulas
LIBSTP_EXPORT Expr vc_bvAndExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvOrExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvXorExpr(VC vc, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvNotExpr(VC vc, Expr child);

// Shift an expression by another expression. This is newstyle.
LIBSTP_EXPORT Expr vc_bvLeftShiftExprExpr(VC vc, int n_bits, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvRightShiftExprExpr(VC vc, int n_bits, Expr left, Expr right);
LIBSTP_EXPORT Expr vc_bvSignedRightShiftExprExpr(VC vc, int n_bits, Expr left, Expr right);

// These shifts are old-style. Kept for compatability---oldstyle.
LIBSTP_EXPORT Expr vc_bvLeftShiftExpr(VC vc, int sh_amt, Expr child);
LIBSTP_EXPORT Expr vc_bvRightShiftExpr(VC vc, int sh_amt, Expr child);
/* Same as vc_bvLeftShift only that the answer in 32 bits long */
LIBSTP_EXPORT Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child);
/* Same as vc_bvRightShift only that the answer in 32 bits long */
LIBSTP_EXPORT Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child);
LIBSTP_EXPORT Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child);
LIBSTP_EXPORT Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child);
LIBSTP_EXPORT Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs);

LIBSTP_EXPORT Expr vc_bvExtract(VC vc, Expr child, int high_bit_no, int low_bit_no);

// accepts a bitvector and position, and returns a boolean
// corresponding to that position. More precisely, it return the
// equation (x[bit_no:bit_no] == 0)
LIBSTP_EXPORT Expr vc_bvBoolExtract(VC vc, Expr x, int bit_no);
LIBSTP_EXPORT Expr vc_bvBoolExtract_Zero(VC vc, Expr x, int bit_no);

// accepts a bitvector and position, and returns a boolean
// corresponding to that position. More precisely, it return the
// equation (x[bit_no:bit_no] == 1)
LIBSTP_EXPORT Expr vc_bvBoolExtract_One(VC vc, Expr x, int bit_no);
LIBSTP_EXPORT Expr vc_bvSignExtend(VC vc, Expr child, int nbits);

/*C pointer support:  C interface to support C memory arrays in CVCL */
LIBSTP_EXPORT Expr vc_bvCreateMemoryArray(VC vc, const char* arrayName);
LIBSTP_EXPORT Expr vc_bvReadMemoryArray(VC vc, Expr array, Expr byteIndex, int numOfBytes);
LIBSTP_EXPORT Expr vc_bvWriteToMemoryArray(VC vc, Expr array, Expr byteIndex, Expr element,
                             int numOfBytes);
LIBSTP_EXPORT Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value);

// return a string representation of the Expr e. The caller is responsible
// for deallocating the string with free()
LIBSTP_EXPORT char* exprString(Expr e);

// return a string representation of the Type t. The caller is responsible
// for deallocating the string with free()
LIBSTP_EXPORT char* typeString(Type t);

LIBSTP_EXPORT Expr getChild(Expr e, int i);

// 1.if input expr is TRUE then the function returns 1;
//
// 2.if input expr is FALSE then function returns 0;
//
// 3.otherwise the function returns -1
LIBSTP_EXPORT int vc_isBool(Expr e);

/* Register the given error handler to be called for each fatal error.*/
LIBSTP_EXPORT void vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg));

LIBSTP_EXPORT int vc_getHashQueryStateToBuffer(VC vc, Expr query);

// destroys the STP instance, and removes all the created expressions
LIBSTP_EXPORT void vc_Destroy(VC vc);

// deletes the expression e
LIBSTP_EXPORT void vc_DeleteExpr(Expr e);

// Get the whole counterexample from the current context
LIBSTP_EXPORT WholeCounterExample vc_getWholeCounterExample(VC vc);

// Get the value of a term expression from the CounterExample
LIBSTP_EXPORT Expr vc_getTermFromCounterExample(VC vc, Expr e, WholeCounterExample c);

// Free the return value of vc_getWholeCounterExample
LIBSTP_EXPORT void vc_deleteWholeCounterExample(WholeCounterExample cc);

// Kinds of Expr
enum exprkind_t
{
  UNDEFINED,
  SYMBOL,
  BVCONST,
  BVNEG,
  BVCONCAT,
  BVOR,
  BVAND,
  BVXOR,
  BVNAND,
  BVNOR,
  BVXNOR,
  BVEXTRACT,
  BVLEFTSHIFT,
  BVRIGHTSHIFT,
  BVSRSHIFT,
  BVVARSHIFT,
  BVPLUS,
  BVSUB,
  BVUMINUS,
  BVMULTINVERSE,
  BVMULT,
  BVDIV,
  BVMOD,
  SBVDIV,
  SBVREM,
  SBVMOD,
  BVSX,
  BVZX,
  ITE,
  BOOLEXTRACT,
  BVLT,
  BVLE,
  BVGT,
  BVGE,
  BVSLT,
  BVSLE,
  BVSGT,
  BVSGE,
  EQ,
  FALSE,
  TRUE,
  NOT,
  AND,
  OR,
  NAND,
  NOR,
  XOR,
  IFF,
  IMPLIES,
  PARAMBOOL,
  READ,
  WRITE,
  ARRAY,
  BITVECTOR,
  BOOLEAN
};

// type of expression
enum type_t
{
  BOOLEAN_TYPE = 0,
  BITVECTOR_TYPE,
  ARRAY_TYPE,
  UNKNOWN_TYPE
};

// get the kind of the expression
LIBSTP_EXPORT enum exprkind_t getExprKind(Expr e);

// get the number of children nodes
LIBSTP_EXPORT int getDegree(Expr e);

// get the bv length
LIBSTP_EXPORT int getBVLength(Expr e);

// get expression type
LIBSTP_EXPORT enum type_t getType(Expr e);

// get value bit width
LIBSTP_EXPORT int getVWidth(Expr e);

// get index bit width
LIBSTP_EXPORT int getIWidth(Expr e);

// Prints counterexample to an open file descriptor 'fd'
LIBSTP_EXPORT void vc_printCounterExampleFile(VC vc, int fd);

// get name of expression. must be a variable.
LIBSTP_EXPORT const char* exprName(Expr e);

// get the node ID of an Expr.
LIBSTP_EXPORT int getExprID(Expr ex);

// parse the expr from memory string!
LIBSTP_EXPORT int vc_parseMemExpr(VC vc, const char* s, Expr* oquery, Expr* oasserts);
#ifdef __cplusplus
}
#endif

#undef _CVCL_DEFAULT_ARG

#endif
