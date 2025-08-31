/********************************************************************
 * AUTHORS: Michael Katelman, Vijay Ganesh, Trevor Hansen, Andrew V. Jones
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

#ifdef __cplusplus
extern "C" {
#endif

#include <stdbool.h>

/////////////////////////////////////////////////////////////////////////////
/// STP API INTERNAL MACROS FOR LINKING
///
/// These are undefined at the end of this file to prevent them from leaking
/// into code that includes it.
/////////////////////////////////////////////////////////////////////////////

#if defined(_MSC_VER)
// NOTE: for now, we need STP_SHARED_LIB for clients of the statically linked
// STP library, for which linking fails when DLL_PUBLIC is __declspec(dllimport).
#if defined(STP_SHARED_LIB) && defined(STP_EXPORTS)
// This is visible when building the STP library as a DLL.
#define DLL_PUBLIC __declspec(dllexport)
#elif defined(STP_SHARED_LIB)
// This is visible for STP clients.
#define DLL_PUBLIC __declspec(dllimport)
#else
#define DLL_PUBLIC
#endif

// Symbols are hidden by default in MSVC.
#define DLL_LOCAL

#elif defined(__GNUC__) || defined(__clang__)
#define DLL_PUBLIC __attribute__((visibility("default")))
#define DLL_LOCAL __attribute__((visibility("hidden")))
#else
#define DLL_PUBLIC
#define DLL_LOCAL
#endif

/////////////////////////////////////////////////////////////////////////////
/// STP API Types
///
/// This gives absolutely no pointer typing at compile-time. Most C
/// users prefer this over stronger typing. User is the king. A
/// stronger typed interface is in the works.
/////////////////////////////////////////////////////////////////////////////

#ifdef STP_STRONG_TYPING // not used for now!
#else
typedef void* VC;
typedef void* Expr;
typedef void* Type;
typedef void* WholeCounterExample;
#endif

/////////////////////////////////////////////////////////////////////////////
/// START API
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns the C string for the git sha of STP
//!
DLL_PUBLIC const char* get_git_version_sha(void);

//! \brief Returns the C string for the git tag of STP
//!
DLL_PUBLIC const char* get_git_version_tag(void);

//! \brief Returns the C string for the compilation env of STP
//!
DLL_PUBLIC const char* get_compilation_env(void);

//! \brief Processes the given flag represented as char for the given validity checker.
//!
//! The following flags are supported:
//!  - 'a': Disables optimization. TODO: What kind of optimization is meant here?
//!  - 'c': Enables construction of counter examples.
//!  - 'd': Enables construction and checking of counter examples. Superseeds flag 'c'.
//!  - 'm': Use SMTLib1 parser. Conflicts with using SMTLib2 parser.
//!  - 'n': Enables printing of the output. TODO: What is meant with output here?
//!  - 'p': Enables printing of counter examples.
//!  - 'q': Enables printing of array values in declared order.
//!  - 'r': Enables accermannisation.
//!  - 's': Sets the status flag to true. TODO: What consequenses does this have?
//!  - 't': Enables quick statistics. TODO: What is this?
//!  - 'v': Enables printing of nodes.
//!  - 'w': Enables word-level solving. TODO: What is mean with this?
//!  - 'y': Enables printing binaries. TODO: What is meant with this?
//!
//! This function panics if given an unsupported or unknown flag.
//!
DLL_PUBLIC void process_argument(const char ch, VC bm);

//! \brief Deprecated: use process_argument instead!
//!
//! Sets flags for the validity checker.
//! For more information about this look into the documentation of process_argument.
//!
//! Parameter num_absrefine has no effect in the current implementation.
//! It is left for compatibility with existing code.
//!
DLL_PUBLIC void vc_setFlags(VC vc, char c,
                            int num_absrefine _CVCL_DEFAULT_ARG(0));

//! \brief Deprecated: use process_argument instead!
//!
//! Sets flags for the validity checker.
//! For more information about this look into the documentation of process_argument.
//!
DLL_PUBLIC void vc_setFlag(VC vc, char c);

//! Interface-only flags.
//!
enum ifaceflag_t
{
  //! Tells the validity checker that it is responsible for resource
  //! deallocation of its allocated expressions.
  //!
  //! This is set to true by default.
  //!
  //! Affected methods are:
  //!  - vc_arrayType
  //!  - vc_boolType
  //!  - vc_bvType
  //!  - vc_bv32Type
  //!  - vc_vcConstExprFromInt
  //!
  //! Changing this flag while STP is running may result in undefined behaviour.
  //!
  //! Use this with great care; otherwise memory leaks are very easily possible!
  //!
  EXPRDELETE,

  //! Use the minisat SAT solver.
  //!
  MS,

  //! Use a simplifying version of the minisat SAT solver.
  //!
  SMS,

  //! Use the crypto minisat version 4 or higher (currently version 5) solver.
  //!
  CMS4,

  //! Use the SAT solver Riss.
  //!
  RISS,

  //! Use the SAT solver Kissat.
  //!
  KISSAT,

  //! \brief Deprecated: use `MS` instead!
  //!
  //! This used to be the array version of the minisat SAT solver.
  //!
  //! Currently simply forwards to MS.
  //!
  MSP

};

//! \brief Sets the given interface flag for the given validity checker to param_value.
//!
//! Use this to set the underlying SAT solver used by STP or to change
//! the global behaviour for expression ownership semantics via EXPRDELETE.
//!
DLL_PUBLIC void vc_setInterfaceFlags(VC vc, enum ifaceflag_t f,
                                     int param_value);

//! \brief Deprecated: this functionality is no longer needed!
//!
//! Since recent versions of STP division is always total.
DLL_PUBLIC void make_division_total(VC vc);

//! \brief Creates a new instance of an STP validity checker.
//!
//! Validity checker is the context for all STP resources like expressions,
//! type and counter examples that may be generated while running STP.
//!
//! It is also the interface for assertions and queries.
//!
DLL_PUBLIC VC vc_createValidityChecker(void);

//! \brief Returns the boolean type for the given validity checker.
//!
DLL_PUBLIC Type vc_boolType(VC vc);

//! \brief Returns an array type with the given index type and data type
//!        for the given validity checker.
//!
//! Note that index type and data type must both be of bitvector (bv) type.
//!
DLL_PUBLIC Type vc_arrayType(VC vc, Type typeIndex, Type typeData);

/////////////////////////////////////////////////////////////////////////////
/// EXPR MANUPULATION METHODS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns a variable (symbol) expression with the given name and type.
//!
//! The type cannot be a function type. (TODO: Are function type still a thing in STP?)
//!
//! The variable name must only consist of alphanumerics and underscore
//! characters, otherwise this may behave in undefined ways, e.g. segfault.
//!
DLL_PUBLIC Expr vc_varExpr(VC vc, const char* name, Type type);

//! \brief Similar to vc_varExpr but more bare metal. Do not use this unless
//!        you really know what you are doing!
//!
//! Note: This should be deprecated in favor of the saner vc_varExpr API
//! and as this API leaks implementation details of STP.
//!
//! The variable name must only consist of alphanumerics and underscore
//! characters, otherwise this may behave in undefined ways, e.g. segfault.
//!
DLL_PUBLIC Expr vc_varExpr1(VC vc, const char* name, int indexwidth,
                            int valuewidth);

//! \brief Returns the type of the given expression.
//!
DLL_PUBLIC Type vc_getType(VC vc, Expr e);

//! \brief Returns the bit-width of the given bitvector.
//!
DLL_PUBLIC int vc_getBVLength(VC vc, Expr e);

//! \brief Create an equality expression. The two children must have the same type.
//!
//! Returns a boolean expression.
//!
DLL_PUBLIC Expr vc_eqExpr(VC vc, Expr child0, Expr child1);

/////////////////////////////////////////////////////////////////////////////
/// BOOLEAN EXPRESSIONS
///
/// The following functions create boolean expressions.
/// The children provided as arguments must be of type boolean.
///
/// An exception is the function vc_iteExpr().
/// In the case of vc_iteExpr() the conditional must always be boolean,
/// but the thenExpr (resp. elseExpr) can be bit-vector or boolean type.
/// However, the thenExpr and elseExpr must be both of the same type.
///
/////////////////////////////////////////////////////////////////////////////

//! \brief Creates a boolean expression that represents true.
//!
DLL_PUBLIC Expr vc_trueExpr(VC vc);

//! \brief Creates a boolean expression that represents false.
//!
DLL_PUBLIC Expr vc_falseExpr(VC vc);

//! \brief Creates a boolean not expression that logically negates its child.
//!
DLL_PUBLIC Expr vc_notExpr(VC vc, Expr child);

//! \brief Creates a binary and-expression that represents a conjunction
//!        of the given boolean child expressions.
//!
DLL_PUBLIC Expr vc_andExpr(VC vc, Expr left, Expr right);

//! \brief Creates an and-expression with multiple child boolean expressions
//!        that represents the conjunction of all of its child expressions.
//!
//! This API is useful since SMTLib2 defines non-binary expressions for logical-and.
//!
DLL_PUBLIC Expr vc_andExprN(VC vc, Expr* children, int numOfChildNodes);

//! \brief Creates a binary or-expression that represents a disjunction
//!        of the given boolean child expressions.
//!
DLL_PUBLIC Expr vc_orExpr(VC vc, Expr left, Expr right);

//! \brief Creates an or-expression with multiple child boolean expressions
//!        that represents the disjunction of all of its child expressions.
//!
//! This API is useful since SMTLib2 defines non-binary expressions for logical-or.
//!
DLL_PUBLIC Expr vc_orExprN(VC vc, Expr* children, int numOfChildNodes);

//! \brief Creates a binary xor-expressions for the given boolean child expressions.
//!
DLL_PUBLIC Expr vc_xorExpr(VC vc, Expr left, Expr right);

//! \brief Creates an implies-expression for the given hyp (hypothesis) and
//!        conc (conclusion) boolean expressions.
//!
DLL_PUBLIC Expr vc_impliesExpr(VC vc, Expr hyp, Expr conc);

//! \brief Creates an if-and-only-if-expression for the given boolean expressions.
//!
DLL_PUBLIC Expr vc_iffExpr(VC vc, Expr left, Expr right);

//! \brief Creates an if-then-else-expression for the given conditional boolean expression
//!        and its then and else expressions which must be of the same type.
//!
//! The output type of this API may be of boolean or bitvector type.
//!
DLL_PUBLIC Expr vc_iteExpr(VC vc, Expr conditional, Expr thenExpr,
                           Expr elseExpr);

//! \brief Returns a bitvector expression from the given boolean expression.
//!
//! Returns a constant bitvector expression that represents one (1) if
//! the given boolean expression was false or returns a bitvector expression
//! representing zero (0) otherwise.
//!
//! Panics if the given expression is not of boolean type.
//!
DLL_PUBLIC Expr vc_boolToBVExpr(VC vc, Expr form);

//! \brief Creates a parameterized boolean expression with the given boolean
//!        variable expression and the parameter param.
//!
DLL_PUBLIC Expr vc_paramBoolExpr(VC vc, Expr var, Expr param);

/////////////////////////////////////////////////////////////////////////////
/// ARRAY EXPRESSIONS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns an array-read-expression representing the reading of
//!        the given array's entry of the given index.
//!
//! The array parameter must be of type array and index must be of type bitvector.
//!
DLL_PUBLIC Expr vc_readExpr(VC vc, Expr array, Expr index);

//! \brief Returns an array-write-expressions representing the writing of
//!        the given new value into the given array at the given entry index.
//!
//! The array parameter must be of type array, and index and newValue of type bitvector.
//!
DLL_PUBLIC Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue);

//! \brief Parses the expression stored in the file of the given filepath
//!        and returns it on success.
//!
//! TODO: What format is expected? SMTLib2?
//!       Does the user have to deallocate resources for the returned expression?
//!       Why exactly is this "pretty cool!"?
//!
DLL_PUBLIC Expr vc_parseExpr(VC vc, const char* filepath);

//! \brief Prints the given expression to stdout in the presentation language.
//!
DLL_PUBLIC void vc_printExpr(VC vc, Expr e);

//! \brief Prints the given expression to stdout as C code.
//!
DLL_PUBLIC void vc_printExprCCode(VC vc, Expr e);

//! \brief Prints the given expression to stdout in the STMLib2 format.
//!
DLL_PUBLIC char* vc_printSMTLIB(VC vc, Expr e);

//! \brief Prints the given expression into the file with the given file descriptor
//!        in the presentation language.
//!
DLL_PUBLIC void vc_printExprFile(VC vc, Expr e, int fd);

// //! \brief Prints the state of the given validity checker into
// //!        buffer allocated by STP stores it into the given 'buf' alongside
// //!        its length into 'len'.
// //!
// //! It is the responsibility of the caller to free the buffer.
// //!
// void vc_printStateToBuffer(VC vc, char **buf, unsigned long *len);

//! \brief Prints the given expression into a buffer allocated by STP.
//!
//! The buffer is returned via output parameter 'buf' alongside its length 'len'.
//! It is the responsibility of the caller to free the memory afterwards.
DLL_PUBLIC void vc_printExprToBuffer(VC vc, Expr e, char** buf,
                                     unsigned long* len);

//! \brief Prints the counter example after an invalid query to stdout.
//!
//! This method should only be called after a query which returns false.
//!
DLL_PUBLIC void vc_printCounterExample(VC vc);

//! \brief Prints variable declarations to stdout.
//!
DLL_PUBLIC void vc_printVarDecls(VC vc);

//! \brief Clears the internal list of variables that are maintained
//!        for printing purposes via 'vc_printVarDecls'.
//!
//! A user may want to do this after finishing printing the variable
//! declarations to prevent memory leaks.
//! This is also useful if printing of declarations is never wanted.
//!
DLL_PUBLIC void vc_clearDecls(VC vc);

//! \brief Prints assertions to stdout.
//!
//! The validity checker's flag 'simplify_print' must be set to '1'
//! to enable simplifications of the asserted formulas during printing.
//!
DLL_PUBLIC void vc_printAsserts(VC vc, int simplify_print _CVCL_DEFAULT_ARG(0));

//! \brief Prints the state of the query to a buffer allocated by STP
//!        that is returned via output parameter 'buf' alongside its
//!        length in 'len'.
//!
//! It is the callers responsibility to free the buffer's memory.
//!
//! The validity checker's flag 'simplify_print' must be set to '1'
//! to enable simplifications of the query state during printing.
//!
DLL_PUBLIC void vc_printQueryStateToBuffer(VC vc, Expr e, char** buf,
                                           unsigned long* len,
                                           int simplify_print);

//! \brief Prints the found counter example to a buffer allocated by STP
//!        that is returned via output parameter 'buf' alongside its
//!        length in 'len'.
//!
//! It is the callers responsibility to free the buffer's memory.
//!
//! The validity checker's flag 'simplify_print' must be set to '1'
//! to enable simplifications of the counter example during printing.
//!
DLL_PUBLIC void vc_printCounterExampleToBuffer(VC vc, char** buf,
                                               unsigned long* len);

//! \brief Prints the query to stdout in presentation language.
//!
DLL_PUBLIC void vc_printQuery(VC vc);

/////////////////////////////////////////////////////////////////////////////
/// CONTEXT RELATED METHODS
/////////////////////////////////////////////////////////////////////////////

//! \brief Adds the given expression as assertion to the given validity checker.
//!
//! The expression must be of type boolean.
//!
DLL_PUBLIC void vc_assertFormula(VC vc, Expr e);

//! \brief Simplifies the given expression with respect to the given validity checker.
//!
DLL_PUBLIC Expr vc_simplify(VC vc, Expr e);

//! \brief Checks the validity of the given expression 'e' in the given context.
//!
//! 'timeout_max_conflicts' is represented and expected as the number of conflicts
//! 'timeout_max_time' is represented and expected in seconds.
//! The given expression 'e' must be of type boolean.
//!
//! Returns ...
//!   0: if 'e' is INVALID
//!   1: if 'e' is VALID
//!   2: if errors occured
//!   3: if the timeout was reached
//!
//! Note: Only the cryptominisat solver supports timeout_max_time
//!
DLL_PUBLIC int vc_query_with_timeout(VC vc, Expr e, int timeout_max_conflicts, int timeout_max_time);

//! \brief Checks the validity of the given expression 'e' in the given context
//!        with an unlimited timeout.
//!
//! This simply forwards to 'vc_query_with_timeout'.
//!
//! Note: Read the documentation of 'vc_query_with_timeout' for more information
//!       about subtle details.
//!
DLL_PUBLIC int vc_query(VC vc, Expr e);

//! \brief Returns the counter example after an invalid query.
//!
DLL_PUBLIC Expr vc_getCounterExample(VC vc, Expr e);

//! \brief Returns an array from a counter example after an invalid query.
//!
//! The buffer for the array is allocated by STP and returned via the
//! non-null expected out parameters 'outIndices' for the indices, 'outValues'
//! for the values and 'outSize' for the size of the array.
//!
//! It is the caller's responsibility to free the memory afterwards.
//!
DLL_PUBLIC void vc_getCounterExampleArray(VC vc, Expr e, Expr** outIndices,
                                          Expr** outValues, int* outSize);

//! \brief Returns the size of the counter example array,
//!        i.e. the number of variable and array locations
//!        in the counter example.
//!
DLL_PUBLIC int vc_counterexample_size(VC vc);

//! \brief Checkpoints the current context and increases the scope level.
//!
//! TODO: What effects has this?
//!
DLL_PUBLIC void vc_push(VC vc);

//! \brief Restores the current context to its state at the last checkpoint.
//!
//! TODO: What effects has this?
//!
DLL_PUBLIC void vc_pop(VC vc);

//! \brief Returns the associated integer from the given bitvector expression.
//!
//! Panics if the given bitvector cannot be represented by an 'int'.
//!
DLL_PUBLIC int getBVInt(Expr e);

//! \brief Returns the associated unsigned integer from the given bitvector expression.
//!
//! Panics if the given bitvector cannot be represented by an 'unsigned int'.
//!
DLL_PUBLIC unsigned int getBVUnsigned(Expr e);

//! Return an unsigned long long int from a constant bitvector expressions

//! \brief Returns the associated unsigned long long integer from the given bitvector expression.
//!
//! Panics if the given bitvector cannot be represented by an 'unsigned long long int'.
//!
DLL_PUBLIC unsigned long long int getBVUnsignedLongLong(Expr e);

//! \brief Prints the bit string for a a constant bitvector expression to a
//!        buffer allocated by STP that is returned via output parameter 'buf'
//!        alongside its length in 'len'.
//!
//! It is the callers responsibility to free the buffer's memory.
//!
DLL_PUBLIC void vc_printBVBitStringToBuffer(Expr e, char** buf, unsigned long* len);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR OPERATIONS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns the bitvector type for the given validity checker.
//!
DLL_PUBLIC Type vc_bvType(VC vc, int no_bits);

//! \brief Returns the bitvector type with a bit-width of 32 for the
//!        given validity checker.
//!
//! This is equal to calling 'vc_bvType(vc, 32)'.
//!
//! Note: This is a convenience function that simply forwards its input.
//!
DLL_PUBLIC Type vc_bv32Type(VC vc);

//! \brief Returns the value size for the given type.
//!
DLL_PUBLIC int vc_getValueSize(VC /* vc */, Type type);

//! \brief Returns the index size for the given type.
//!
DLL_PUBLIC int vc_getIndexSize(VC /* vc */, Type type);

//Const expressions for string, int, long-long, etc

//! \brief Parses the given string and returns an associated bitvector expression.
//!
//! This function expects the input string to be of decimal format.
//!
DLL_PUBLIC Expr vc_bvConstExprFromDecStr(VC vc, int width,
                                         const char* decimalInput);

//! \brief Parses the given string and returns an associated bitvector expression.
//!
//! This function expects the input string to be of binary format.
//!
DLL_PUBLIC Expr vc_bvConstExprFromStr(VC vc, const char* binaryInput);

//! \brief Returns a bitvector with 'bitWidth' bit-width from the given
//!        unsigned integer value.
//!
//! The 'bitWidth' must be large enough to fully store the given value's bit representation.
//!
DLL_PUBLIC Expr vc_bvConstExprFromInt(VC vc, int bitWidth, unsigned int value);

//! \brief Returns a bitvector with 'bitWidth' bit-width from the given
//!        unsigned long long integer value.
//!
//! The 'bitWidth' must be large enough to fully store the given value's bit representation.
//!
DLL_PUBLIC Expr vc_bvConstExprFromLL(VC vc, int bitWidth,
                                     unsigned long long value);

//! \brief Returns a bitvector with a bit-width of 32 from the given
//!        unsigned integer value.
//!
DLL_PUBLIC Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR ARITHMETIC OPERATIONS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns a bitvector expression representing the concatenation of the two
//!        given bitvector expressions.
//!
//! This results in a bitvector with the bit-width of the bit-width sum
//! of its children.
//!
//! Example: Given bitvector 'a = 1101' and 'b = 1000' then 'vc_bvConcatExpr(vc, a, b)'
//!          results in 'c = 11011000'.
//!
DLL_PUBLIC Expr vc_bvConcatExpr(VC vc, Expr left, Expr right);

//! \brief Returns a bitvector expression representing the addition of the two
//!        given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_bvPlusExpr(VC vc, int bitWidth, Expr left, Expr right);

//! \brief Returns a bitvector expression representing the addition of the N
//!        given bitvector expressions in the 'children' array.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_bvPlusExprN(VC vc, int bitWidth, Expr* children,
                               int numOfChildNodes);

//! \brief Returns a bitvector expression with a bit-width of 32
//!        representing the addition of the two given bitvector expressions.
//!
//! The given bitvector expressions must have a bit-width of 32.
//!
DLL_PUBLIC Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right);

//! \brief Returns a bitvector expression with a bit-width of 'bitWidth'
//!        representing the subtraction '(left - right)' of the two
//!        given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_bvMinusExpr(VC vc, int bitWidth, Expr left, Expr right);

//! \brief Returns a bitvector expression with a bit-width of 32
//!        representing the subtraction '(left - right)' of the given
//!        bitvector expressions.
//!
//! The given bitvector expressions must have a bit-width of 32.
//!
DLL_PUBLIC Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right);

//! \brief Returns a bitvector expression with a bit-width of 'bitWidth'
//!        representing the multiplication '(left * right)' of the two
//!        given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_bvMultExpr(VC vc, int bitWidth, Expr left, Expr right);

//! \brief Returns a bitvector expression with a bit-width of 32
//!        representing the multiplication '(left * right)' of the given
//!        bitvector expressions.
//!
//! The given bitvector expressions must have a bit-width of 32.
//!
DLL_PUBLIC Expr vc_bv32MultExpr(VC vc, Expr left, Expr right);

//! \brief Returns a bitvector expression with a bit-width of 'bitWidth'
//!        representing the division '(dividend / divisor)' of the two
//!        given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_bvDivExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

//! \brief Returns a bitvector expression with a bit-width of 'bitWidth'
//!        representing the modulo '(dividend % divisor)' of the two
//!        given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_bvModExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

//! \brief Returns a bitvector expression with a bit-width of 'bitWidth'
//!        representing the modulo '(dividend % divisor)' of the two
//!        given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_bvRemExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

//! \brief Returns a (signed) bitvector expression with a bit-width of 'bitWidth'
//!        representing the signed division '(dividend / divisor)' of the two
//!        given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_sbvDivExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

//! \brief Returns a (signed) bitvector expression with a bit-width of 'bitWidth'
//!        representing the signed modulo '(dividend % divisor)' of the two
//!        given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_sbvModExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

//! \brief Returns a (signed) bitvector expression with a bit-width of 'bitWidth'
//!        representing the signed remainder of the two
//!        given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width as 'bitWidth'
//!
DLL_PUBLIC Expr vc_sbvRemExpr(VC vc, int bitWidth, Expr dividend, Expr divisor);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR COMPARISON OPERATIONS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns a boolean expression representing the less-than
//!        operation '(left < right)' of the given bitvector expressions.
//!
DLL_PUBLIC Expr vc_bvLtExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression representing the less-equals
//!        operation '(left <= right)' of the given bitvector expressions.
//!
DLL_PUBLIC Expr vc_bvLeExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression representing the greater-than
//!        operation '(left > right)' of the given bitvector expressions.
//!
DLL_PUBLIC Expr vc_bvGtExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression representing the greater-equals
//!        operation '(left >= right)' of the given bitvector expressions.
//!
DLL_PUBLIC Expr vc_bvGeExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression representing the signed less-than
//!        operation '(left < right)' of the given signed bitvector expressions.
//!
DLL_PUBLIC Expr vc_sbvLtExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression representing the signed less-equals
//!        operation '(left <= right)' of the given signed bitvector expressions.
//!
DLL_PUBLIC Expr vc_sbvLeExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression representing the signed greater-than
//!        operation '(left > right)' of the given signed bitvector expressions.
//!
DLL_PUBLIC Expr vc_sbvGtExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression representing the signed greater-equals
//!        operation '(left >= right)' of the given signed bitvector expressions.
//!
DLL_PUBLIC Expr vc_sbvGeExpr(VC vc, Expr left, Expr right);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR BITWISE OPERATIONS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns a bitvector expression representing the arithmetic
//!        negation '(-a)' (unary minus) of the given child bitvector expression.
//!
DLL_PUBLIC Expr vc_bvUMinusExpr(VC vc, Expr child);

//! \brief Returns a bitvector expression representing the bitwise-and
//!        operation '(a & b)' for the given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width.
//!
DLL_PUBLIC Expr vc_bvAndExpr(VC vc, Expr left, Expr right);

//! \brief Returns a bitvector expression representing the bitwise-or
//!        operation '(a | b)' for the given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width.
//!
DLL_PUBLIC Expr vc_bvOrExpr(VC vc, Expr left, Expr right);

//! \brief Returns a bitvector expression representing the bitwise-xor
//!        operation '(a ^ b)' for the given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width.
//!
DLL_PUBLIC Expr vc_bvXorExpr(VC vc, Expr left, Expr right);

//! \brief Returns a bitvector expression representing the bitwise-not
//!        operation '~a' for the given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width.
//!
DLL_PUBLIC Expr vc_bvNotExpr(VC vc, Expr child);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR SHIFT OPERATIONS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns a bitvector expression with a bit-width of 'bitWidth'
//!        representing the left-shift operation '(left << right)' of the
//!        given bitvector expressions.
//!
//! Note: This is the new API for this kind of operation!
//!
DLL_PUBLIC Expr vc_bvLeftShiftExprExpr(VC vc, int bitWidth, Expr left,
                                       Expr right);

//! \brief Returns a bitvector expression with a bit-width of 'bitWidth'
//!        representing the right-shift operation '(left >> right)' of the
//!        given bitvector expressions.
//!
//! Note: This is the new API for this kind of operation!
//!
DLL_PUBLIC Expr vc_bvRightShiftExprExpr(VC vc, int bitWidth, Expr left,
                                        Expr right);

//! \brief Returns a bitvector expression with a bit-width of 'bitWidth'
//!        representing the signed right-shift operation '(left >> right)' of the
//!        given bitvector expressions.
//!
//! Note: This is the new API for this kind of operation!
//!
DLL_PUBLIC Expr vc_bvSignedRightShiftExprExpr(VC vc, int bitWidth, Expr left,
                                              Expr right);

//! \brief Deprecated: Use the new API instead!
//!
//! Returns an expression representing the left-shift operation '(child << sh_amt)'
//! for the given child bitvector expression.
//!
//! Note: Use 'vc_bvLeftShiftExprExpr' instead!
//!
DLL_PUBLIC Expr vc_bvLeftShiftExpr(VC vc, int sh_amt, Expr child);

//! \brief Deprecated: Use the new API instead!
//!
//! Returns an expression representing the right-shift operation '(child >> sh_amt)'
//! for the given child bitvector expression.
//!
//! Note: Use 'vc_bvRightShiftExprExpr' instead!
//!
DLL_PUBLIC Expr vc_bvRightShiftExpr(VC vc, int sh_amt, Expr child);

//! \brief Deprecated: Use the new API instead!
//!
//! Returns a bitvector expression with a bit-width of 32
//! representing the left-shift operation '(child << sh_amt)'
//! for the given child bitvector expression.
//!
//! Note: Use 'vc_bvLeftShiftExprExpr' instead!
//!
DLL_PUBLIC Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child);

//! \brief Deprecated: Use the new API instead!
//!
//! Returns a bitvector expression with a bit-width of 32
//! representing the right-shift operation '(child >> sh_amt)'
//! for the given child bitvector expression.
//!
//! Note: Use 'vc_bvRightShiftExprExpr' instead!
//!
DLL_PUBLIC Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child);

//! \brief Deprecated: Use the new API instead!
//!
//! Returns a bitvector expression with a bit-width of 32
//! representing the left-shift operation '(child << sh_amt)'
//! for the given child bitvector expression.
//!
//! Note: Use 'vc_bvLeftShiftExprExpr' instead!
//!
DLL_PUBLIC Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child);

//! \brief Deprecated: Use the new API instead!
//!
//! Returns a bitvector expression with a bit-width of 32
//! representing the right-shift operation '(child >> sh_amt)'
//! for the given child bitvector expression.
//!
//! Note: Use 'vc_bvRightShiftExprExpr' instead!
//!
DLL_PUBLIC Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child);

//! \brief Deprecated: Use the new API instead!
//!
//! Returns a bitvector expression representing the division
//! operation of the power of two '(child / 2^rhs)' for the given
//! bitvector expressions.
//!
//! Note: Use 'vc_bvSignedRightShiftExprExpr' instead!
//!
DLL_PUBLIC Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs);

/////////////////////////////////////////////////////////////////////////////
/// BITVECTOR EXTRACTION & EXTENSION
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns a bitvector expression representing the extraction
//!        of the bits within the range of 'low_bit_no' and 'high_bit_no'.
//!
//! Note: The resulting bitvector expression has a bit-width of '(high_bit_no - low_bit_no) + 1'.
//!
DLL_PUBLIC Expr vc_bvExtract(VC vc, Expr child, int high_bit_no,
                             int low_bit_no);

//! \brief Superseeded: Use 'vc_bvBoolExtract_Zero' or 'vc_bvBoolExtract_One' instead.
//!
//! Returns a boolean expression that accepts a bitvector expression 'x'
//! and represents the following equation: '(x[bit_no:bit_no] == 0)'.
//!
//! Note: This is equal to calling 'vc_bvBoolExtract_Zero'.
//!
DLL_PUBLIC Expr vc_bvBoolExtract(VC vc, Expr x, int bit_no);

//! \brief Returns a boolean expression that accepts a bitvector expression 'x'
//!        and represents the following equation: '(x[bit_no:bit_no] == 0)'.
//!
DLL_PUBLIC Expr vc_bvBoolExtract_Zero(VC vc, Expr x, int bit_no);

//! \brief Returns a boolean expression that accepts a bitvector expression 'x'
//!        and represents the following equation: '(x[bit_no:bit_no] == 1)'.
//!
DLL_PUBLIC Expr vc_bvBoolExtract_One(VC vc, Expr x, int bit_no);

//! \brief Returns a bitvector expression representing the extension of the given
//!        to the amount of bits given by 'newWidth'.
//!
//! Note: This operation retains the signedness of the bitvector is existant.
//!
DLL_PUBLIC Expr vc_bvSignExtend(VC vc, Expr child, int newWidth);

/////////////////////////////////////////////////////////////////////////////
/// CONVENIENCE FUNCTIONS FOR ARRAYS
/////////////////////////////////////////////////////////////////////////////

/*C pointer support:  C interface to support C memory arrays in CVCL */

//! \brief Convenience function to create a named array expression with
//!        an index bit-width of 32 and a value bit-width of 8.
//!
DLL_PUBLIC Expr vc_bvCreateMemoryArray(VC vc, const char* arrayName);

//! \brief Convenience function to read a bitvector with byte-width 'numOfBytes' of an
//!        array expression created by 'vc_bvCreateMemoryArray' and return it.
//!
//! Note: This returns a bitvector expression with a bit-width of 'numOfBytes'.
//!
DLL_PUBLIC Expr vc_bvReadMemoryArray(VC vc, Expr array, Expr byteIndex,
                                     int numOfBytes);

//! \brief Convenience function to write a bitvector 'element' with byte-width 'numOfBytes'
//!        into the given array expression at offset 'byteIndex'.
//!
DLL_PUBLIC Expr vc_bvWriteToMemoryArray(VC vc, Expr array, Expr byteIndex,
                                        Expr element, int numOfBytes);

/////////////////////////////////////////////////////////////////////////////
/// GENERAL EXPRESSION OPERATIONS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns a string representation of the given expression.
//!
//! Note:
//!     The caller is responsible for deallocating the string afterwards.
//!     The buffer that stores the string is allocated by STP.
//!
DLL_PUBLIC char* exprString(Expr e);

//! \brief Returns a string representation of the given type.
//!
//! Note:
//!     The caller is responsible for deallocating the string afterwards.
//!     The buffer that stores the string is allocated by STP.
//!
DLL_PUBLIC char* typeString(Type t);

//! \brief Returns the n-th child of the given expression.
//!
DLL_PUBLIC Expr getChild(Expr e, int n);

//! \brief Misleading name!
//!
//! Returns '1' if the given boolean expression evaluates to 'true',
//! returns '0' if the given boolean expression evaluates to 'false',
//! or returns '-1' otherwise, i.e. if the given expression was not a
//! boolean expression.
//!
DLL_PUBLIC int vc_isBool(Expr e);

//! \brief Registers the given error handler function to be called for each
//!        fatal error that occures while running STP.
//!
DLL_PUBLIC void
vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg));

//! \brief Returns the hash of the given query state.
//!
DLL_PUBLIC int vc_getHashQueryStateToBuffer(VC vc, Expr query);

//! \brief Destroy the given validity checker.
//!
//! Removes all associated expressions with it if 'EXPRDELETE' was set to 'true'
//! via 'vc_setInterfaceFlags' during the process.
//!
DLL_PUBLIC void vc_Destroy(VC vc);

//! \brief Destroy the given expression, freeing its associated memory.
//!
DLL_PUBLIC void vc_DeleteExpr(Expr e);

//! \brief Returns the whole counterexample from the given validity checker.
//!
DLL_PUBLIC WholeCounterExample vc_getWholeCounterExample(VC vc);

//! \brief Returns the value of the given term expression from the given whole counter example.
//!
DLL_PUBLIC Expr vc_getTermFromCounterExample(VC vc, Expr e,
                                             WholeCounterExample c);

//! \brief Destroys the given whole counter example, freeing all of its associated memory.
//!
DLL_PUBLIC void vc_deleteWholeCounterExample(WholeCounterExample cc);

//! Covers all kinds of expressions that exist in STP.
//!
enum exprkind_t
{
  UNDEFINED, //!< An undefined expression.
  SYMBOL,    //!< Named expression (or variable), i.e. created via 'vc_varExpr'.
  BVCONST, //!< Bitvector constant expression, i.e. created via 'vc_bvConstExprFromInt'.
  BVNOT,    //!< Bitvector bitwise-not
  BVCONCAT, //!< Bitvector concatenation
  BVOR,     //!< Bitvector bitwise-or
  BVAND,    //!< Bitvector bitwise-and
  BVXOR,    //!< Bitvector bitwise-xor
  BVNAND, //!< Bitvector bitwise not-and; OR nand (TODO: does this still exist?)
  BVNOR,  //!< Bitvector bitwise not-or; OR nor (TODO: does this still exist?)
  BVXNOR, //!< Bitvector bitwise not-xor; OR xnor (TODO: does this still exist?)
  BVEXTRACT,    //!< Bitvector extraction, i.e. via 'vc_bvExtract'.
  BVLEFTSHIFT,  //!< Bitvector left-shift
  BVRIGHTSHIFT, //!< Bitvector right-right
  BVSRSHIFT,    //!< Bitvector signed right-shift
  BVPLUS,       //!< Bitvector addition
  BVSUB,        //!< Bitvector subtraction
  BVUMINUS,     //!< Bitvector unary minus; OR negate expression
  BVMULT,       //!< Bitvector multiplication
  BVDIV,        //!< Bitvector division
  BVMOD,        //!< Bitvector modulo operation
  SBVDIV,       //!< Signed bitvector division
  SBVREM,       //!< Signed bitvector remainder
  SBVMOD,       //!< Signed bitvector modulo operation
  BVSX,         //!< Bitvector signed extend
  BVZX,         //!< Bitvector zero extend
  ITE,          //!< If-then-else
  BOOLEXTRACT,  //!< Bitvector boolean extraction
  BVLT,         //!< Bitvector less-than
  BVLE,         //!< Bitvector less-equals
  BVGT,         //!< Bitvector greater-than
  BVGE,         //!< Bitvector greater-equals
  BVSLT,        //!< Signed bitvector less-than
  BVSLE,        //!< Signed bitvector less-equals
  BVSGT,        //!< Signed bitvector greater-than
  BVSGE,        //!< Signed bitvector greater-equals
  EQ,           //!< Equality comparator
  FALSE,        //!< Constant false boolean expression
  TRUE,         //!< Constant true boolean expression
  NOT,          //!< Logical-not boolean expression
  AND,          //!< Logical-and boolean expression
  OR,           //!< Logical-or boolean expression
  NAND, //!< Logical-not-and boolean expression (TODO: Does this still exist?)
  NOR,  //!< Logical-not-or boolean expression (TODO: Does this still exist?)
  XOR,  //!< Logical-xor (either-or) boolean expression
  IFF,  //!< If-and-only-if boolean expression
  IMPLIES,   //!< Implication boolean expression
  PARAMBOOL, //!< Parameterized boolean expression
  READ,      //!< Array read expression
  WRITE,     //!< Array write expression
  ARRAY,     //!< Array creation expression
  BITVECTOR, //!< Bitvector creation expression
  BOOLEAN    //!< Boolean creation expression
};

//! \brief Returns the expression-kind of the given expression.
//!
DLL_PUBLIC enum exprkind_t getExprKind(Expr e);

//! \brief Returns the number of child expressions of the given expression.
//!
DLL_PUBLIC int getDegree(Expr e);

//! \brief Returns the bit-width of the given bitvector expression.
//!
DLL_PUBLIC int getBVLength(Expr e);

//! Covers all kinds of types that exist in STP.
//!
enum type_t
{
  BOOLEAN_TYPE = 0,
  BITVECTOR_TYPE,
  ARRAY_TYPE,
  UNKNOWN_TYPE
};

//! \brief Returns the type-kind of the given expression.
//!
DLL_PUBLIC enum type_t getType(Expr e);

// get value bit width

//! \brief Returns the value bit-width of the given expression.
//!
//! This is mainly useful for array expression.
//!
DLL_PUBLIC int getVWidth(Expr e);

//! \brief Returns the index bit-width of the given expression.
//!
//! This is mainly useful for array expression.
//!
DLL_PUBLIC int getIWidth(Expr e);

//! \brief Prints the given counter example to the file that is
//!        associated with the given open file descriptor.
//!
DLL_PUBLIC void vc_printCounterExampleFile(VC vc, int fd);

//! \brief Returns the name of the given variable expression.
//!
DLL_PUBLIC const char* exprName(Expr e);

//! \brief Returns the internal node ID of the given expression.
//!
DLL_PUBLIC int getExprID(Expr ex);

//! \brief Parses the given string in CVC or SMTLib1.0 format and extracts
//!        query and assertion information into the 'outQuery' and 'outAsserts'
//!        buffers respectively.
//!
//! It is the caller's responsibility to free the buffer's memory afterwards.
//!
//! Note: The user can controle the parsed format via 'process_argument'.
//!
//! Returns '1' if parsing was successful.
//!
DLL_PUBLIC int vc_parseMemExpr(VC vc, const char* s, Expr* outQuery,
                               Expr* outAsserts);

//! \brief Checks if STP was compiled with support for minisat
//!
//!  Note: always returns true (future support for minisat being the
//!  non-default)
//!
DLL_PUBLIC bool vc_supportsMinisat(VC vc);

//! \brief Sets underlying SAT solver to minisat
//!
DLL_PUBLIC bool vc_useMinisat(VC vc);

//! \brief Checks if underlying SAT solver is minisat
//!
DLL_PUBLIC bool vc_isUsingMinisat(VC vc);

//! \brief Checks if STP was compiled with support for simplifying minisat
//!
//!  Note: always returns true (future support for simplifying minisat being
//!  the non-default)
//!
DLL_PUBLIC bool vc_supportsSimplifyingMinisat(VC vc);

//! \brief Sets underlying SAT solver to simplifying minisat
//!
DLL_PUBLIC bool vc_useSimplifyingMinisat(VC vc);

//! \brief Checks if underlying SAT solver is simplifying minisat
//!
DLL_PUBLIC bool vc_isUsingSimplifyingMinisat(VC vc);

//! \brief Checks if STP was compiled with support for cryptominisat
//!
DLL_PUBLIC bool vc_supportsCryptominisat(VC vc);

//! \brief Sets underlying SAT solver to cryptominisat
//!
DLL_PUBLIC bool vc_useCryptominisat(VC vc);

//! \brief Checks if underlying SAT solver is cryptominisat
//!
DLL_PUBLIC bool vc_isUsingCryptominisat(VC vc);

//! \brief Checks if STP was compiled with support for riss
//!
DLL_PUBLIC bool vc_supportsRiss(VC vc);

//! \brief Sets underlying SAT solver to riss
//!
DLL_PUBLIC bool vc_useRiss(VC vc);

//! \brief Checks if underlying SAT solver is riss
//!
DLL_PUBLIC bool vc_isUsingRiss(VC vc);

//! \brief Checks if STP was compiled with support for Kissat
//!
DLL_PUBLIC bool vc_supportsKissat(VC vc);

//! \brief Sets underlying SAT solver to Kissat
//!
DLL_PUBLIC bool vc_useKissat(VC vc);

//! \brief Checks if underlying SAT solver is Kissat
//!
DLL_PUBLIC bool vc_isUsingKissat(VC vc);

#ifdef __cplusplus
}
#endif

#undef DLL_PUBLIC // Undefine internal macro to prevent it from leaking into the API.
#undef DLL_LOCAL // Undefine internal macro to prevent it from leaking into the API.

#undef _CVCL_DEFAULT_ARG // Undefine macro to not pollute global macro namespace!

#endif // _cvcl__include__c_interface_h_
