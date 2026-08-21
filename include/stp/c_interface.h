/********************************************************************
 * AUTHORS: Michael Katelman, Vijay Ganesh, Trevor Hansen, Andrew Teylu
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
#include <stddef.h>
#include <stdint.h>

/////////////////////////////////////////////////////////////////////////////
/// STP API INTERNAL MACROS FOR LINKING
///
/// These are undefined at the end of this file to prevent them from leaking
/// into code that includes it.
/////////////////////////////////////////////////////////////////////////////

// The DLL_PUBLIC / DLL_LOCAL block below is duplicated verbatim from
// include/stp/Util/Attributes.h, and deliberately so: this is the only header
// STP installs, and Attributes.h ships nowhere, so it cannot be included from
// here. Do not "deduplicate" the two -- that would leave this header with no
// definition of DLL_PUBLIC once installed. Keep them in sync instead.
#if defined(_MSC_VER)
// MSVC symbol visibility. Two macros drive it, both set by lib/CMakeLists.txt:
//
//   STP_SHARED_LIB  libstp is a DLL. Defined only when BUILD_SHARED_LIBS is ON:
//                   for the library's own sources, and, through the exported
//                   target's interface, for clients that link it.
//   STP_EXPORTS     this translation unit is part of libstp itself, rather than
//                   a client compiling against these headers.
//
// A static build defines neither and gets an empty DLL_PUBLIC. That is the only
// expansion that links for static: a static client that saw dllimport would
// fail at link time. A shared build gets dllexport while the library is being
// compiled and dllimport for everyone else.
//
// The mechanism is currently dormant -- no shared MSVC build of STP is produced
// (the only Windows CI job is STATICCOMPILE=ON, which forces BUILD_SHARED_LIBS
// OFF), so neither __declspec arm is ever taken. It is kept correct so that
// enabling a Windows DLL build later works.
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

//! Opaque, nonzero identity of a context-owned UF declaration. Identities are
//! allocated monotonically across the process and never reused; zero is the
//! invalid handle. They are values, not pointers: callers never dereference,
//! cast, or free them. Destroying the owning VC retires its registry entry, so
//! a stale or cross-context identity can be rejected without dereferencing it.
typedef uint64_t UFDeclHandle;

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
//!  - 'i': Enables incremental solving from the first vc_query on.
//!  - 'm': Use SMTLib1 parser. Conflicts with using SMTLib2 parser.
//!  - 'n': Enables printing of the output. TODO: What is meant with output here?
//!  - 'p': Enables printing of counter examples.
//!  - 'q': Enables printing of array values in declared order.
//!  - 'r': Enables accermannisation.
//!  - 's': Sets the status flag to true. TODO: What consequenses does this have?
//!  - 't': Enables quick statistics. TODO: What is this?
//!  - 'u': Enables the UFSTP v2 uninterpreted-functions profile.
//!  - 'v': Enables printing of nodes.
//!  - 'w': *Disables* word-level solving, despite the name.
//!  - 'x': Enables deciding equality between whole arrays (the extensional
//!         theory of arrays). Must be set before any such equality is built.
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

  //! \brief Deprecated: use `MS` instead!
  //!
  //! This used to be the array version of the minisat SAT solver.
  //!
  //! Currently simply forwards to MS.
  //!
  MSP,

  //! Use the SAT solver CaDiCaL.
  //!
  //! Note: this is last so that the values of the flags above are unchanged
  //! from the releases before CaDiCaL was added.
  //!
  CADICAL,

  //! The real-query ordinal at which a session that never asked for the
  //! incremental driver starts using it anyway.
  //!
  //! `param_value` is that ordinal: 1 engages on the first query, N on the
  //! Nth, 0 disables automatic engagement entirely, and a negative value
  //! restores the default (the third query). `vc_setFlags(vc, 'i')` still
  //! forces the driver from the first query regardless of this.
  //!
  //! Set this before the first query; it is read per query, so changing it
  //! mid-session takes effect on the next one.
  //!
  //! Note: appended so the values of the flags above are unchanged.
  //!
  INCREMENTAL_AUTO_ENGAGE_AT,

  //! How many congruence lemmas one refuted candidate may install during
  //! uninterpreted-function refinement (default 8).
  //!
  //! `param_value` is that count: zero installs every conflict the candidate
  //! exposes, and one is the one-lemma-per-round reference profile. This is
  //! the C API's way to reach --uf-lemmas-per-round. A negative value is
  //! refused with a nonfatal diagnostic.
  //!
  UF_LEMMAS_PER_ROUND,

  //! The bit-vector width given to a sort introduced by (declare-sort S 0),
  //! which bounds how many elements of that sort a query can tell apart
  //! (default 16).
  //!
  //! `param_value` is that width. A larger value is always sound and only a
  //! smaller one is not, so raising it is the way to answer a query that
  //! exhausted the carrier. This is the C API's way to reach --uf-sort-width.
  //!
  //! Accepted between 1 and 1024, and refused with a nonfatal diagnostic
  //! outside that, leaving the width unchanged. Both ends were reachable and
  //! neither failed cleanly: zero made every element a zero-width term that
  //! the legacy width checks read as a Boolean, and a width past the ceiling
  //! overflowed the word arithmetic the bit-vector layer is built on and
  //! answered unsat for two elements of an unbounded sort.
  //!
  UF_SORT_WIDTH,

  //! Replace a (distinct ...) over variables that occur nowhere else with a
  //! strict chain, fixing one of the n! equivalent orderings the bit-blaster
  //! would otherwise search.
  //!
  //! `param_value` nonzero enables (the default), zero disables. This is the
  //! C API's way to reach --distinct-ordering.
  //!
  DISTINCT_ORDERING,

  //! A hard limit on the AND gates bit-blasting may build, so that a query
  //! whose AIG would exhaust the machine reports unknown instead (default -1:
  //! no limit).
  //!
  //! `param_value` is that count. -1 means no limit and is the only negative
  //! value accepted; any other negative value is refused with a nonfatal
  //! diagnostic. Zero is a budget of no gates at all, which gives up before
  //! the first one. This is the C API's way to reach --aig-node-budget.
  //!
  //! Exceeding it ends the query without an answer: vc_query returns 3, the
  //! value every way of giving up returns, and vc_getReasonUnknown returns
  //! REASON_UNKNOWN_INCOMPLETE with a sentence naming this budget and the
  //! count it stopped at -- the same sentence SMT-LIB2 reads through
  //! (get-info :reason-unknown).
  //!
  AIG_NODE_BUDGET

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

//! \brief Creates a validity checker over an existing node manager.
//!
//! `_bm` must be a live stp::STPMgr* (the parameter is void* only so this C
//! header need not name the C++ type). Lets a client that builds nodes
//! through the C++ objects solve them through the C API. The manager keeps
//! any node factory it was already given, and stays owned by the caller's
//! vc_Destroy like any other checker's manager.
//!
DLL_PUBLIC VC vc_createValidityCheckerReuse(void* _bm);

//! \brief Returns the boolean type for the given validity checker.
//!
DLL_PUBLIC Type vc_boolType(VC vc);

//! \brief Returns an array type with the given index type and data type
//!        for the given validity checker.
//!
//! Index type and data type may each be a bitvector type (vc_bvType), a
//! floating-point type (vc_fpType) or the RoundingMode type
//! (vc_fpRoundingModeType), matching SMT-LIB's (Array X Y) over those
//! sorts. Reads and writes then expect (and vc_readExpr's result carries)
//! the corresponding sorts; a float-indexed array follows SMT-LIB '='
//! on its indexes, so every NaN addresses one cell while +0 and -0 stay
//! distinct cells.
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
//! A positive 'indexwidth' asks for an array, whose elements are
//! 'valuewidth' bits wide; a zero 'indexwidth' asks for a bit-vector of
//! 'valuewidth' bits, or for a Boolean when 'valuewidth' is zero too.
//! A zero-width bit-vector is not a sort, so an array whose element width
//! is not positive is a fatal error, as it is in vc_bvType: the message
//! reaches any handler registered with vc_registerErrorHandler and the
//! call does not return.
//!
DLL_PUBLIC Expr vc_varExpr1(VC vc, const char* name, int indexwidth,
                            int valuewidth);

//! \brief Declares a nonzero-arity uninterpreted function and returns its
//!        context-owned identity.
//!
//! Call vc_setFlag(vc, 'u') before constructing any Type or Expr handle that
//! will be supplied to the UF API. Each domain entry and the codomain must be
//! a live Type owned by this VC, constructed with vc_boolType, vc_bvType,
//! vc_fpType or vc_fpRoundingModeType; bit-vector widths must be positive.
//! Array types are not accepted, because an uninterpreted function is decided
//! by comparing concrete argument values and a counterexample gives an array
//! only as a partial map. domainCount must be at least one: SMT-LIB treats a
//! zero-arity declare-fun as an ordinary symbol, which vc_varExpr represents.
//!
//! A FloatingPoint position is compared by *value*, not by bit pattern: every
//! NaN is one value, so f(NaN) and f(NaN) agree however each was built, while
//! -0 and +0 are distinct arguments.
//!
//! The Type array and its elements are borrowed for this call; ownership is
//! not transferred. The declaration copies the name and source sorts, so the
//! caller may release UF-tracked Type wrappers afterwards with vc_DeleteExpr.
//! The returned UFDeclHandle is immutable, owned by the VC, is not an Expr,
//! must not be passed to vc_DeleteExpr, and remains safely rejectable after
//! the VC is destroyed. Ordinary symbols and UFs share one namespace.
//!
//! On a null/foreign/destroyed Type, unsupported or empty signature, invalid
//! or colliding name, disabled feature, or other validation failure, no
//! declaration is registered. A nonfatal diagnostic is sent to the handler
//! installed with vc_registerErrorHandler (or stderr), and zero is returned.
DLL_PUBLIC UFDeclHandle vc_declareUninterpretedFunction(
    VC vc, const char* name, const Type* domain, size_t domainCount,
    Type codomain);

//! \brief Builds a durable, exactly typed application of a declared UF.
//!
//! function must be a live declaration identity owned by this VC. arguments
//! is borrowed for this call and each entry must be a live UF-tracked Expr
//! from the same VC; no ownership is transferred. The argument count and
//! every source sort must match the declaration exactly -- a float argument
//! must have the declared format, and a rounding mode the RoundingMode sort
//! rather than a bare 5-bit vector.
//!
//! The returned Expr denotes the public UF_APPLY itself, never a temporary
//! lowered SAT symbol. Its underlying hash-consed node has context lifetime;
//! this wrapper is caller-owned until vc_DeleteExpr or vc_Destroy, whichever
//! comes first. As with every legacy raw Expr, a wrapper is invalid after
//! vc_DeleteExpr.
//!
//! A bad/stale/cross-context declaration, bad argument handle, arity mismatch
//! or sort mismatch builds and registers nothing, reports a nonfatal
//! diagnostic through vc_registerErrorHandler (or stderr), and returns NULL.
DLL_PUBLIC Expr vc_applyUninterpretedFunction(
    VC vc, UFDeclHandle function, const Expr* arguments,
    size_t argumentCount);

//! \brief Evaluates a durable UF_APPLY in the most recently certified model.
//!
//! The application must be a live wrapper owned by this VC, must have been
//! reachable from the public root of the most recent satisfiable query, and
//! that query's UF model must still be certified. Assertion/stack changes,
//! another query, or declaration changes can invalidate the certified map.
//! vc_getCounterExample dispatches UF_APPLY handles through this same map.
//!
//! Success returns a caller-owned constant wrapper of the declared codomain
//! sort -- a Boolean, a bit-vector literal, a floating-point constant of the
//! declared format, or one of the five rounding modes -- released with
//! vc_DeleteExpr. A non-application, stale/inactive/cross-context wrapper,
//! unobserved application, or missing/invalidated certified model reports a
//! nonfatal diagnostic through vc_registerErrorHandler (or stderr) and
//! returns NULL. No internal lowered symbol is exposed.
DLL_PUBLIC Expr vc_getUninterpretedFunctionValue(VC vc, Expr application);

//! \brief Why the last query had no answer.
//!
//! vc_query reports a query it could not decide as 3, whatever stopped it, so
//! this is how a caller learns which of the causes it was and whether trying
//! again could help. It is the C API's reading of the same record SMT-LIB2
//! reports through (get-info :reason-unknown).
//!
enum reason_unknown_t
{
  //! No unknown to explain: the last query was answered, or none has run.
  REASON_UNKNOWN_NONE = 0,

  //! The wall clock given to vc_query_with_timeout ran out. The only cause
  //! that more time on the same machine may get past.
  REASON_UNKNOWN_TIMEOUT,

  //! The conflict budget given to vc_query_with_timeout ran out. Deterministic
  //! -- re-running with a longer clock reproduces it exactly -- so what is
  //! worth doing is raising the budget.
  REASON_UNKNOWN_CONFLICT_BUDGET,

  //! Something stopped before an answer and has no value of its own here yet.
  //! vc_getReasonUnknownToBuffer gives the sentence, which says what.
  //!
  //! The one below was this until it was named, and is appended rather
  //! than inserted so that nothing already reporting as incomplete moves. A
  //! caller that has not heard of a later addition compares unequal to every
  //! value it knows and still has the sentence to fall back on, which is what
  //! makes naming a cause a safe change to make.
  REASON_UNKNOWN_INCOMPLETE,

  //! A sort introduced by (declare-sort S 0) had a carrier too narrow for the
  //! query, so an unsat that may be an artefact of the encoding was withheld
  //! rather than reported. Raise UF_SORT_WIDTH.
  //!
  //! Not reachable through this interface today: a declared sort can only come
  //! from an SMT-LIB2 (declare-sort), and the sorts a UF may be declared over
  //! here are built by vc_boolType, vc_bvType, vc_fpType and
  //! vc_fpRoundingModeType. Named for what it is so that reading the sentence
  //! is not the only way to know it, if that ever changes.
  REASON_UNKNOWN_CARRIER_EXHAUSTED

};

//! \brief Returns why the last query had no answer.
//!
//! Meaningful after vc_query returns 3; REASON_UNKNOWN_NONE at any other
//! time, since there is then no unknown to explain. The record is cleared at
//! the start of every query, so this describes the last one and not the
//! session.
DLL_PUBLIC enum reason_unknown_t vc_getReasonUnknown(VC vc);

//! \brief Prints why the last query had no answer into a buffer allocated by
//!        STP.
//!
//! The buffer is returned via output parameter 'buf' alongside its length
//! 'len'. It is the responsibility of the caller to free the memory
//! afterwards.
//!
//! REASON_UNKNOWN_INCOMPLETE and REASON_UNKNOWN_CARRIER_EXHAUSTED carry a
//! sentence, saying what was reached; the causes their name alone is enough
//! to act on write an empty string. Prose for a person to read: a caller deciding
//! what to do next wants vc_getReasonUnknown, which is why the two are
//! separate.
DLL_PUBLIC void vc_getReasonUnknownToBuffer(VC vc, char** buf, size_t* len);

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
//! On floating-point operands this is SMT-LIB's '=': +0 and -0 are
//! distinct, and every NaN equals every NaN (payloads are not
//! distinguished). For IEEE equality (+0 == -0, NaN unequal to
//! everything) use vc_fpEqExpr.
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

//! \brief Creates a binary not-and-expression that represents the negated
//!        conjunction of the given boolean child expressions.
//!
DLL_PUBLIC Expr vc_nandExpr(VC vc, Expr left, Expr right);

//! \brief Creates a binary not-or-expression that represents the negated
//!        disjunction of the given boolean child expressions.
//!
DLL_PUBLIC Expr vc_norExpr(VC vc, Expr left, Expr right);

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

//! \brief Creates a boolean variable named after the application of the
//!        given boolean variable expression to the parameter, e.g. "p(0x3)".
//!        Two applications denote the same variable exactly when the names
//!        match. The parameter must be a constant bit-vector expression.
//!
DLL_PUBLIC Expr vc_paramBoolExpr(VC vc, Expr var, Expr param);

/////////////////////////////////////////////////////////////////////////////
/// ARRAY EXPRESSIONS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns an array-read-expression representing the reading of
//!        the given array's entry of the given index.
//!
//! The array parameter must be of type array, and the index must have the
//! array's index sort: a bitvector for a bitvector-indexed array, a float
//! of the declared format for a float-indexed one, a rounding mode for a
//! RoundingMode-indexed one. The result carries the array's element sort
//! (a read from a float-element array is a float of that format, usable
//! anywhere a float is; a read from a RoundingMode-element array is a
//! rounding mode, pinned to the five legal encodings at solve time).
//!
DLL_PUBLIC Expr vc_readExpr(VC vc, Expr array, Expr index);

//! \brief Returns an array-write-expressions representing the writing of
//!        the given new value into the given array at the given entry index.
//!
//! The array parameter must be of type array; the index must have the
//! array's index sort and newValue the array's element sort, as for
//! vc_readExpr.
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
//! The presentation language has no floating-point syntax. An expression that
//! uses the floating-point theory -- including a RoundingMode -- is refused
//! here rather than printed; use vc_printSMTLIB2.
//!
DLL_PUBLIC void vc_printExpr(VC vc, Expr e);

//! \brief Returns the given expression in the SMT-LIB 2 format.
//!
//! It is the responsibility of the caller to free the returned string.
//!
//! This is the export that understands every sort STP has: bit-vectors,
//! arrays, FloatingPoint and RoundingMode. Prefer it to vc_printExpr, which
//! predates the floating-point theory and refuses it. (vc_printSMTLIB, which
//! returned SMT-LIB 1, has been removed.)
//!
DLL_PUBLIC char* vc_printSMTLIB2(VC vc, Expr e);

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
                                     size_t* len);

//! \brief Prints the counter example after an invalid query to stdout, in the
//!        presentation language.
//!
//! This method should only be called after a query which returns false.
//!
//! The presentation language has no floating-point or rounding-mode syntax, so
//! values of those sorts print as their packed carriers here -- a float as its
//! IEEE bits, a rounding mode as a 5-bit constant. Use
//! vc_printCounterExampleSMTLIB2 to get them at the sort they were declared
//! with.
//!
DLL_PUBLIC void vc_printCounterExample(VC vc);

//! \brief Prints the counter example after an invalid query to stdout, in the
//!        SMT-LIB 2 `(define-fun ...)` form.
//!
//! This method should only be called after a query which returns false.
//!
//! Unlike vc_printCounterExample this states each value at its declared sort:
//! a float as `(fp #b... #b... #b...)` of the right `(_ FloatingPoint eb sb)`,
//! a rounding mode by name. Symbols STP introduced for itself are left out.
//!
DLL_PUBLIC void vc_printCounterExampleSMTLIB2(VC vc);

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
                                           size_t* len,
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
                                               size_t* len);

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
//! For both budgets, -1 means "no limit" and is the only negative value
//! accepted; 0 means a budget of zero, i.e. give up without searching. Any
//! other negative value is rejected as an error.
//!
//! 'timeout_max_time' is a budget for the whole query rather than for each
//! call into the SAT solver, of which a query makes several.
//!
//! Returns ...
//!   0: if 'e' is INVALID
//!   1: if 'e' is VALID
//!   2: if errors occured
//!   3: if the timeout was reached
//!
//! Note: only the cryptominisat and cadical solvers can abandon a search that
//!       is already running. With the other solvers 'timeout_max_time' is
//!       still honoured, but only between calls into the SAT solver, so a
//!       query may overrun the budget by however long a single call takes.
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
//! The value has the sort of 'e': the value of a floating-point term is a
//! floating-point constant of that term's format, not the bitvector of its
//! packed bits. So it can be fed straight back -- vc_eqExpr(vc, e, value) is
//! well sorted, and asserting it pins 'e' to the value.
//!
//! There has to be a model to read. A query must have been answered -- VALID
//! or INVALID, not a timeout or an error -- and it must still be the last
//! thing to have happened: as vc_pop and vc_push document, a counterexample
//! survives vc_pop and is discarded by the next vc_push or vc_query. Called
//! with no model behind it, this reports a nonfatal diagnostic through
//! vc_registerErrorHandler (or stderr) and returns NULL, rather than failing
//! fatally -- as vc_getUninterpretedFunctionValue does for the same class of
//! misuse. It used to answer from the empty counterexample map instead, which
//! invented a value for a bit-vector or a Boolean and was fatal for a float.
//!
//! A constant is the exception, and needs no query behind it: it already is
//! its own value, so there is nothing for it to read out of a model and
//! nothing to invent. That covers a bit-vector constant and the Boolean
//! constants; a symbol, and any term that has to be evaluated to reach a
//! value, needs a model like everything else.
//!
DLL_PUBLIC Expr vc_getCounterExample(VC vc, Expr e);

//! \brief Returns an array from a counter example after an invalid query.
//!
//! The buffer for the array is allocated by STP and returned via the
//! non-null expected out parameters 'outIndices' for the indices, 'outValues'
//! for the values and 'outSize' for the size of the array.
//!
//! As for vc_getCounterExample, each index has the array's index sort and
//! each value its element sort, so an entry can be fed back as
//! vc_readExpr(vc, e, index) and vc_eqExpr with the value.
//!
//! It is the caller's responsibility to free the memory afterwards;
//! vc_deleteCounterExampleArray does so with the allocator that made it.
//!
DLL_PUBLIC void vc_getCounterExampleArray(VC vc, Expr e, Expr** outIndices,
                                          Expr** outValues, int* outSize);

//! \brief Frees a counter example array returned by
//!        vc_getCounterExampleArray.
//!
//! Deletes every entry expression and releases both buffers inside the
//! library, so allocation and deallocation always use the same
//! allocator even when the embedding process links a different one.
//! With a size of zero nothing was allocated and nothing is freed.
//!
DLL_PUBLIC void vc_deleteCounterExampleArray(Expr* indices, Expr* values,
                                             int size);

//! \brief Returns the size of the counter example array,
//!        i.e. the number of variable and array locations
//!        in the counter example.
//!
DLL_PUBLIC int vc_counterexample_size(VC vc);

//! \brief Checkpoints the current context and increases the scope level.
//!
//! Opens a new assertion level: formulas asserted after this call are
//! retracted again by the matching vc_pop. Also discards the previous
//! query's counterexample and derived solver state, since the assertion
//! set is about to change.
//!
//! Symbols are not scoped: an Expr created at any level remains valid --
//! and remains the same variable -- after any number of pops.
//!
DLL_PUBLIC void vc_push(VC vc);

//! \brief Restores the current context to its state at the last checkpoint.
//!
//! Retracts every formula asserted since the matching vc_push. The last
//! query's counterexample is deliberately retained: the idiomatic use of
//! this API brackets each vc_query in push/pop and reads the model
//! afterwards. The counterexample describes the last vc_query (its
//! assertions plus the negated query at that moment) and stays readable
//! until the next vc_push or vc_query discards it.
//! A certified uninterpreted-function application map is intentionally
//! stricter: because it is keyed by the solved stack/block, vc_pop invalidates
//! UF application-value reads even while legacy scalar/array values remain.
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

//! Return a uint64_t from a constant bitvector expressions

//! \brief Returns the associated 64-bit unsigned integer from the given bitvector expression.
//!
//! Panics if the given bitvector cannot be represented by a 'uint64_t'.
//!
DLL_PUBLIC uint64_t getBVUnsignedLongLong(Expr e);

//! \brief Prints the bit string for a a constant bitvector expression to a
//!        buffer allocated by STP that is returned via output parameter 'buf'
//!        alongside its length in 'len'.
//!
//! It is the callers responsibility to free the buffer's memory.
//!
DLL_PUBLIC void vc_printBVBitStringToBuffer(Expr e, char** buf, size_t* len);

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

/////////////////////////////////////////////////////////////////////////////
/// FLOATING POINT OPERATIONS
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns the IEEE-754 floating-point type with `exp_bits` exponent
//!        bits and `sig_bits` significand bits.
//!
//! The significand width INCLUDES the hidden bit, matching SMT-LIB's
//! `(_ FloatingPoint eb sb)`. For example `vc_fpType(vc, 11, 53)` is an IEEE
//! double and `vc_fpType(vc, 8, 24)` an IEEE single. Use it anywhere a type is
//! expected, e.g. `vc_varExpr(vc, "x", vc_fpType(vc, 11, 53))`.
//!
DLL_PUBLIC Type vc_fpType(VC vc, int exp_bits, int sig_bits);

//! \brief The RoundingMode sort, for declaring rounding-mode variables with
//!        vc_varExpr.
//!
//! A variable of this sort ranges over exactly the five modes: vc_varExpr
//! asserts the validity constraint (at the current assertion level, so it
//! scopes with vc_push/vc_pop like any assertion), and
//! vc_printCounterExampleSMTLIB2 prints the variable's value by mode name.
//! (vc_printCounterExample prints the 5-bit carrier: the presentation language
//! has no rounding-mode syntax.) Read it from a model with
//! vc_getCounterExample; the bits are the enum VCRoundingMode encoding.
//! vc_fpRoundingModeVar is a one-call convenience for the same thing.
DLL_PUBLIC Type vc_fpRoundingModeType(VC vc);

//! \brief Returns the exponent width of a floating-point expression, value or
//!        type (0 if `e` is not floating-point).
//!
DLL_PUBLIC int vc_getExpWidth(Expr e);

//! \brief Returns the significand width (including the hidden bit) of a
//!        floating-point expression, value or type (0 if not floating-point).
//!
DLL_PUBLIC int vc_getSigWidth(Expr e);

//! \brief Builds a floating-point constant of format (exp_bits, sig_bits) by
//!        reinterpreting the bits of the bitvector constant `bv`.
//!
//! `bv`'s width must equal exp_bits + sig_bits, laid out most-significant-first
//! as sign : exponent : trailing-significand (the hidden significand bit is not
//! stored). This is the exact, format-generic primitive for floating-point
//! constants; every value -- normals, subnormals, the zeros, the infinities and
//! NaN -- has such a bit pattern. NaN payloads are not preserved: the sort has
//! a single NaN, so every NaN pattern (any sign, any payload) interns as the
//! one canonical quiet NaN -- the same bits every floating-point operation and
//! vc_fpToIEEEBV produce. If exact NaN bits matter, keep them in a bitvector
//! and reinterpret at the boundary.
//!
DLL_PUBLIC Expr vc_fpConstFromBits(VC vc, int exp_bits, int sig_bits, Expr bv);

//! \brief Returns the IEEE floating-point equality `a == b` (fp.eq).
//!
//! True exactly when `a` and `b` are equal as numbers: +0 == -0, and any NaN
//! operand makes it false. For SMT-LIB's '=' -- which keeps +0 and -0
//! distinct and makes every NaN equal to every NaN (payloads are not
//! distinguished) -- use vc_eqExpr instead.
//!
DLL_PUBLIC Expr vc_fpEqExpr(VC vc, Expr a, Expr b);

//! \brief Rounding modes, matching SMT-LIB's RoundingMode. Pass one to
//!        vc_fpRoundingMode to obtain a rounding-mode expression.
//!
enum VCRoundingMode
{
  //! The values are one-hot because they mirror STP's internal rounding-mode
  //! encoding. They are five DISTINCT modes, not flags: combining them with
  //! bitwise-or does not name a mode, and vc_fpRoundingMode rejects it.
  VC_RM_RNE = 1,  //!< round nearest, ties to even  (roundNearestTiesToEven)
  VC_RM_RTP = 2,  //!< round toward positive        (roundTowardPositive)
  VC_RM_RTN = 4,  //!< round toward negative        (roundTowardNegative)
  VC_RM_RTZ = 8,  //!< round toward zero            (roundTowardZero)
  VC_RM_RNA = 16  //!< round nearest, ties to away  (roundNearestTiesToAway)
};

//! \brief Returns a rounding-mode expression for `mode`, to pass as the first
//!        operand of the rounding operations (add, sub, mul, div, fma, sqrt and
//!        roundToIntegral).
//!
DLL_PUBLIC Expr vc_fpRoundingMode(VC vc, enum VCRoundingMode mode);

//! \brief A fresh variable of SMT-LIB's RoundingMode sort, usable wherever
//!        vc_fpRoundingMode's constants are. Shorthand for vc_varExpr over
//!        vc_fpRoundingModeType (see there for the semantics).
//!
//! Do NOT substitute a plain 5-bit variable: nothing would constrain it to
//! denote one of the five modes.
DLL_PUBLIC Expr vc_fpRoundingModeVar(VC vc, const char* name);

// Arithmetic. The result is a floating-point value with the same format as the
// operands (which must all share that format).

//! \brief fp.abs: the magnitude of `f` (clears the sign bit).
DLL_PUBLIC Expr vc_fpAbsExpr(VC vc, Expr f);
//! \brief fp.neg: `f` with its sign bit flipped.
DLL_PUBLIC Expr vc_fpNegExpr(VC vc, Expr f);
//! \brief fp.add of `a` and `b` under rounding mode `rm`.
DLL_PUBLIC Expr vc_fpAddExpr(VC vc, Expr rm, Expr a, Expr b);
//! \brief fp.sub of `a` and `b` under rounding mode `rm`.
DLL_PUBLIC Expr vc_fpSubExpr(VC vc, Expr rm, Expr a, Expr b);
//! \brief fp.mul of `a` and `b` under rounding mode `rm`.
DLL_PUBLIC Expr vc_fpMulExpr(VC vc, Expr rm, Expr a, Expr b);
//! \brief fp.div of `a` by `b` under rounding mode `rm`.
DLL_PUBLIC Expr vc_fpDivExpr(VC vc, Expr rm, Expr a, Expr b);
//! \brief fp.fma under rounding mode `rm`: round(a*b + c).
DLL_PUBLIC Expr vc_fpFMAExpr(VC vc, Expr rm, Expr a, Expr b, Expr c);
//! \brief fp.sqrt of `f` under rounding mode `rm`.
DLL_PUBLIC Expr vc_fpSqrtExpr(VC vc, Expr rm, Expr f);
//! \brief fp.roundToIntegral of `f` under rounding mode `rm`.
DLL_PUBLIC Expr vc_fpRoundToIntegralExpr(VC vc, Expr rm, Expr f);
//! \brief fp.rem: the IEEE remainder of `a` by `b` (exact; no rounding mode).
DLL_PUBLIC Expr vc_fpRemExpr(VC vc, Expr a, Expr b);
//! \brief fp.min of `a` and `b` (no rounding mode).
DLL_PUBLIC Expr vc_fpMinExpr(VC vc, Expr a, Expr b);
//! \brief fp.max of `a` and `b` (no rounding mode).
DLL_PUBLIC Expr vc_fpMaxExpr(VC vc, Expr a, Expr b);

// Predicates. The result is Boolean.

//! \brief fp.lt: ordered less-than (false if either operand is NaN).
DLL_PUBLIC Expr vc_fpLtExpr(VC vc, Expr a, Expr b);
//! \brief fp.leq: ordered less-or-equal (false if either operand is NaN).
DLL_PUBLIC Expr vc_fpLeqExpr(VC vc, Expr a, Expr b);
//! \brief fp.gt: ordered greater-than (false if either operand is NaN).
DLL_PUBLIC Expr vc_fpGtExpr(VC vc, Expr a, Expr b);
//! \brief fp.geq: ordered greater-or-equal (false if either operand is NaN).
DLL_PUBLIC Expr vc_fpGeqExpr(VC vc, Expr a, Expr b);
//! \brief fp.isNormal: true when `f` is a normal number.
DLL_PUBLIC Expr vc_fpIsNormalExpr(VC vc, Expr f);
//! \brief fp.isSubnormal: true when `f` is subnormal.
DLL_PUBLIC Expr vc_fpIsSubnormalExpr(VC vc, Expr f);
//! \brief fp.isZero: true when `f` is +0 or -0.
DLL_PUBLIC Expr vc_fpIsZeroExpr(VC vc, Expr f);
//! \brief fp.isInfinite: true when `f` is +oo or -oo.
DLL_PUBLIC Expr vc_fpIsInfiniteExpr(VC vc, Expr f);
//! \brief fp.isNaN: true when `f` is NaN.
DLL_PUBLIC Expr vc_fpIsNaNExpr(VC vc, Expr f);
//! \brief fp.isNegative: true when `f` is negative (includes -oo and -0).
DLL_PUBLIC Expr vc_fpIsNegativeExpr(VC vc, Expr f);
//! \brief fp.isPositive: true when `f` is positive (includes +oo and +0).
DLL_PUBLIC Expr vc_fpIsPositiveExpr(VC vc, Expr f);

// Special-value constants of a given floating-point type.

//! \brief The NaN of `fpType`.
DLL_PUBLIC Expr vc_fpNaN(VC vc, Type fpType);
//! \brief +oo of `fpType`.
DLL_PUBLIC Expr vc_fpPlusInfinity(VC vc, Type fpType);
//! \brief -oo of `fpType`.
DLL_PUBLIC Expr vc_fpMinusInfinity(VC vc, Type fpType);
//! \brief +0 of `fpType`.
DLL_PUBLIC Expr vc_fpPlusZero(VC vc, Type fpType);
//! \brief -0 of `fpType`.
DLL_PUBLIC Expr vc_fpMinusZero(VC vc, Type fpType);

//! \brief A constant of `target` floating-point type equal to the native
//!        double `d`, rounded under `rm`.
//!
//! `d` is already an IEEE-754 binary64 value, so this reinterprets its bits as
//! a (11,53) float and, when `target` differs, reformats with fp.to_fp under
//! `rm` (exact when `target` is binary64, so `rm` is then irrelevant). Note: a
//! literal such as 0.1 is rounded to the nearest double by the C compiler
//! before it reaches here.
//!
DLL_PUBLIC Expr vc_fpConstFromDouble(VC vc, Type target, Expr rm, double d);
//! \brief As vc_fpConstFromDouble, from a native float (IEEE-754 binary32).
DLL_PUBLIC Expr vc_fpConstFromFloat(VC vc, Type target, Expr rm, float f);

// Conversions.

//! \brief One-argument (_ to_fp eb sb): reinterpret the bits of bitvector `bv`
//!        (whose width must be eb+sb) as a float. No rounding.
DLL_PUBLIC Expr vc_fpToFPFromIEEEBV(VC vc, int eb, int sb, Expr bv);
//! \brief (_ to_fp eb sb) rm f: reformat float `f` to format (eb,sb) under `rm`.
DLL_PUBLIC Expr vc_fpToFPFromFP(VC vc, int eb, int sb, Expr rm, Expr f);
//! \brief (_ to_fp eb sb) rm bv: convert the signed integer in `bv` to a float
//!        of format (eb,sb) under `rm`.
DLL_PUBLIC Expr vc_fpToFPFromSignedBV(VC vc, int eb, int sb, Expr rm, Expr bv);
//! \brief (_ to_fp_unsigned eb sb) rm bv: convert the unsigned integer in `bv`
//!        to a float of format (eb,sb) under `rm`.
DLL_PUBLIC Expr vc_fpToFPFromUnsignedBV(VC vc, int eb, int sb, Expr rm, Expr bv);
//! \brief (_ fp.to_ubv m) rm f: round float `f` to an m-bit unsigned integer
//!        (a bitvector) under `rm`.
DLL_PUBLIC Expr vc_fpToUBVExpr(VC vc, int width, Expr rm, Expr f);
//! \brief (_ fp.to_sbv m) rm f: round float `f` to an m-bit signed integer
//!        (a bitvector) under `rm`.
DLL_PUBLIC Expr vc_fpToSBVExpr(VC vc, int width, Expr rm, Expr f);

//! \brief Reinterpret float `f` as its packed IEEE bits: a bitvector of width
//!        exp_width + sig_width, laid out most-significant-first as
//!        sign : exponent : trailing-significand.
//!
//! The inverse of vc_fpToFPFromIEEEBV. Use vc_bvExtract on the result to pull
//! out the sign, exponent or significand field (e.g. the exponent is bits
//! [sig_width-1 .. sig_width+exp_width-2]). NaN is canonicalised -- the payload
//! is not preserved -- so every NaN yields the same bits.
//!
DLL_PUBLIC Expr vc_fpToIEEEBV(VC vc, Expr f);

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
//!        64-bit unsigned integer value.
//!
//! The 'bitWidth' must be large enough to fully store the given value's bit representation.
//!
DLL_PUBLIC Expr vc_bvConstExprFromLL(VC vc, int bitWidth, uint64_t value);

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
/// BITVECTOR OVERFLOW PREDICATES
///
/// Each of these returns a boolean expression that is true exactly when the
/// corresponding operation on the two given bitvector expressions does not
/// fit in their common bit-width, i.e. when the result of the same operation
/// at that width would wrap.
///
/// The two given bitvector expressions must have the same bit-width.
///
/////////////////////////////////////////////////////////////////////////////

//! \brief Returns a boolean expression that is true when the unsigned addition
//!        '(left + right)' overflows.
//!
DLL_PUBLIC Expr vc_bvUnsignedAddOverflowExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression that is true when the signed addition
//!        '(left + right)' overflows.
//!
DLL_PUBLIC Expr vc_bvSignedAddOverflowExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression that is true when the unsigned
//!        subtraction '(left - right)' overflows.
//!
DLL_PUBLIC Expr vc_bvUnsignedSubOverflowExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression that is true when the signed
//!        subtraction '(left - right)' overflows.
//!
DLL_PUBLIC Expr vc_bvSignedSubOverflowExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression that is true when the unsigned
//!        multiplication '(left * right)' overflows.
//!
DLL_PUBLIC Expr vc_bvUnsignedMulOverflowExpr(VC vc, Expr left, Expr right);

//! \brief Returns a boolean expression that is true when the signed
//!        multiplication '(left * right)' overflows.
//!
DLL_PUBLIC Expr vc_bvSignedMulOverflowExpr(VC vc, Expr left, Expr right);

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

//! \brief Returns a bitvector expression representing the bitwise-not-and
//!        operation '~(a & b)' for the given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width.
//!
DLL_PUBLIC Expr vc_bvNandExpr(VC vc, Expr left, Expr right);

//! \brief Returns a bitvector expression representing the bitwise-not-or
//!        operation '~(a | b)' for the given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width.
//!
DLL_PUBLIC Expr vc_bvNorExpr(VC vc, Expr left, Expr right);

//! \brief Returns a bitvector expression representing the bitwise-not-xor
//!        operation '~(a ^ b)' for the given bitvector expressions.
//!
//! The given bitvector expressions must have the same bit-width.
//!
DLL_PUBLIC Expr vc_bvXnorExpr(VC vc, Expr left, Expr right);

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

//! \brief Returns a bitvector expression of bit-width 'newWidth' that holds the
//!        given child zero-extended, i.e. padded with zeroes in the new
//!        high bits.
//!
//! If 'newWidth' is at most the child's current bit-width then the child is
//! truncated to 'newWidth' instead, matching how 'vc_bvSignExtend' behaves in
//! that case.
//!
//! This function panics if 'newWidth' is not positive.
//!
DLL_PUBLIC Expr vc_bvZeroExtend(VC vc, Expr child, int newWidth);

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

//! \brief Registers the error handler called for fatal STP errors and for
//!        documented nonfatal validation failures such as UF API misuse.
//!
//! The callback is process-global and is invoked synchronously. Passing NULL
//! restores the default reporting path (stderr for nonfatal UF validation).
//!
//! One nonfatal diagnostic reaches it as well: vc_getCounterExample reports a
//! model read with no model behind it this way and then returns NULL, rather
//! than ending the process. A handler must therefore not assume that it is
//! only ever called on the way to abort().
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
//! Only for expressions the caller owns. Do NOT pass expressions returned by
//! the vc_fp* constructors (or the type/true/false constructors): those are
//! owned by the checker and freed by vc_Destroy -- deleting one here frees
//! it twice. Exception: after vc_setFlag(vc, 'u') has enabled UF handle
//! tracking, wrappers constructed subsequently are tracked and may be released
//! explicitly; vc_declareUninterpretedFunction documents this for its borrowed
//! Type arguments.
//!
DLL_PUBLIC void vc_DeleteExpr(Expr e);

//! \brief Returns the whole counterexample from the given validity checker.
//!
DLL_PUBLIC WholeCounterExample vc_getWholeCounterExample(VC vc);

//! \brief Returns the value of the given term expression from the given whole counter example.
//!
//! As for vc_getCounterExample, the value has the sort of 'e' -- a
//! floating-point term's value is a floating-point constant of that term's
//! format. Note that 'e' must be a variable or something the model already
//! records: unlike vc_getCounterExample this does not evaluate a term
//! against the model, and hands an unrecorded term straight back.
//!
DLL_PUBLIC Expr vc_getTermFromCounterExample(VC vc, Expr e,
                                             WholeCounterExample c);

//! \brief Destroys the given whole counter example, freeing all of its associated memory.
//!
DLL_PUBLIC void vc_deleteWholeCounterExample(WholeCounterExample cc);

//! Covers the expression kinds exposed by the public C API. Internal kinds
//! may be represented by their corresponding public kind.
//!
//! Mirrors the internal stp::Kind (generated from lib/AST/ASTKind.kinds) by
//! numeric value: getExprKind is a direct cast, so the enumerators must stay
//! in the same order. static_asserts next to getExprKind's implementation
//! pin the correspondence.
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
  BVUADDO,      //!< Unsigned addition overflow predicate
  BVSADDO,      //!< Signed addition overflow predicate
  BVUMULO,      //!< Unsigned multiplication overflow predicate
  BVSMULO,      //!< Signed multiplication overflow predicate
  BVUSUBO,      //!< Unsigned subtraction overflow predicate
  BVSSUBO,      //!< Signed subtraction overflow predicate
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
  PARAMBOOL, //!< Parameterized boolean expression. No longer created;
             //!< kept so that the later kind values don't change.
  READ,          //!< Array read expression
  WRITE,         //!< Array write expression
  ARRAY,         //!< Array creation expression
  BITVECTOR,     //!< Bitvector creation expression
  BOOLEAN,       //!< Boolean creation expression
  FLOATINGPOINT, //!< Floating point creation expression
  ROUNDINGMODE,  //!< RoundingMode type expression (vc_fpRoundingModeType)
  FP_ABS,
  FP_NEG,
  FP_ADD,
  FP_SUB,
  FP_MUL,
  FP_DIV,
  FP_FMA,
  FP_SQRT,
  FP_REM,
  FP_ROUNDTOINTEGRAL,
  FP_MIN,
  FP_MAX,
  FP_TOFP,
  FP_TOFP_SIGNED,
  FP_TOFP_UNSIGNED,
  FP_TO_UBV,
  FP_TO_SBV,
  FP_TO_IEEE_BV,
  FP_LEQ,
  FP_LT,
  FP_GEQ,
  FP_GT,
  FP_EQ,
  FP_ISNORMAL,
  FP_ISSUBNORMAL,
  FP_ISZERO,
  FP_ISINFINITE,
  FP_ISNAN,
  FP_ISNEGATIVE,
  FP_ISPOSITIVE,
  FP_SMT_EQ, //!< SMT-LIB '=' over floats: +0 and -0 distinct, all NaNs equal.
  //! Durable uninterpreted-function application. ARRAY_EQ is the unexposed
  //! internal kind between FP_SMT_EQ and UF_APPLY.
  UF_APPLY = FP_SMT_EQ + 2,
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
//! FLOATINGPOINT_TYPE and ROUNDINGMODE_TYPE are appended after the legacy
//! values so that values compiled into older clients stay valid. This public
//! enum describes source sorts; STP's internal carrier enum has no separate
//! RoundingMode entry.
enum type_t
{
  BOOLEAN_TYPE = 0,
  BITVECTOR_TYPE,
  ARRAY_TYPE,
  UNKNOWN_TYPE,
  FLOATINGPOINT_TYPE,
  ROUNDINGMODE_TYPE
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
DLL_PUBLIC uint64_t getExprID(Expr ex);

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
DLL_PUBLIC bool vc_supportsMinisat(VC vc);

//! \brief Sets underlying SAT solver to minisat
//!
DLL_PUBLIC bool vc_useMinisat(VC vc);

//! \brief Checks if underlying SAT solver is minisat
//!
DLL_PUBLIC bool vc_isUsingMinisat(VC vc);

//! \brief Checks if STP was compiled with support for simplifying minisat
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

//! \brief Checks if STP was compiled with support for cadical
//!
DLL_PUBLIC bool vc_supportsCadical(VC vc);

//! \brief Sets underlying SAT solver to cadical
//!
DLL_PUBLIC bool vc_useCadical(VC vc);

//! \brief Checks if underlying SAT solver is cadical
//!
DLL_PUBLIC bool vc_isUsingCadical(VC vc);

#ifdef __cplusplus
}
#endif

#undef DLL_PUBLIC // Undefine internal macro to prevent it from leaking into the API.
#undef DLL_LOCAL // Undefine internal macro to prevent it from leaking into the API.

#undef _CVCL_DEFAULT_ARG // Undefine macro to not pollute global macro namespace!

#endif // _cvcl__include__c_interface_h_
