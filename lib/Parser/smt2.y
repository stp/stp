/* %define api.pure full */
/*%lex-param {void *scanner}
%parse-param {void *scanner}
*/

%define parse.error verbose

%{
  /********************************************************************
   * AUTHORS:  Trevor Hansen
   *
   * BEGIN DATE: May, 2010
   *
   * This file is modified version of the STP's smtlib.y file. Please
   * see CVCL license below
  ********************************************************************/

  /********************************************************************
   * AUTHORS: Vijay Ganesh, Trevor Hansen
   *
   * BEGIN DATE: July, 2006
   *
   * This file is modified version of the CVCL's smtlib.y file. Please
   * see CVCL license below
  ********************************************************************/

  /********************************************************************
   *
   * \file smtlib.y
   *
   * Author: Sergey Berezin, Clark Barrett
   *
   * Created: Apr 30 2005
   *
   * <hr>
   * Copyright (C) 2004 by the Board of Trustees of Leland Stanford
   * Junior University and by New York University.
   *
   * License to use, copy, modify, sell and/or distribute this software
   * and its documentation for any purpose is hereby granted without
   * royalty, subject to the terms and conditions defined in the \ref
   * LICENSE file provided with this distribution.  In particular:
   *
   * - The above copyright notice and this permission notice must appear
   * in all copies of the software and related documentation.
   *
   * - THE SOFTWARE IS PROVIDED "AS-IS", WITHOUT ANY WARRANTIES,
   * EXPRESSED OR IMPLIED.  USE IT AT YOUR OWN RISK.
   *
   * <hr>
  ********************************************************************/

#include "stp/Parser/SMT2Attribute.h"
#include "stp/cpp_interface.h"
#include "stp/Parser/LetMgr.h"
#include "stp/Parser/parser.h"
#include "stp/Parser/ParserUnwind.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/FloatBlaster/DecimalLiteral.h"
#include "parsesmt2.tab.h"
#include "smt2_flex_header.h"
#include <sstream>
#include <string>

#include <cctype>
#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <limits>
#include <string>
#include <vector>

  using std::cout;
  using std::cerr;
  using std::endl;

  using stp::UNDEFINED;    //!< An undefined expression.
  using stp::SYMBOL;       //!< Named expression (or variable)
  using stp::BVCONST;      //!< Bitvector constant expression
  using stp::BVNOT;        //!< Bitvector bitwise-not
  using stp::BVCONCAT;     //!< Bitvector concatenation
  using stp::BVOR;         //!< Bitvector bitwise-or
  using stp::BVAND;        //!< Bitvector bitwise-and
  using stp::BVXOR;        //!< Bitvector bitwise-xor
  using stp::BVNAND;       //!< Bitvector bitwise not-and; OR nand (TODO: does this still exist?)
  using stp::BVNOR;        //!< Bitvector bitwise not-or; OR nor (TODO: does this still exist?)
  using stp::BVXNOR;       //!< Bitvector bitwise not-xor; OR xnor (TODO: does this still exist?)
  using stp::BVEXTRACT;    //!< Bitvector extraction
  using stp::BVLEFTSHIFT;  //!< Bitvector left-shift
  using stp::BVRIGHTSHIFT; //!< Bitvector right-right
  using stp::BVSRSHIFT;    //!< Bitvector signed right-shift
  using stp::BVPLUS;       //!< Bitvector addition
  using stp::BVSUB;        //!< Bitvector subtraction
  using stp::BVUMINUS;     //!< Bitvector unary minus; OR negate expression
  using stp::BVMULT;       //!< Bitvector multiplication
  using stp::BVDIV;        //!< Bitvector division
  using stp::BVMOD;        //!< Bitvector modulo operation
  using stp::SBVDIV;       //!< Signed bitvector division
  using stp::SBVREM;       //!< Signed bitvector remainder
  using stp::SBVMOD;       //!< Signed bitvector modulo operation
  using stp::BVSX;         //!< Bitvector signed extend
  using stp::BVZX;         //!< Bitvector zero extend
  using stp::ITE;          //!< If-then-else
  using stp::BOOLEXTRACT;  //!< Bitvector boolean extraction
  using stp::BVLT;         //!< Bitvector less-than
  using stp::BVLE;         //!< Bitvector less-equals
  using stp::BVGT;         //!< Bitvector greater-than
  using stp::BVGE;         //!< Bitvector greater-equals
  using stp::BVSLT;        //!< Signed bitvector less-than
  using stp::BVSLE;        //!< Signed bitvector less-equals
  using stp::BVSGT;        //!< Signed bitvector greater-than
  using stp::BVSGE;        //!< Signed bitvector greater-equals
  using stp::BVUADDO;      //!< Unsigned addition overflow predicate
  using stp::BVSADDO;      //!< Signed addition overflow predicate
  using stp::BVUMULO;      //!< Unsigned multiplication overflow predicate
  using stp::BVSMULO;      //!< Signed multiplication overflow predicate
  using stp::BVUSUBO;      //!< Unsigned subtraction overflow predicate
  using stp::BVSSUBO;      //!< Signed subtraction overflow predicate
  using stp::EQ;           //!< Equality comparator
  using stp::FALSE;        //!< Constant false boolean expression
  using stp::TRUE;         //!< Constant true boolean expression
  using stp::NOT;          //!< Logical-not boolean expression
  using stp::AND;          //!< Logical-and boolean expression
  using stp::OR;           //!< Logical-or boolean expression
  using stp::NAND;         //!< Logical-not-and boolean expression (TODO: Does this still exist?)
  using stp::NOR;          //!< Logical-not-or boolean expression (TODO: Does this still exist?)
  using stp::XOR;          //!< Logical-xor (either-or) boolean expression
  using stp::IFF;          //!< If-and-only-if boolean expression
  using stp::IMPLIES;      //!< Implication boolean expression
  using stp::READ;         //!< Array read expression
  using stp::WRITE;        //!< Array write expression

  using stp::FP_ABS;
  using stp::FP_NEG;
  using stp::FP_ADD;
  using stp::FP_SUB;
  using stp::FP_MUL;
  using stp::FP_DIV;
  using stp::FP_FMA;
  using stp::FP_SQRT;
  using stp::FP_REM;
  using stp::FP_ROUNDTOINTEGRAL;
  using stp::FP_MIN;
  using stp::FP_MAX;
  using stp::FP_TOFP;
  using stp::FP_TOFP_SIGNED;
  using stp::FP_TOFP_UNSIGNED;
  using stp::FP_TO_UBV;
  using stp::FP_TO_SBV;
  using stp::FP_LEQ;
  using stp::FP_LT;
  using stp::FP_GEQ;
  using stp::FP_GT;
  using stp::FP_EQ;
  using stp::FP_ISNORMAL;
  using stp::FP_ISSUBNORMAL;
  using stp::FP_ISZERO;
  using stp::FP_ISINFINITE;
  using stp::FP_ISNAN;
  using stp::FP_ISNEGATIVE;
  using stp::FP_ISPOSITIVE;
  using stp::FP_SMT_EQ;

  using stp::symbolic_fp::rounding_modes::ROUND_NEAREST_TIES_TO_EVEN;
  using stp::symbolic_fp::rounding_modes::ROUND_TOWARD_POSITIVE;
  using stp::symbolic_fp::rounding_modes::ROUND_TOWARD_NEGATIVE;
  using stp::symbolic_fp::rounding_modes::ROUND_TOWARD_ZERO;
  using stp::symbolic_fp::rounding_modes::ROUND_NEAREST_TIES_TO_AWAY;

  using stp::NOT_DECLARED;
  using stp::TO_BE_SATISFIABLE;
  using stp::TO_BE_UNSATISFIABLE;
  using stp::TO_BE_UNKNOWN;

  using stp::BOOLEAN_TYPE;
  using stp::BITVECTOR_TYPE;
  using stp::ARRAY_TYPE;
  using stp::FLOATINGPOINT_TYPE;
  using stp::UNKNOWN_TYPE;

  using stp::SOLVER_INVALID;
  using stp::SOLVER_VALID;
  using stp::SOLVER_UNDECIDED;
  using stp::SOLVER_UNKNOWN;
  using stp::SOLVER_ERROR;
  using stp::SOLVER_UNSATISFIABLE;
  using stp::SOLVER_SATISFIABLE;

  extern char* smt2text;
  extern int smt2lineno;
  extern bool stringOnly;

  // Whether a token is all digits and out of range for the unsigned that
  // every numeric position in this grammar but a real magnitude wants. The
  // lexer made the same call to choose the token; recomputing it keeps the
  // diagnostic a function of the text it is reporting.
  static bool numeralTooLargeForIndex(const char* text)
  {
    if (text == nullptr || *text == '\0')
      return false;
    for (const char* p = text; *p != '\0'; p++)
      if (*p < '0' || *p > '9')
        return false;
    errno = 0;
    const unsigned long value = strtoul(text, nullptr, 10);
    return errno == ERANGE ||
           value > std::numeric_limits<unsigned>::max();
  }

  // The diagnostic, built once. It is the body of the SMT-LIB (error ...)
  // response on stdout and also what the fatal path reports -- which used
  // to be the empty string, so a caller told of the failure learned that
  // parsing had failed but never why, and the command line printed two
  // labelled blank lines after a perfectly good response.
  static std::string smt2_diagnostic(const char *s)
  {
    std::ostringstream o;
    o << "syntax error: line " << smt2lineno << " " << s
      << "  token: " << smt2text;
    // Outside an FP logic a floating-point name is not an unknown name, it is
    // a disabled keyword -- and every message that can land here says the
    // opposite, from bison's "unexpected STRING_TOK" to the sort rules'
    // "unknown sort (not built in...)". Nothing else in the output points at
    // the missing set-logic, so this does.
    if (stp::SMT2FpKeywordNeedsLogic(smt2text))
      o << "  hint: " << smt2text << " is a floating-point name; those are "
           "recognised only after a floating-point (set-logic): QF_FP, "
           "QF_BVFP, QF_ABVFP, QF_UFFP, QF_UFBVFP, QF_AUFBVFP or one of "
           "their LRA variants";
    // Likewise, a numeral the parser would not take is not a malformed
    // numeral: it is one too large to be the index, width or count that the
    // position calls for. Without this the report is bison's token name.
    if (numeralTooLargeForIndex(smt2text))
      o << "  hint: " << smt2text << " does not fit an unsigned, so it cannot "
           "be an index, a width or a count; only a real literal may be this "
           "large";
    return o.str();
  }

  // SMT-LIB spells a logic as an optional HO_ and QF_ prefix followed by the
  // theory abbreviations it combines, written in a fixed order, and closed by
  // at most one arithmetic fragment. Recognising that shape -- rather than
  // carrying the standard's catalogue of names, which gains a division at a
  // time -- separates the two mistakes a set-logic can make: naming a logic
  // STP does not decide, and naming something that is not a logic at all.
  // Both are refused, so an imprecise call here costs a word in a diagnostic
  // and nothing else.
  static bool consumeLogicPart(const std::string& name, size_t& at,
                               const char* part)
  {
    const size_t length = strlen(part);
    if (name.compare(at, length, part) != 0)
      return false;
    at += length;
    return true;
  }

  static bool isSMTLIBLogicName(const std::string& name)
  {
    size_t at = 0;
    consumeLogicPart(name, at, "HO_");
    consumeLogicPart(name, at, "QF_");
    const size_t afterPrefixes = at;

    if (consumeLogicPart(name, at, "ALL"))
      return at == name.size();

    // AX first: the array logic with extensionality is a name in its own
    // right, not arrays followed by a theory called X.
    if (!consumeLogicPart(name, at, "AX"))
      consumeLogicPart(name, at, "A");
    consumeLogicPart(name, at, "UF");
    consumeLogicPart(name, at, "BV");
    consumeLogicPart(name, at, "FP");
    consumeLogicPart(name, at, "DT");
    consumeLogicPart(name, at, "FF");
    consumeLogicPart(name, at, "S");

    // Longest match first: the mixed fragments begin with the same letters as
    // the single-sort ones they combine.
    static const char* const arithmetics[] = {"LIRA", "NIRA", "LIA", "LRA",
                                              "NIA",  "NRA",  "IDL", "RDL"};
    for (const char* fragment : arithmetics)
      if (consumeLogicPart(name, at, fragment))
        break;

    // A logic is the prefixes plus at least one theory, with nothing left
    // over: "QF_" alone names nothing, and "QF_BVX" is not "QF_BV".
    return at > afterPrefixes && at == name.size();
  }

  // How the set-logic test below reads out loud; a name added there belongs
  // here too. The UF+FP aliases are deliberately absent: they are alternative
  // spellings of names already listed, and a caller reading a refusal is
  // looking for a fragment STP has, not for a synonym of one.
  static const char* supportedLogicsPhrase()
  {
    return "ALL (the supported quantifier-free fragments), QF_BV, QF_ABV, QF_AX, QF_UF, QF_UFBV, QF_AUFBV, QF_LRA, QF_UFLRA, "
           "QF_AUFLRA, the floating-point logics QF_FP, QF_BVFP, QF_ABVFP, "
           "QF_UFFP, QF_UFBVFP, QF_AUFBVFP, and their LRA variants";
  }

  void reportRedeclaredName();

  int yyerror(const char *s) {
    if (stp::SMT2DeclassifiedNamePending())
    {
      // Bison ran past a declassified declare-fun name and hit a syntax
      // error before any var_decl action consumed the record: a malformed
      // zero-arity declaration shape. The legacy grammar died AT the name,
      // so the name-position error is the whole pinned response, whatever
      // `s` says. Return rather than throw: the grammar has no error
      // productions, so bison now abandons the parse itself and reclaims
      // its stack through the %destructor rules. (Nothing but bison calls
      // yyerror while a record is pending: only sort rules sit between the
      // name and the action, and those fail through fatal_yyerror below;
      // the lexer's illegal-character rule handles its own case.)
      reportRedeclaredName();
      return 1;
    }
    stp::GlobalParserInterface->rejectCurrentCommand(smt2_diagnostic(s));
    return 1;
  }

  int fatal_yyerror(const char *s) 
  {
    if (stp::SMT2DeclassifiedNamePending())
    {
      // A sort rule inside a zero-arity declaration over a known name is
      // rejecting a width or format. The legacy grammar never reached it:
      // it died at the name. Print that error alone and unwind to
      // SMT2Parse() -- neither the sort's own message nor FatalError's exit.
      reportRedeclaredName();
      throw stp::DeclassifiedNameAbandon();
    }
    yyerror(s);
    // The grammar's own refusal ends the parse, not the process: unwind to
    // SMT2Parse(), which answers failure, and the caller decides -- the
    // command line exits with the diagnostic, a library caller gets a parse
    // error with its assertion stack put back. The other channels (the
    // "Fatal Error:" line on stderr and the observer) keep their report;
    // under the 3.x API the diagnostic is also the error's own text.
    stp::ReportFatalError(smt2_diagnostic(s).c_str());
    throw stp::ParseAbandon();
  }

  // STP's lowering layer intentionally treats a float's packed
  // representation as bits, but that is an internal implementation detail.
  // At the SMT-LIB boundary a BV operator accepts only a BitVec-sorted
  // term; no operator exposes a float's representation (fp.to_ieee_bv is
  // not implemented -- and note it is underspecified for NaN, whose
  // payload nothing else in the language can observe either).
  void checkBitVectorTerm(const ASTNode& n)
  {
    if (n.GetSourceSort().kind() != stp::SourceSort::Kind::BitVector)
      fatal_yyerror("bitvector operator requires bitvector operands");
  }

  void checkBitVectorTerms(const ASTVec& terms)
  {
    for (const ASTNode& term : terms)
      checkBitVectorTerm(term);
  }

  // SMT-LIB's bit-vector operators take operands of one width. The node
  // factory builds over two regardless -- some operators were then answered
  // under no defined semantics, others aborted the process in a check -- so
  // the grammar refuses it, as it refuses an operand that is no bit-vector.
  void checkSameWidth(const ASTNode& a, const ASTNode& b)
  {
    if (a.GetValueWidth() != b.GetValueWidth())
    {
      const std::string message = "bitvector operands of different widths (" +
                                  std::to_string(a.GetValueWidth()) + " and " +
                                  std::to_string(b.GetValueWidth()) + ")";
      fatal_yyerror(message.c_str());
    }
  }

  void checkSameWidths(const ASTVec& terms)
  {
    for (size_t i = 1; i < terms.size(); ++i)
      checkSameWidth(terms[0], terms[i]);
  }

  void checkSameSourceSort(const ASTVec& terms, const char* message)
  {
    if (terms.empty())
      return;
    const stp::SourceSort expected = terms[0].GetSourceSort();
    if (!expected.isKnown())
      fatal_yyerror(message);
    for (size_t i = 1; i < terms.size(); ++i)
    {
      if (terms[i].GetSourceSort() != expected)
      {
        std::ostringstream diagnostic;
        diagnostic << message << ": observed (";
        for (size_t j = 0; j < terms.size(); ++j)
        {
          if (j != 0)
            diagnostic << ", ";
          diagnostic << terms[j].GetSourceSort();
        }
        diagnostic << ')';
        fatal_yyerror(diagnostic.str().c_str());
      }
    }
  }

  // (distinct t1 ... tn) is unsatisfiable as soon as n exceeds the number of
  // values its operands' sort has: n terms cannot take n different values out
  // of fewer than n. That is pigeonhole. Although distinct now stays native
  // through query assembly, unmatched instances are eventually lowered to
  // C(n, 2) disequalities, whose CDCL cost is out of all proportion to how the
  // source reads. Measured on this tree: sixteen operands over (_ BitVec 4)
  // answer in 0.02s, seventeen take over seven minutes. The cliff is one
  // operand wide, and n is already known here.
  //
  // Only a sort whose value count is exact is guarded, which here means Bool
  // and the bit-vectors.
  //
  // FloatingPoint is deliberately left out. Its equality in these rules is
  // FP_SMT_EQ, which identifies patterns the packed representation keeps apart
  // (every NaN is one value), so the number of distinguishable values is below
  // 2^width rather than equal to it; folding at n > 2^width would still be
  // sound, merely weaker than it looks. RoundingMode is left out too, although
  // its five values are exact: folding it would retire what
  // fp-tests/array-rm-element-only-five-modes.smt2 exists to check, namely
  // that a six-operand RoundingMode distinct comes out unsat through the
  // solver. Arrays have no finite count worth computing.
  bool distinctExceedsCardinality(const stp::SourceSort& sort, size_t operands)
  {
    typedef stp::SourceSort::Kind SortKind;
    if (sort.kind() == SortKind::Bool)
      return operands > 2;
    // Only a bit-vector's width is its cardinality. A sort declared by
    // declare-sort is unbounded -- (distinct s0 .. s16) over it is satisfiable
    // in a seventeen-element domain however narrow its carrier is -- and it is
    // excluded here by having a kind of its own, so this needs no side channel
    // to ask about it.
    if (sort.kind() != SortKind::BitVector)
      return false;
    const unsigned width = sort.bitVectorWidth();
    // 2^64 operands cannot be written down, so a wide sort is never exceeded
    // and the shift that would overflow is never taken.
    if (width >= 64)
      return false;
    return static_cast<uint64_t>(operands) > (static_cast<uint64_t>(1) << width);
  }

  ASTNode* createNode(Kind k, ASTVec*& c)
  {
    if (c->size() < 2)
    {
      // Abandon the command the way fatal_yyerror's declassified path does:
      // SMT2Parse() turns the unwind into a failed parse, so a library caller
      // (the 3.x API's parse_term) sees a PARSE error rather than exit(1).
      yyerror("Must be >=2 operands.");
      stp::releaseParserValue(c);
      throw stp::DeclassifiedNameAbandon();
    }
   ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(k, *c));
   stp::releaseParserValue(c);
   return n;
   }

  static std::string unsupportedUFDomainSort(
      const std::string& name, const stp::parsed_uf_sort& sort,
      const size_t argument)
  {
    std::string diagnostic =
        "uninterpreted functions: unsupported domain sort " + sort.spelling +
        " at argument " + std::to_string(argument) + " of " + name;
    diagnostic += sort.known
                      ? " (" + std::string(
                            stp::UFSignature::supportedSortsPhrase()) + ")"
                      : " (unknown; " + std::string(
                            stp::UFSignature::supportedSortsPhrase()) + ")";
    return diagnostic;
  }

  static std::string unsupportedUFResultSort(
      const std::string& name, const stp::parsed_uf_sort& sort)
  {
    std::string diagnostic =
        "uninterpreted functions: unsupported result sort " + sort.spelling +
        " of " + name;
    diagnostic += sort.known
                      ? " (" + std::string(
                            stp::UFSignature::supportedSortsPhrase()) + ")"
                      : " (unknown; " + std::string(
                            stp::UFSignature::supportedSortsPhrase()) + ")";
    return diagnostic;
  }

  // Whether the decimal `digits` of (_ bvN w) fits `width` bits. The value is
  // built at a width that always holds it (four bits per digit), and its
  // highest set bit compared against the width; the engine's constructor
  // treats an overflow as fatal, so the grammar asks first.
  static bool decimalFitsWidth(const std::string& digits, unsigned width)
  {
    unsigned wide = 4u * static_cast<unsigned>(digits.size()) + 4u;
    if (wide < width)
      wide = width;
    stp::CBV bv = CONSTANTBV::BitVector_Create(wide, true);
    const CONSTANTBV::ErrCode code =
        CONSTANTBV::BitVector_from_Dec(bv, (unsigned char*)digits.c_str());
    const bool fits = code == CONSTANTBV::ErrCode_Ok &&
                      CONSTANTBV::Set_Max(bv) < static_cast<signed long>(width);
    CONSTANTBV::BitVector_Destroy(bv);
    return fits;
  }

  static ASTNode* applyParsedUF(const stp::UFDecl* declaration,
                                const ASTVec& actuals)
  {
    std::string diagnostic;
    ASTNode application =
        stp::GlobalParserInterface->applyUninterpretedFunction(
            declaration, actuals, &diagnostic);
    if (application.GetKind() == UNDEFINED)
      stp::GlobalParserInterface->refuseCurrentCommand(diagnostic);
    return stp::GlobalParserInterface->newNode(application);
  }

  // The zero-arity var_decl actions: a declassified declare-fun name means
  // the legacy grammar rejected this declaration AT the name, so replicate
  // that error and abandon. YYABORT does not reclaim the aborting rule's own
  // right-hand side, so the action releases what it owns first (see
  // "Cleanup: popping" in the generated parser).
#define ABANDON_IF_REDECLARED_ZERO_ARITY(release)                            \
  do                                                                        \
  {                                                                         \
    if (stp::SMT2DeclassifiedNamePending())                                 \
    {                                                                       \
      reportRedeclaredName();                                               \
      release;                                                              \
      YYABORT;                                                              \
    }                                                                       \
  } while (0)

  // Returns only when the name is free to declare; a collision ends the
  // session, as every other rejection in this frontend now does.
  static void requireFreeTopLevelDeclarationName(const std::string& name)
  {
    // Preserve the pinned frontend byte-for-byte when uninterpreted-function
    // support is disabled. The additional shared-namespace check exists only
    // because an enabled UFDecl registry is otherwise invisible to the legacy
    // symbol/function tables.
    if (!stp::GlobalParserInterface->getUserFlags()
             .enable_uninterpreted_functions)
      return;
    std::string diagnostic;
    if (stp::GlobalParserInterface->validateTopLevelDeclarationName(
            name, &diagnostic))
      return;
    stp::GlobalParserInterface->refuseCurrentCommand(diagnostic);
  }

  ASTNode* createNode(Kind k, ASTNode*& c0, ASTNode*& c1)
  {
    // Every binary call to this overload is a BV predicate/overflow
    // production. Boolean connectives use the vector overload.
    checkBitVectorTerm(*c0);
    checkBitVectorTerm(*c1);
    checkSameWidth(*c0, *c1);
    ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateNode(k, *c0, *c1));
    stp::releaseParserValue(c0);
    stp::releaseParserValue(c1);
    return n;
  }

  // Stamp an SMT-LIB floating-point format onto a node. Floats are carried as
  // their packed bit pattern, so the value width is the total width and the
  // exponent/significand widths record how to unpack it.
  //
  // Through withFormat, which stamps only where the stamp is both needed and
  // legal. The factory folds floating-point identities as the term is built --
  // (fp.min x x) is x, (fp.mul rm x 1.0) is x -- so `n` may be an operand that
  // already carries this format and whose kind is not a floating-point one at
  // all (an ite, an array read, a symbol, a constant). Stamping one of those
  // is at best redundant and, on a bitvector-kind interior node, forbidden:
  // nodes are hash-consed and the format is per-node state, so it would retype
  // every other use of the same bits (SetExpWidth asserts on it).
  void setFPFormat(ASTNode* n, unsigned int exp_width, unsigned int sig_width)
  {
    *n = stp::FloatBlaster::withFormat(stp::GlobalParserBM, *n, exp_width,
                                       sig_width);
    assert(n->GetType() == FLOATINGPOINT_TYPE);
  }

  // The rounding-mode argument of a floating-point operation.
  //
  // Testing the carrier -- "a 5-bit bitvector" -- is not the same test.
  // SMT-LIB's RoundingMode has five values and the carrier thirty-two, and
  // symfpu's roundingDecision falls through to truncate, overflowing to the
  // maximum and underflowing to the smallest subnormal, when every mode
  // equality comes out false. That is a sixth mode, in no standard, and an
  // input that reached it was answered rather than refused.
  //
  // BVTypeCheck still asks only about the carrier: it runs over nodes STP
  // builds for itself as well as ones the input names, including the
  // rebuilt operations of model evaluation, whose rounding mode may be a
  // model value for a read the solve never constrained. This is the check
  // for what the input asks for.
  void checkRoundingMode(ASTNode* rm)
  {
    if (rm->GetSourceSort().kind() != stp::SourceSort::Kind::RoundingMode)
    {
      fatal_yyerror("expected a rounding mode.");
    }
  }

  // Source-sort checks for select/store.  The central BV type checker sees
  // only the packed carrier widths, while floating-point and RoundingMode
  // index/element sorts are recorded by STPMgr.  Enforce those richer sorts
  // before constructing a READ/WRITE; FpTotalise's later canonicalisation is
  // an encoding step, not an implicit source-language coercion.
  void checkArrayIndexSort(const ASTNode& array, const ASTNode& index)
  {
    const stp::SourceSort array_sort = array.GetSourceSort();
    if (array_sort.kind() != stp::SourceSort::Kind::Array)
      fatal_yyerror("select/store expects an array as its first argument");
    if (index.GetSourceSort() == array_sort.index())
      return;

    if (array_sort.index().kind() == stp::SourceSort::Kind::FloatingPoint)
    {
      fatal_yyerror("array index is not a float of the declared format");
    }
    if (array_sort.index().kind() == stp::SourceSort::Kind::RoundingMode)
    {
      fatal_yyerror("array index is not of sort RoundingMode");
    }
    if (array_sort.index().kind() ==
        stp::SourceSort::Kind::Uninterpreted)
    {
      fatal_yyerror("array index is not of the declared sort");
    }
    fatal_yyerror("array index is not of the declared bitvector sort");
  }

  void checkArrayValueSort(const ASTNode& array, const ASTNode& value)
  {
    const stp::SourceSort array_sort = array.GetSourceSort();
    if (array_sort.kind() != stp::SourceSort::Kind::Array)
      fatal_yyerror("store expects an array as its first argument");
    if (value.GetSourceSort() == array_sort.element())
      return;

    if (array_sort.element().kind() ==
        stp::SourceSort::Kind::FloatingPoint)
    {
      fatal_yyerror("stored value is not a float of the declared format");
    }
    if (array_sort.element().kind() == stp::SourceSort::Kind::RoundingMode)
    {
      fatal_yyerror("stored value is not of sort RoundingMode");
    }
    if (array_sort.element().kind() ==
        stp::SourceSort::Kind::Uninterpreted)
    {
      fatal_yyerror("stored value is not of the declared sort");
    }
    fatal_yyerror("stored value is not of the declared bitvector sort");
  }

  // fp.add/fp.sub/fp.mul/fp.div. Each is ternary -- the rounding mode is
  // child 0, matching the arity declared in ASTKind.kinds -- so that the
  // blaster rounds as the input asked rather than assuming RNE.
  // The rounding-mode argument is taken as a plain an_term rather than an
  // an_rounding_mode: an_term already derives an_rounding_mode, so using the
  // narrower nonterminal here makes the position ambiguous and LALR resolves
  // it by swallowing the rounding mode as the first operand. Checking the
  // rounding mode here (and again in BVTypeCheck) costs nothing by comparison.
  ASTNode* createFPArith(Kind k, ASTNode*& rm, ASTNode*& lhs, ASTNode*& rhs)
  {
    checkRoundingMode(rm);

    if (lhs->GetSourceSort().kind() !=
            stp::SourceSort::Kind::FloatingPoint ||
        rhs->GetSourceSort().kind() !=
            stp::SourceSort::Kind::FloatingPoint)
    {
      fatal_yyerror("arguments to a floating-point operation must be floats.");
    }

    if (lhs->GetExpWidth() != rhs->GetExpWidth() ||
        lhs->GetSigWidth() != rhs->GetSigWidth())
    {
      fatal_yyerror("floating-point operands must have the same format.");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(k, lhs->GetValueWidth(),
                                                   *rm, *lhs, *rhs));
    setFPFormat(n, lhs->GetExpWidth(), lhs->GetSigWidth());
    stp::releaseParserValue(rm);
    stp::releaseParserValue(lhs);
    stp::releaseParserValue(rhs);
    return n;
  }

  // fp.leq/fp.lt/fp.geq/fp.gt. These are chainable in SMT-LIB, so (fp.lt x y z)
  // means (and (fp.lt x y) (fp.lt y z)).
  ASTNode* createFPChain(Kind k, ASTVec*& terms, const char* name)
  {
    if (terms->size() < 2)
    {
      std::string msg("too few arguments to ");
      msg += name;
      msg += ".";
      fatal_yyerror(msg.c_str());
    }

    for (size_t i = 0; i < terms->size(); i++)
    {
      if ((*terms)[i].GetSourceSort().kind() !=
          stp::SourceSort::Kind::FloatingPoint)
      {
        std::string msg("arguments to ");
        msg += name;
        msg += " must be floats.";
        fatal_yyerror(msg.c_str());
      }
      if ((*terms)[i].GetExpWidth() != (*terms)[0].GetExpWidth() ||
          (*terms)[i].GetSigWidth() != (*terms)[0].GetSigWidth())
      {
        std::string msg("arguments to ");
        msg += name;
        msg += " must have the same format.";
        fatal_yyerror(msg.c_str());
      }
    }

    ASTNode* n;
    if (terms->size() == 2)
    {
      n = stp::GlobalParserInterface->newNode(
          stp::GlobalParserInterface->CreateNode(k, (*terms)[0], (*terms)[1]));
    }
    else
    {
      ASTVec result;
      result.reserve(terms->size() - 1);
      for (size_t i = 1; i < terms->size(); i++)
      {
        result.push_back(stp::GlobalParserInterface->CreateNode(
            k, (*terms)[i - 1], (*terms)[i]));
      }
      n = stp::GlobalParserInterface->newNode(
          stp::GlobalParserInterface->CreateNode(AND, result));
    }
    stp::releaseParserValue(terms);
    return n;
  }

  // fp.rem/fp.min/fp.max: two floats of the same format in, one out. Unlike
  // fp.add and friends these take no rounding mode.
  ASTNode* createFPBinary(Kind k, ASTNode*& lhs, ASTNode*& rhs)
  {
    if (lhs->GetSourceSort().kind() !=
            stp::SourceSort::Kind::FloatingPoint ||
        rhs->GetSourceSort().kind() !=
            stp::SourceSort::Kind::FloatingPoint)
    {
      fatal_yyerror("arguments to a floating-point operation must be floats.");
    }

    if (lhs->GetExpWidth() != rhs->GetExpWidth() ||
        lhs->GetSigWidth() != rhs->GetSigWidth())
    {
      fatal_yyerror("floating-point operands must have the same format.");
    }

    // Refuse fp.rem where its circuit cannot be built (found by murxla as a
    // stack-overflow SIGSEGV at Float128): the unrolling is exponential in
    // the exponent width. Refused here, with the numbers, rather than deep
    // in the blaster.
    if (k == FP_REM && !stp::FloatBlaster::remSupported(lhs->GetExpWidth(),
                                                        lhs->GetSigWidth()))
    {
      const std::string msg =
          "fp.rem is not supported at this format: its circuit unrolls one "
          "divide step per representable exponent difference (2^eb + sb - 4 "
          "= " +
          std::to_string(stp::FloatBlaster::remUnrollSteps(
              lhs->GetExpWidth(), lhs->GetSigWidth())) +
          " steps here, over the limit of " +
          std::to_string(stp::FloatBlaster::REM_UNROLL_LIMIT) +
          "); use a format no larger than binary64";
      fatal_yyerror(msg.c_str());
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(k, lhs->GetValueWidth(),
                                                   *lhs, *rhs));
    setFPFormat(n, lhs->GetExpWidth(), lhs->GetSigWidth());
    stp::releaseParserValue(lhs);
    stp::releaseParserValue(rhs);
    return n;
  }

  // fp.fma: a rounding mode and three floats of the same format.
  ASTNode* createFPFma(ASTNode*& rm, ASTNode*& x, ASTNode*& y, ASTNode*& z)
  {
    checkRoundingMode(rm);

    if (x->GetSourceSort().kind() !=
            stp::SourceSort::Kind::FloatingPoint ||
        y->GetSourceSort().kind() !=
            stp::SourceSort::Kind::FloatingPoint ||
        z->GetSourceSort().kind() !=
            stp::SourceSort::Kind::FloatingPoint)
    {
      fatal_yyerror("arguments to fp.fma must be floats.");
    }

    if (x->GetExpWidth() != y->GetExpWidth() ||
        x->GetSigWidth() != y->GetSigWidth() ||
        x->GetExpWidth() != z->GetExpWidth() ||
        x->GetSigWidth() != z->GetSigWidth())
    {
      fatal_yyerror("arguments to fp.fma must have the same format.");
    }

    ASTVec children;
    children.push_back(*rm);
    children.push_back(*x);
    children.push_back(*y);
    children.push_back(*z);

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(FP_FMA, x->GetValueWidth(),
                                                   children));
    setFPFormat(n, x->GetExpWidth(), x->GetSigWidth());
    stp::releaseParserValue(rm);
    stp::releaseParserValue(x);
    stp::releaseParserValue(y);
    stp::releaseParserValue(z);
    return n;
  }

  // fp.sqrt: a rounding mode and one float.
  ASTNode* createFPSqrt(ASTNode*& rm, ASTNode*& expr)
  {
    checkRoundingMode(rm);

    if (expr->GetSourceSort().kind() !=
        stp::SourceSort::Kind::FloatingPoint)
    {
      fatal_yyerror("argument to fp.sqrt must be a float.");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(FP_SQRT,
                                                   expr->GetValueWidth(), *rm,
                                                   *expr));
    setFPFormat(n, expr->GetExpWidth(), expr->GetSigWidth());
    stp::releaseParserValue(rm);
    stp::releaseParserValue(expr);
    return n;
  }

  // (fp.roundToIntegral rm f). The mode is an ordinary term, exactly as in
  // fp.sqrt, so a RoundingMode variable is accepted as well as the five
  // literal modes.
  ASTNode* createFPRoundToIntegral(ASTNode*& rm, ASTNode*& expr)
  {
    checkRoundingMode(rm);

    if (expr->GetSourceSort().kind() !=
        stp::SourceSort::Kind::FloatingPoint)
    {
      fatal_yyerror("argument to fp.roundToIntegral must be a float.");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(FP_ROUNDTOINTEGRAL,
                                                   expr->GetValueWidth(), *rm,
                                                   *expr));
    setFPFormat(n, expr->GetExpWidth(), expr->GetSigWidth());
    stp::releaseParserValue(rm);
    stp::releaseParserValue(expr);
    return n;
  }

  // (_ BitVec 0) is not a sort. SourceSort::bitVector asserts a positive
  // width, so without this the asserting build aborts inside a header and the
  // NDEBUG build carries a zero-width symbol through the pipeline as a
  // Boolean. The array-component rule was the only one that refused it; every
  // (_ BitVec N) sort production goes through here now, so there is one
  // wording for one mistake rather than a copy per rule.
  void checkBitVectorWidth(unsigned int width)
  {
    if (width == 0)
      fatal_yyerror("bit-vectors must be of positive length");
  }

  // The indexed to_fp forms and the special values carry the format as
  // numerals; apply the floor the sort rule enforces.
  void checkFpFormatWidths(unsigned int exp_width, unsigned int sig_width)
  {
    if (exp_width < 2 || sig_width < 2)
    {
      fatal_yyerror("a floating-point format needs at least 2 exponent and "
                    "2 significand bits");
    }
  }

  // Named IEEE interchange formats, including the hidden significand bit.
  bool namedFloatFormat(const std::string& name, unsigned int& exp_width,
                        unsigned int& sig_width)
  {
    if (name == "Float16") { exp_width = 5;  sig_width = 11;  return true; }
    if (name == "Float32") { exp_width = 8;  sig_width = 24;  return true; }
    if (name == "Float64") { exp_width = 11; sig_width = 53;  return true; }
    if (name == "Float128") { exp_width = 15; sig_width = 113; return true; }
    return false;
  }

  // The same table, for the grammar rule: one named sort per token, so the
  // name is a literal here and the lookup cannot fail.
  stp::float_size* namedFloatSize(const char* name)
  {
    unsigned int exp_width = 0;
    unsigned int sig_width = 0;
    if (!namedFloatFormat(name, exp_width, sig_width))
      stp::FatalError("namedFloatSize: not a named floating-point sort");

    return new stp::float_size(exp_width, sig_width);
  }

  stp::SMT2Sort* namedSortExpression(const std::string& name,
                                     const std::vector<stp::SMT2Sort>& args = {})
  {
    try
    {
      return new stp::SMT2Sort(stp::GlobalParserInterface->sortExpression(name, args));
    }
    catch (const std::invalid_argument& error)
    {
      fatal_yyerror(error.what());
    }
    return nullptr;
  }

  // ((_ to_fp_unsigned e s) rm bv) -- convert an unsigned integer held in a
  // bitvector to the nearest float.
  ASTNode* createFPFromUnsignedBV(unsigned int exp_width,
                                  unsigned int sig_width, ASTNode*& rm,
                                  ASTNode*& bits)
  {
    checkFpFormatWidths(exp_width, sig_width);
    checkRoundingMode(rm);

    if (bits->GetSourceSort().kind() !=
        stp::SourceSort::Kind::BitVector)
    {
      fatal_yyerror("to_fp_unsigned's argument must be a bitvector.");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(
            FP_TOFP_UNSIGNED, exp_width + sig_width,
            stp::GlobalParserInterface->CreateBVConst(32, exp_width),
            stp::GlobalParserInterface->CreateBVConst(32, sig_width), *rm,
            ASTVec(1, *bits)));
    setFPFormat(n, exp_width, sig_width);
    stp::releaseParserValue(rm);
    stp::releaseParserValue(bits);
    return n;
  }

  // ((_ fp.to_ubv m) rm x) / ((_ fp.to_sbv m) rm x): round a float to an
  // integer of width m. The result is a bitvector, not a float, so it gets no
  // floating-point format. The value for the inputs SMT-LIB leaves
  // unspecified is added later, by FpTotalise.
  ASTNode* createFPToBV(Kind k, unsigned int target_width, ASTNode*& rm,
                        ASTNode*& expr)
  {
    if (target_width == 0)
      fatal_yyerror("fp.to_ubv/fp.to_sbv width must be positive.");

    checkRoundingMode(rm);

    if (expr->GetSourceSort().kind() !=
        stp::SourceSort::Kind::FloatingPoint)
      fatal_yyerror("argument to fp.to_ubv/fp.to_sbv must be a float.");

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(
            k, target_width,
            stp::GlobalParserInterface->CreateBVConst(32, target_width), *rm,
            *expr));
    stp::releaseParserValue(rm);
    stp::releaseParserValue(expr);
    return n;
  }

  // fp.abs/fp.neg: a float in, a float of the same format out.
  ASTNode* createFPUnary(Kind k, ASTNode*& expr)
  {
    if (expr->GetSourceSort().kind() !=
        stp::SourceSort::Kind::FloatingPoint)
    {
      fatal_yyerror("argument to a floating-point operation must be a float.");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(k, expr->GetValueWidth(),
                                                   *expr));
    setFPFormat(n, expr->GetExpWidth(), expr->GetSigWidth());
    stp::releaseParserValue(expr);
    return n;
  }

  // fp.isNaN and friends: a float in, a Boolean out.
  ASTNode* createFPPredicate(Kind k, ASTNode*& expr)
  {
    if (expr->GetSourceSort().kind() !=
        stp::SourceSort::Kind::FloatingPoint)
    {
      fatal_yyerror("argument to a floating-point predicate must be a float.");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateNode(k, *expr));
    stp::releaseParserValue(expr);
    return n;
  }

  // (fp.to_real f) -- the exact Real value of a float, through the engine's
  // one construction (STPMgr::CreateFpToReal), which the 3.x API shares.
  ASTNode* createFpToReal(ASTNode*& expr)
  {
    if (expr->GetSourceSort().kind() !=
        stp::SourceSort::Kind::FloatingPoint)
    {
      stp::releaseParserValue(expr);
      fatal_yyerror("fp.to_real takes a floating-point operand.");
      return nullptr;
    }
    try
    {
      ASTNode value = stp::GlobalParserInterface->CreateFpToReal(*expr);
      stp::releaseParserValue(expr);
      return stp::GlobalParserInterface->newNode(value);
    }
    catch (const stp::ParseAbandon&)
    {
      throw;
    }
    catch (const std::exception& failure)
    {
      const std::string diagnostic =
          std::string("fp.to_real: ") + failure.what();
      stp::releaseParserValue(expr);
      fatal_yyerror(diagnostic.c_str());
    }
    return nullptr;
  }

  // (fp.to_ieee_bv f) -- STP's extension, the inverse of ((_ to_fp e s) bv):
  // a float's packed bits (sign, exponent, significand) as a bitvector of
  // width e + s; every NaN gives the canonical pattern.
  ASTNode* createFPToIEEEBV(ASTNode*& expr)
  {
    if (expr->GetSourceSort().kind() !=
        stp::SourceSort::Kind::FloatingPoint)
    {
      stp::releaseParserValue(expr);
      fatal_yyerror("fp.to_ieee_bv takes a floating-point operand.");
      return nullptr;
    }
    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(
            stp::FP_TO_IEEE_BV, expr->GetExpWidth() + expr->GetSigWidth(), *expr));
    stp::releaseParserValue(expr);
    return n;
  }

  // ((_ to_fp e s) bv) -- reinterpret a bitvector's bits as a float.
  ASTNode* createFPFromBits(unsigned int exp_width, unsigned int sig_width,
                            ASTNode*& bits)
  {
    checkFpFormatWidths(exp_width, sig_width);
    if (bits->GetSourceSort().kind() !=
        stp::SourceSort::Kind::BitVector)
    {
      fatal_yyerror("the one-argument form of to_fp takes a bitvector.");
    }

    if (bits->GetValueWidth() != exp_width + sig_width)
    {
      fatal_yyerror("to_fp bitvector width must equal e + s.");
    }

    // No conversion is needed, only a retyping, but the node has to be a
    // distinct object from the bitvector it retypes: the widths are stored on
    // the interned node, so stamping them onto the child directly would make
    // every other use of that bitvector claim to be a float.
    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(
            FP_TOFP, bits->GetValueWidth(),
            stp::GlobalParserInterface->CreateBVConst(32, exp_width),
            stp::GlobalParserInterface->CreateBVConst(32, sig_width), *bits));
    setFPFormat(n, exp_width, sig_width);
    stp::releaseParserValue(bits);
    return n;
  }

  // A concrete Real constant under to_fp -- the only Real terms the
  // QF_FP-family logics admit: a numeral or decimal magnitude, optionally
  // a denominator (the (/ p q) rational spelling), optionally negated.
  struct ParsedRealConstant
  {
    std::string* num;
    std::string* den; // null unless the (/ p q) form
    bool negative;
  };

  static void destroyParsedRealConstant(ParsedRealConstant*& value)
  {
    if (value == nullptr)
      return;
    delete value->num;
    delete value->den;
    delete value;
    value = nullptr;
  }

  static ASTNode* createExactRealLiteral(std::string*& text)
  {
    try
    {
      ASTNode value = stp::GlobalParserInterface->CreateRealConst(*text);
      stp::releaseParserValue(text);
      return stp::GlobalParserInterface->newNode(value);
    }
    catch (const std::exception& failure)
    {
      const std::string diagnostic =
          std::string("invalid exact Real literal: ") + failure.what();
      stp::releaseParserValue(text);
      fatal_yyerror(diagnostic.c_str());
    }
    return nullptr;
  }

  static ASTNode* createExactRealTerm(Kind kind, ASTVec*& children)
  {
    try
    {
      /* SMT-LIB declares * and / :left-assoc, so (* a b c) is (* (* a b) c).
       * CreateRealTerm takes + and - at any arity but these two only in
       * pairs, so fold them here rather than refuse a query the standard
       * allows. Folding left is also what keeps a product legal: the
       * constants meet each other before any symbol does, and every binary
       * node then has the concrete operand the linear fragment asks for.
       * ITE is not associative and is left alone. */
      if ((kind == stp::REAL_MUL || kind == stp::REAL_DIV)
          && children->size() > 2)
      {
        ASTNode folded = (*children)[0];
        for (std::size_t i = 1, n = children->size(); i != n; ++i)
          folded = stp::GlobalParserInterface->CreateRealTerm(
              kind, ASTVec{folded, (*children)[i]});
        stp::releaseParserValue(children);
        return stp::GlobalParserInterface->newNode(folded);
      }
      ASTNode value =
          stp::GlobalParserInterface->CreateRealTerm(kind, *children);
      stp::releaseParserValue(children);
      return stp::GlobalParserInterface->newNode(value);
    }
    catch (const std::exception& failure)
    {
      const std::string diagnostic =
          std::string("unsupported or malformed exact Real operation: ") +
          failure.what();
      stp::releaseParserValue(children);
      fatal_yyerror(diagnostic.c_str());
    }
    return nullptr;
  }

  /* Expanding a define-fun rebuilds the body's nodes through the node
   * factory, which folds constant Real arithmetic through CreateRealTerm --
   * so a macro over Reals can exhaust the number budget while it expands,
   * exactly as a written-out literal can. createExactRealTerm guards the
   * literal path; nothing guarded this one, and SMT2Parse() catches only
   * DeclassifiedNameAbandon, so a NumberFailure escaped the parse and
   * reached std::terminate: SIGABRT with no (error ...) line, where the same
   * overflow spelled as a literal is a clean syntax error.
   *
   * The guard belongs in the action rather than around the parse. checkSat
   * runs from a grammar action too, so a handler at SMT2Parse() would sit
   * above the solve and swallow solve-time budget refusals, which
   * lra::gaveUpOnABudget deliberately tells apart from a bug in STP. Staying
   * inside the action also leaves bison to reclaim its own stack through the
   * %destructor rules, which yyerror's comment above says it relies on. */
  template <class FunctionRef>
  static ASTNode applyFunctionChecked(const FunctionRef& f,
                                      const ASTVec& params)
  {
    try
    {
      return stp::GlobalParserInterface->applyFunction(f, params);
    }
    catch (const stp::ParseAbandon&)
    {
      throw;
    }
    catch (const std::exception& failure)
    {
      const std::string diagnostic =
          std::string("define-fun expansion failed: ") + failure.what();
      fatal_yyerror(diagnostic.c_str());
    }
    return ASTNode();
  }

  static std::string exactRealSignature(const std::string& operation,
                                        const ASTVec& children)
  {
    std::ostringstream diagnostic;
    diagnostic << operation << '(';
    for (size_t i = 0; i < children.size(); ++i)
    {
      if (i != 0)
        diagnostic << ", ";
      diagnostic << children[i].GetSourceSort();
    }
    diagnostic << ')';
    return diagnostic.str();
  }

  static ASTNode* createExactRealPredicate(Kind kind, ASTNode* lhs,
                                           ASTNode* rhs)
  {
    try
    {
      ASTNode value = stp::GlobalParserInterface->CreateRealPredicate(
          kind, *lhs, *rhs);
      stp::releaseParserValue(lhs);
      stp::releaseParserValue(rhs);
      return stp::GlobalParserInterface->newNode(value);
    }
    catch (const std::exception& failure)
    {
      const std::string diagnostic =
          std::string("unsupported or malformed exact Real comparison: ") +
          failure.what();
      stp::releaseParserValue(lhs);
      stp::releaseParserValue(rhs);
      fatal_yyerror(diagnostic.c_str());
    }
    return nullptr;
  }

  static ASTNode* createExactRealPredicate(Kind kind, ASTVec*& operands)
  {
    /* SMT-LIB declares <, <=, > and >= over Reals :chainable, so (> a b c) is
     * (and (> a b) (> b c)) and any arity of two or more is well formed. */
    if (operands->size() < 2)
    {
      const std::string diagnostic =
          "Real comparison " +
          exactRealSignature(stp::_kind_names[kind], *operands) +
          ": expected at least two operands";
      stp::releaseParserValue(operands);
      fatal_yyerror(diagnostic.c_str());
      return nullptr;
    }
    if (operands->size() == 2)
    {
      ASTNode* lhs = new ASTNode((*operands)[0]);
      ASTNode* rhs = new ASTNode((*operands)[1]);
      stp::releaseParserValue(operands);
      return createExactRealPredicate(kind, lhs, rhs);
    }
    ASTVec conjuncts;
    conjuncts.reserve(operands->size() - 1);
    for (std::size_t i = 0, n = operands->size() - 1; i != n; ++i)
    {
      ASTNode* lhs = new ASTNode((*operands)[i]);
      ASTNode* rhs = new ASTNode((*operands)[i + 1]);
      ASTNode* link = createExactRealPredicate(kind, lhs, rhs);
      conjuncts.push_back(*link);
      // The grammar action that consumes a node owns it; these links are
      // consumed here, so they are released here.
      delete link;
    }
    stp::releaseParserValue(operands);
    return stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateNode(stp::AND, conjuncts));
  }

  static unsigned exactCommandNumeral(std::string*& text)
  {
    errno = 0;
    char* end = nullptr;
    const unsigned long parsed = strtoul(text->c_str(), &end, 10);
    const bool invalid = errno == ERANGE || end == text->c_str() ||
                         *end != '\0' ||
                         parsed > std::numeric_limits<unsigned>::max();
    stp::releaseParserValue(text);
    if (invalid)
      fatal_yyerror("command numeral does not fit an unsigned value");
    return static_cast<unsigned>(parsed);
  }

  // The five rounding modes as parse-time values. Rounding-mode constants
  // are interned, so comparing against the five is exact; anything else of
  // RoundingMode sort is symbolic.
  bool constantRoundingMode(const ASTNode& rm, unsigned* mode)
  {
    static const unsigned modes[] = {
        ROUND_NEAREST_TIES_TO_EVEN, ROUND_NEAREST_TIES_TO_AWAY,
        ROUND_TOWARD_POSITIVE, ROUND_TOWARD_NEGATIVE, ROUND_TOWARD_ZERO};
    for (size_t i = 0; i < sizeof(modes) / sizeof(modes[0]); i++)
    {
      if (rm == stp::GlobalParserInterface->CreateRMConst(modes[i]))
      {
        *mode = modes[i];
        return true;
      }
    }
    return false;
  }

  // One packed pattern as the interned float constant, format stamped --
  // the same product the packed-bits spellings of the value would build.
  ASTNode fpConstFromPackedBits(std::string& bits, unsigned int exp_width,
                                unsigned int sig_width)
  {
    ASTNode packed(stp::GlobalParserInterface->CreateBVConst(
        bits, 2, exp_width + sig_width));
    ASTNode c(stp::GlobalParserInterface->nf->CreateFPConst(packed, exp_width,
                                                            sig_width));
    setFPFormat(&c, exp_width, sig_width);
    return c;
  }

  // ((_ to_fp e s) rm 1.5) -- conversion from a real literal, folded at
  // parse time. LibBF reads the decimal exactly and rounds it once in the
  // (e, s) format per mode (see DecimalLiteral.cpp), so the fold is the
  // SMT-LIB semantics, not an approximation of it. A constant rounding
  // mode picks its conversion directly. A symbolic one gets the value
  // under every mode as an if-then-else over the five constants -- the
  // shape bitwuzla builds -- with the last mode as the fall-through: a
  // RoundingMode term is pinned to the five legal encodings when it is
  // declared, so no sixth case exists. A literal that every mode rounds
  // identically (anything exactly representable) collapses to the one
  // constant, symbolic rounding mode or not.
  ASTNode* createFPFromReal(unsigned int exp_width, unsigned int sig_width,
                            ASTNode*& rm, ParsedRealConstant*& real)
  {
    checkFpFormatWidths(exp_width, sig_width);
    checkRoundingMode(rm);

    static const unsigned modes[] = {
        ROUND_NEAREST_TIES_TO_EVEN, ROUND_NEAREST_TIES_TO_AWAY,
        ROUND_TOWARD_POSITIVE, ROUND_TOWARD_NEGATIVE, ROUND_TOWARD_ZERO};
    const size_t n_modes = sizeof(modes) / sizeof(modes[0]);

    unsigned mode = 0;
    const bool constant_rm = constantRoundingMode(*rm, &mode);

    // The conversions this use needs: one for a constant rounding mode,
    // all five for a symbolic one. The error cases (exponent widths the
    // conversion does not cover, a zero denominator) do not depend on the
    // mode, so the first conversion reports them.
    std::string bits[sizeof(modes) / sizeof(modes[0])];
    std::string err;
    const size_t needed = constant_rm ? 1 : n_modes;
    for (size_t i = 0; i < needed; i++)
    {
      const unsigned m = constant_rm ? mode : modes[i];
      bool converted;
      if (real->den != nullptr)
      {
        converted = stp::rationalToPackedFPBits(*real->num, *real->den,
                                                real->negative, exp_width,
                                                sig_width, m, bits[i], err);
      }
      else
      {
        // The engine takes the sign inline for the plain spelling.
        const std::string text =
            (real->negative ? "-" : "") + *real->num;
        converted = stp::decimalToPackedFPBits(text, exp_width, sig_width, m,
                                               bits[i], err);
      }
      if (!converted)
      {
        fatal_yyerror(err.c_str());
      }
    }

    bool all_same = true;
    for (size_t i = 1; i < needed; i++)
      all_same = all_same && bits[i] == bits[0];

    ASTNode* n;
    if (all_same)
    {
      n = stp::GlobalParserInterface->newNode(
          fpConstFromPackedBits(bits[0], exp_width, sig_width));
    }
    else
    {
      // Innermost else first. Each step wraps exactly what the grammar's
      // own (ite ...) rule would build: the branches are float constants
      // of one format, so the source sorts agree by construction, and the
      // leaves carry the format -- the ite nodes are not stamped, like
      // any other parsed ite over floats.
      const unsigned int width = exp_width + sig_width;
      ASTNode result =
          fpConstFromPackedBits(bits[n_modes - 1], exp_width, sig_width);
      for (size_t i = n_modes - 1; i-- > 0;)
      {
        ASTNode cond(stp::GlobalParserInterface->nf->CreateNode(
            EQ, *rm, stp::GlobalParserInterface->CreateRMConst(modes[i])));
        ASTNode branch = fpConstFromPackedBits(bits[i], exp_width, sig_width);
        result = stp::GlobalParserInterface->nf->CreateArrayTerm(
            ITE, result.GetIndexWidth(), width, cond, branch, result);
      }
      n = stp::GlobalParserInterface->newNode(result);
    }
    stp::releaseParserValue(rm);
    destroyParsedRealConstant(real);
    return n;
  }

  // (fp sign exp sig) -- build a float from its three bitvector components:
  // a one-bit sign, an e-bit exponent, and the (s-1)-bit stored significand
  // (the hidden bit is implicit). SMT-LIB permits each component to be an
  // arbitrary bitvector term, not just a literal, so concatenate them and
  // reinterpret the packed bits -- folding to an interned float constant when
  // every component is literal, exactly as the one-argument to_fp does.
  ASTNode* createFPFromParts(ASTNode*& sign, ASTNode*& exp, ASTNode*& sig)
  {
    if (sign->GetSourceSort().kind() != stp::SourceSort::Kind::BitVector ||
        exp->GetSourceSort().kind() != stp::SourceSort::Kind::BitVector ||
        sig->GetSourceSort().kind() != stp::SourceSort::Kind::BitVector)
    {
      fatal_yyerror("fp: the sign, exponent and significand must be bitvectors.");
    }

    unsigned int sign_bits = sign->GetValueWidth();
    unsigned int exp_bits = exp->GetValueWidth();
    unsigned int sig_bits = sig->GetValueWidth();

    if (sign_bits != 1)
    {
      fatal_yyerror("fp: the sign must be a one-bit bitvector.");
    }

    // Plain stack nodes: newNode is only for values handed to bison, and
    // wrapping the intermediates in it leaked two heap nodes per literal.
    ASTNode first(stp::GlobalParserInterface->nf->CreateTerm(
        BVCONCAT, sign_bits + exp_bits, *sign, *exp));
    ASTNode packed(stp::GlobalParserInterface->nf->CreateTerm(
        BVCONCAT, sign_bits + exp_bits + sig_bits, first, *sig));

    const unsigned int exp_width = exp_bits;
    const unsigned int sig_width = sig_bits + sign_bits;

    // The format implied by the component widths gets the same floor the
    // sort rule enforces; without this, (fp #b0 #b1 #b1) built an
    // eb = 1 format that every other entrance rejects.
    checkFpFormatWidths(exp_width, sig_width);

    ASTNode* n;
    if (packed.GetKind() == BVCONST)
    {
      n = stp::GlobalParserInterface->newNode(
          stp::GlobalParserInterface->nf->CreateFPConst(packed, exp_width,
                                                        sig_width));
    }
    else
    {
      n = stp::GlobalParserInterface->newNode(
          stp::GlobalParserInterface->nf->CreateTerm(
              FP_TOFP, sign_bits + exp_bits + sig_bits,
              stp::GlobalParserInterface->CreateBVConst(32, exp_width),
              stp::GlobalParserInterface->CreateBVConst(32, sig_width), packed));
    }

    setFPFormat(n, exp_width, sig_width);

    stp::GlobalParserInterface->deleteNode(sign);
    stp::GlobalParserInterface->deleteNode(exp);
    stp::GlobalParserInterface->deleteNode(sig);
    return n;
  }

  ASTNode* createFPFromReal(unsigned int exp_width, unsigned int sig_width,
                            ASTNode*& rm, ParsedRealConstant*& real);

  // ((_ to_fp e s) rm f) -- reformat a float under a rounding mode.
  ASTNode* createFPToFP(unsigned int exp_width, unsigned int sig_width,
                        ASTNode*& rm, ASTNode*& expr)
  {
    // With the Real keywords live (a Real logic, or a parse the API opened
    // for every theory) a real literal is lexed as a Real term and folded to
    // a Real constant, so it arrives here rather than through
    // an_real_constant: hand it to the from-Real conversion.
    if (expr->GetKind() == stp::REAL_CONST)
    {
      std::string num = expr->GetRealNumerator();
      const std::string den = expr->GetRealDenominator();
      const bool negative = !num.empty() && num[0] == '-';
      if (negative)
        num.erase(0, 1);
      ParsedRealConstant* real = new ParsedRealConstant{
          new std::string(num), den == "1" ? nullptr : new std::string(den),
          negative};
      stp::releaseParserValue(expr);
      try
      {
        return createFPFromReal(exp_width, sig_width, rm, real);
      }
      catch (...)
      {
        // Not on the parser's stack, so nothing else reclaims it; null here
        // if createFPFromReal released it before refusing.
        destroyParsedRealConstant(real);
        throw;
      }
    }

    checkFpFormatWidths(exp_width, sig_width);
    checkRoundingMode(rm);

    // The rm-taking form of to_fp covers three different operations,
    // distinguished by the source's sort: reformatting a float, converting a
    // signed integer held in a bitvector, and converting a real. The first
    // two are handled here, and a Real constant above; a symbolic Real has
    // no conversion.
    const stp::SourceSort::Kind source_kind = expr->GetSourceSort().kind();
    if (source_kind == stp::SourceSort::Kind::Real)
    {
      fatal_yyerror("to_fp of a symbolic Real is not supported: only a Real "
                    "constant converts to a float");
    }
    if (source_kind != stp::SourceSort::Kind::FloatingPoint &&
        source_kind != stp::SourceSort::Kind::BitVector)
    {
      fatal_yyerror("to_fp's argument must be a float or a bitvector.");
    }

    // Which of the two it is has to be recorded now, in the kind. The sort is
    // only reliable here: a float is carried as its packed bits, so once the
    // operand has been lowered it is indistinguishable from the integer.
    const Kind k =
        (source_kind == stp::SourceSort::Kind::FloatingPoint)
            ? FP_TOFP
            : FP_TOFP_SIGNED;

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(
            k, exp_width + sig_width,
            stp::GlobalParserInterface->CreateBVConst(32, exp_width),
            stp::GlobalParserInterface->CreateBVConst(32, sig_width), *rm,
            ASTVec(1, *expr)));
    setFPFormat(n, exp_width, sig_width);
    stp::releaseParserValue(rm);
    stp::releaseParserValue(expr);
    return n;
  }

  ASTNode* createTerm(Kind k, ASTVec*& c)
  {
    assert(k != BVEXTRACT);
    assert(k != BVCONCAT); // width must be width of first operand.
        
    if (c->size() < 2)
    {
      // see createNode: unwind to SMT2Parse() rather than exit(1)
      yyerror("Must be >=2 operands");
      stp::releaseParserValue(c);
      throw stp::DeclassifiedNameAbandon();
    }
    checkBitVectorTerms(*c);
    checkSameWidths(*c);
    const unsigned int width = (*c)[0].GetValueWidth();
    ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(k, width,  *c));
    stp::releaseParserValue(c);
    return n;
  }

  ASTNode* createTerm(Kind k, ASTNode*& c0, ASTNode*& c1)
  {
    checkBitVectorTerm(*c0);
    checkBitVectorTerm(*c1);
    checkSameWidth(*c0, *c1);
    const unsigned int width = c0->GetValueWidth();
    ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(k, width, *c0, *c1));
    stp::releaseParserValue(c0);
    stp::releaseParserValue(c1);
    return n;
  }

  // (bvnego s) is true iff negating s overflows, i.e. iff s is the signed
  // minimum value INT_MIN (100...0). Desugar it to (= s INT_MIN).
  ASTNode* createNegOverflow(ASTNode*& c0)
  {
    checkBitVectorTerm(*c0);
    auto gi = stp::GlobalParserInterface;
    const unsigned int width = c0->GetValueWidth();
    ASTNode intMin;
    if (width == 1)
      intMin = gi->CreateOneConst(1);
    else
      intMin = gi->nf->CreateTerm(BVCONCAT, width, gi->CreateOneConst(1),
                                  gi->CreateZeroConst(width - 1));
    ASTNode* n = gi->newNode(gi->nf->CreateNode(EQ, *c0, intMin));
    stp::releaseParserValue(c0);
    return n;
  }

  // (bvsdivo s t) is true iff the signed division s/t overflows. This happens
  // only for INT_MIN / -1, so desugar it to (and (= s INT_MIN) (= t -1)).
  ASTNode* createSDivOverflow(ASTNode*& c0, ASTNode*& c1)
  {
    checkBitVectorTerm(*c0);
    checkBitVectorTerm(*c1);
    auto gi = stp::GlobalParserInterface;
    const unsigned int width = c0->GetValueWidth();
    ASTNode intMin;
    if (width == 1)
      intMin = gi->CreateOneConst(1);
    else
      intMin = gi->nf->CreateTerm(BVCONCAT, width, gi->CreateOneConst(1),
                                  gi->CreateZeroConst(width - 1));
    // -1 is the all-ones divisor; the node factory folds BVUMINUS of a
    // constant to that constant.
    const ASTNode minusOne =
        gi->nf->CreateTerm(BVUMINUS, width, gi->CreateOneConst(width));
    const ASTNode lhs = gi->nf->CreateNode(EQ, *c0, intMin);
    const ASTNode rhs = gi->nf->CreateNode(EQ, *c1, minusOne);
    ASTNode* n = gi->newNode(gi->nf->CreateNode(AND, lhs, rhs));
    stp::releaseParserValue(c0);
    stp::releaseParserValue(c1);
    return n;
  }

  // Shared scalar declaration action. A cross-namespace name is diagnosed
  // before anything is interned or registered, and does not come back.
  void declareScalarSymbol(std::string*& name,
                           const stp::SourceSort& sourceSort)
  {
    requireFreeTopLevelDeclarationName(*name);
    ASTNode s = stp::GlobalParserInterface->CreateSourceSymbol(
        name->c_str(), sourceSort);
    if (sourceSort.kind() == stp::SourceSort::Kind::Array)
      stp::GlobalParserInterface->addArraySymbol(s, stp::array_sort{
          stp::array_sort_component(sourceSort.index()),
          stp::array_sort_component(sourceSort.element())});
    else if (sourceSort.kind() == stp::SourceSort::Kind::RoundingMode)
      stp::GlobalParserInterface->addRoundingModeSymbol(s);
    else
      stp::GlobalParserInterface->addSymbol(s);
    stp::releaseParserValue(name);
  }

  void annotateTerm(unsigned depth, const ASTNode& term,
                    const std::vector<stp::SMT2Attribute>& attributes)
  {
    const bool closed = stp::SMT2EndAnnotation();
    for (const auto& attribute : attributes)
    {
      if (attribute.name != "named")
        continue;
      if (attribute.value.kind != stp::SMT2AttributeValue::Kind::Symbol)
        fatal_yyerror(":named requires a symbol");
      if (!closed)
        fatal_yyerror(":named requires a closed term");
      const std::string& name = attribute.value.text;
      if (stp::SMT2IsTheorySymbol(name) || stp::STPMgr::isReservedSymbolName(name.c_str()))
        fatal_yyerror(":named requires a fresh, non-reserved symbol");
      std::string diagnostic;
      if (!stp::GlobalParserInterface->validateTopLevelDeclarationName(name, &diagnostic))
        stp::GlobalParserInterface->refuseCurrentCommand(diagnostic);
      stp::GlobalParserInterface->storeFunction(name, ASTVec(), term, true);
      // Only (! ... :named n) at the root of an assert labels an
      // assertion. Nested annotations still introduce ordinary definitions.
      if (depth == 2)
        stp::GlobalParserInterface->nameCurrentAssertion(name);
    }
  }

  void setParsedOption(const stp::SMT2Attribute& attribute)
  {
    using Kind = stp::SMT2AttributeValue::Kind;
    const std::string& name = attribute.name;
    const auto& value = attribute.value;
    const bool boolean = name == "print-success" || name == "global-declarations" ||
        name == "interactive-mode" || name == "produce-models" ||
        name == "produce-assertions" || name == "produce-assignments" ||
        name == "produce-proofs" || name == "produce-unsat-cores" ||
        name == "produce-unsat-assumptions";
    if (boolean && value.kind != Kind::Symbol)
      stp::GlobalParserInterface->refuseCurrentCommand("option :" + name + " requires a Boolean symbol");
    if ((name == "regular-output-channel" || name == "diagnostic-output-channel") &&
        value.kind != Kind::String)
      stp::GlobalParserInterface->refuseCurrentCommand("option :" + name + " requires a string");
    if ((name == "random-seed" || name == "verbosity" || name == "reproducible-resource-limit") &&
        value.kind != Kind::Numeral)
      stp::GlobalParserInterface->refuseCurrentCommand("option :" + name + " requires a numeral");
    stp::GlobalParserInterface->setOption(name, value.text);
  }

  void setParsedInfo(const stp::SMT2Attribute& attribute)
  {
    if (attribute.name == "status")
    {
      const std::string& status = attribute.value.text;
      if (attribute.value.kind != stp::SMT2AttributeValue::Kind::Symbol ||
          (status != "sat" && status != "unsat" && status != "unknown"))
        stp::GlobalParserInterface->refuseCurrentCommand("set-info :status requires sat, unsat, or unknown");
      stp::input_status = status == "sat" ? stp::TO_BE_SATISFIABLE :
                          status == "unsat" ? stp::TO_BE_UNSATISFIABLE : stp::TO_BE_UNKNOWN;
    }
    stp::GlobalParserInterface->success();
  }

  void checkQualifiedSort(stp::SourceSort*& requested, const stp::SourceSort& actual)
  {
    if (!requested) return;
    const bool matches = *requested == actual;
    const std::string diagnostic = matches ? std::string() :
        "qualified identifier has result sort " + stp::sourceSortToSMTLib(actual) +
        ", not " + stp::sourceSortToSMTLib(*requested);
    stp::releaseParserValue(requested);
    if (!matches) fatal_yyerror(diagnostic.c_str());
  }

  void checkQualifiedResult(stp::SourceSort*& requested, stp::ASTNode*& result)
  {
    if (requested && *requested != result->GetSourceSort())
    {
      const stp::SourceSort actual = result->GetSourceSort();
      stp::GlobalParserInterface->deleteNode(result);
      checkQualifiedSort(requested, actual);
    }
    stp::releaseParserValue(requested);
  }

  struct ParsedIndexedIdentifier
  {
    unsigned first = 0, second = 0, tag = 0;
    std::string digits;
    stp::SourceSort* qualifier = nullptr;
    ~ParsedIndexedIdentifier() { delete qualifier; }
  };

#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 104857600
#define YYERROR_VERBOSE 1
#define YY_EXIT_FAILURE -1

%}

/* Conflict-free, and pinned that way: the floating-point productions were
   once one nonterminal reachable from both term and formula position, which
   alone accounted for 216 shift/reduce and 99 reduce/reduce conflicts. Any
   grammar change that introduces a conflict now fails the build. */
%expect 0

%union {
  struct ParsedIndexedIdentifier* indexed;
  stp::SMT2Attribute* attribute;
  std::vector<stp::SMT2Attribute>* attributes;
  stp::SMT2AttributeValue* attribute_value;
  /* Elaborated: the union lands in parsesmt2.tab.h, where only this
     pointer is named; the struct itself lives in the parser prologue. */
  struct ParsedRealConstant* realc;
  unsigned uintval; /* for numerals in types. */
  stp::float_size* fp_size;
  stp::SourceSort* sort;
  stp::SMT2Sort* sortexpr;
  std::vector<stp::SMT2Sort>* sortexprvec;
  stp::array_sort* arr_sort;

  //ASTNode,ASTVec
  stp::ASTNode *node;
  stp::ASTVec *vec;

  std::string *str;

  /* A resolved define-fun. FunctionMap preserves addresses when :named
     terms introduce definitions while an application is being parsed. */
  const stp::Cpp_interface::Function *fn;
  const stp::UFDecl *ufdecl;
  stp::parsed_uf_sort *ufsort;
  std::vector<stp::parsed_uf_sort> *ufsortvec;
};

/* Successful reductions transfer or release (stp::releaseParserValue) the
   values they own in their grammar actions. Values discarded by Bison during
   recovery or parse abort remain Bison's responsibility; release them here so
   malformed commands do not leak their identifier/string lookahead. */
%destructor { delete $$; } <str> <attribute> <attribute_value> <attributes>
%destructor { delete $$; } <ufsort> <ufsortvec>

/* An exception out of an action or the lexer gets the same cleanup: see
   ParserUnwind.h. */
%initial-action { STP_PARSER_RECLAIM_ON_UNWIND() }

%type <sort> id_and id_bvand id_bvarithrightshift id_bvcomp id_bvconcat id_bvdiv id_bvge id_bvgt id_bvle id_bvleftshift_1 id_bvlt id_bvmod id_bvmult id_bvnand id_bvneg id_bvnego id_bvnor id_bvnot id_bvor id_bvplus id_bvrightshift_1 id_bvsaddo id_bvsdivo id_bvsge id_bvsgt id_bvsle id_bvslt id_bvsmulo id_bvssubo id_bvsub id_bvuaddo id_bvumulo id_bvusubo id_bvxnor id_bvxor id_distinct id_eq id_false id_fp id_fp_abs id_fp_add id_fp_div id_fp_eq id_fp_fma id_fp_geq id_fp_gt id_fp_isinfinite id_fp_isnan id_fp_isnegative id_fp_isnormal id_fp_ispositive id_fp_issubnormal id_fp_iszero id_fp_leq id_fp_lt id_fp_max id_fp_min id_fp_mul id_fp_neg id_fp_rem id_fp_rm_roundnearesttiestoaway id_fp_rm_roundnearesttiestoeven id_fp_rm_roundtowardnegative id_fp_rm_roundtowardpositive id_fp_rm_roundtowardzero id_fp_roundtointegral id_fp_sqrt id_fp_sub id_fp_to_ieee_bv id_fp_to_real id_implies id_ite id_not id_or id_real_add id_real_div id_real_ge id_real_gt id_real_le id_real_lt id_real_mul id_real_sub id_sbvdiv id_sbvmod id_sbvrem id_select id_store id_true id_xor
%type <fn> id_array_functionid id_bitvector_functionid id_boolean_functionid id_declaredsort_functionid id_floatingpoint_functionid id_real_functionid id_roundingmode_functionid
%type <node> id_formid id_termid
%type <ufdecl> id_uf_bool_functionid id_uf_bv_functionid
%type <indexed> id_bvconst_decimal id_bvconst_decimal_bare id_bvextract id_bvextract_bare id_bvrepeat id_bvrepeat_bare id_bvrotate_left id_bvrotate_left_bare id_bvrotate_right id_bvrotate_right_bare id_bvsx id_bvsx_bare id_bvzx id_bvzx_bare id_fp_special id_fp_special_bare id_fp_to_sbv id_fp_to_sbv_bare id_fp_to_ubv id_fp_to_ubv_bare id_fp_tofp id_fp_tofp_bare id_fp_tofp_unsigned id_fp_tofp_unsigned_bare

%start cmd

%type <vec> an_formulas an_terms function_params an_mixed

%type <node> an_term  an_formula function_param an_const an_fp_term an_fp_predicate an_rounding_mode
%type <node> definition_body
%type <uintval> an_fp_const command_numeral
%type <str> sort_parameter_name
%type <attribute> attribute
%type <attributes> attributes
%type <attribute_value> attribute_value
%type <str> uf_decl_name function_def_name
%type <ufsortvec> uf_domain_sorts
%type <ufsort> uf_sort uf_codomain_sort

%type <fp_size> an_fp_sort
%type <sort> resolved_sort
%type <sortexpr> sort_expression array_sort_expression sort_application
%type <sortexprvec> sort_arguments
%type <arr_sort> an_array_sort

/* Release owning values discarded during parser recovery or teardown.
   Successful reductions still transfer or release their own RHS values. */
%destructor { delete $$; } <node>
%destructor { delete $$; } <vec>
%destructor { delete $$; } <fp_size>
%destructor { delete $$; } <sort> <sortexpr> <sortexprvec>
%destructor { delete $$; } <arr_sort> <indexed>
%destructor { destroyParsedRealConstant($$); } <realc>

%token <str> ATTRIBUTE_KEYWORD_TOK
%token <attribute_value> ATTRIBUTE_VALUE_TOK
%token <uintval> NUMERAL_TOK

 /* A numeral too large for an unsigned, carrying its digits. It is a real
    magnitude and nothing else: as an index, a width or a count it is out of
    range, and the grammar rejecting it there is the diagnosis. */
%token <str> BIG_NUMERAL_TOK

%token <str> BVCONST_DECIMAL_TOK
%token <str> BVCONST_BINARY_TOK
%token <str> BVCONST_HEXIDECIMAL_TOK

 /* Carries its text: to_fp folds real literals, and set-info values
    like :smt-lib-version 2.0 land here too (and are freed unused). */
%token <str> DECIMAL_TOK
%token <str> REAL_NUMERAL_TOK REAL_DECIMAL_TOK
%type <str> an_real_magnitude
%type <realc> an_real_constant

%token <node> FORMID_TOK TERMID_TOK
%token <str> ABSTRACT_VALUE_TOK
%token <str> STRING_TOK
%token <fn> BITVECTOR_FUNCTIONID_TOK BOOLEAN_FUNCTIONID_TOK FLOATINGPOINT_FUNCTIONID_TOK ARRAY_FUNCTIONID_TOK REAL_FUNCTIONID_TOK
%token <ufdecl> UF_BV_FUNCTIONID_TOK UF_BOOL_FUNCTIONID_TOK

 /* set-info tokens */
%token SOURCE_TOK
%token CATEGORY_TOK
%token DIFFICULTY_TOK
%token VERSION_TOK
%token STATUS_TOK
%token LICENSE_TOK

 /* ASCII Symbols */
 /* Semicolons (comments) are ignored by the lexer */
%token UNDERSCORE_TOK
%token <uintval> LPAREN_TOK
%type <uintval> annotation_open
%token RPAREN_TOK

/* Used for attributed expressions */
%token EXCLAIMATION_MARK_TOK
%token NAMED_ATTRIBUTE_TOK

 /*BV SPECIFIC TOKENS*/
%token BVLEFTSHIFT_1_TOK
%token BVRIGHTSHIFT_1_TOK
%token BVARITHRIGHTSHIFT_TOK
%token BVPLUS_TOK
%token BVSUB_TOK
%token BVNOT_TOK //bvneg in CVCL
%token BVMULT_TOK
%token BVDIV_TOK
%token SBVDIV_TOK
%token BVMOD_TOK
%token SBVREM_TOK
%token SBVMOD_TOK
%token BVNEG_TOK //bvuminus in CVCL
%token BVAND_TOK
%token BVOR_TOK
%token BVXOR_TOK
%token BVNAND_TOK
%token BVNOR_TOK
%token BVXNOR_TOK
%token BVCONCAT_TOK
%token BVLT_TOK
%token BVGT_TOK
%token BVLE_TOK
%token BVGE_TOK
%token BVSLT_TOK
%token BVSGT_TOK
%token BVSLE_TOK
%token BVSGE_TOK

%token BVSX_TOK
%token BVEXTRACT_TOK
%token BVZX_TOK
%token BVROTATE_RIGHT_TOK
%token BVROTATE_LEFT_TOK
%token BVREPEAT_TOK
%token BVCOMP_TOK

%token BVNEGO_TOK
%token BVUADDO_TOK
%token BVSADDO_TOK
%token BVUMULO_TOK
%token BVSMULO_TOK
%token BVUSUBO_TOK
%token BVSSUBO_TOK
%token BVSDIVO_TOK

 /* Types for QF_BV and QF_AUFBV. */
%token BITVEC_TOK
%token ARRAY_TOK
%token BOOL_TOK

/* Types for QF_FP and QF_BVFP. */
%token FLOATINGPOINT_TOK
%token ROUNDINGMODE_TOK
%token REAL_TOK
%token <fn> ROUNDINGMODE_FUNCTIONID_TOK
%token <fn> DECLAREDSORT_FUNCTIONID_TOK
%token FLOAT16_TOK
%token FLOAT32_TOK
%token FLOAT64_TOK
%token FLOAT128_TOK

/* Mathematical Real linear operations, live only under the Real logics:
   QF_LRA, QF_UFLRA, QF_AUFLRA and the LRA variants of the floating-point
   logics. */
%token REAL_ADD_TOK REAL_SUB_TOK REAL_MUL_TOK REAL_DIV_TOK
%token REAL_LT_TOK REAL_LE_TOK REAL_GT_TOK REAL_GE_TOK

/* CORE THEORY pg. 29 of the SMT-LIB2 standard 30-March-2010. */
%token TRUE_TOK;
%token FALSE_TOK;
%token NOT_TOK;
%token AND_TOK;
%token OR_TOK;
%token XOR_TOK;
%token ITE_TOK;
%token EQ_TOK;
%token IMPLIES_TOK;

 /* CORE THEORY. But not on pg 29. */
%token DISTINCT_TOK;
%token LET_TOK;

%token COLON_TOK

// COMMANDS
%token ASSERT_TOK
%token CHECK_SAT_TOK
%token CHECK_SAT_ASSUMING_TOK
%token DECLARE_CONST_TOK
%token DECLARE_FUNCTION_TOK
%token DECLARE_SORT_TOK
%token DECLARE_SORT_PARAMETER_TOK
%token RESERVED_TOK
%token DEFINE_FUNCTION_TOK
%token DEFINE_FUN_REC_TOK
%token DEFINE_FUNS_REC_TOK
%token DEFINE_SORT_TOK
%token DECLARE_DATATYPE_TOK
%token DECLARE_DATATYPES_TOK
%token <str> STRING_LITERAL_TOK
%token ECHO_TOK
%token DEFINE_CONST_TOK
%token EXIT_TOK
%token GET_ASSERTIONS_TOK
%token GET_ASSIGNMENT_TOK
%token GET_INFO_TOK
%token GET_MODEL_TOK
%token GET_OPTION_TOK
%token GET_PROOF_TOK
%token GET_UNSAT_ASSUMPTIONS_TOK
%token GET_UNSAT_CORE_TOK
%token GET_VALUE_TOK
%token POP_TOK
%token PUSH_TOK
%token RESET_TOK
%token RESET_ASSERTIONS_TOK
%token NOTES_TOK
%token LOGIC_TOK
%token SET_OPTION_TOK

 /* Functions for QF_ABV. */
%token SELECT_TOK;
%token STORE_TOK;
%token AS_TOK;

 /* generic FP token*/
%token FP_TOK

 /* FP conversions */
%token FP_TOFP_TOK
%token FP_TOFP_UNSIGNED_TOK
%token FP_TO_UBV_TOK;
%token FP_TO_SBV_TOK;

 /* Functions for FP */
%token FP_ABS_TOK;
%token FP_NEG_TOK;
%token FP_ADD_TOK;
%token FP_SUB_TOK;
%token FP_MUL_TOK;
%token FP_DIV_TOK;
%token FP_FMA_TOK;
%token FP_SQRT_TOK;
%token FP_REM_TOK;
%token FP_ROUNDTOINTEGRAL_TOK;
%token FP_MIN_TOK;
%token FP_MAX_TOK;
%token FP_LEQ_TOK;
%token FP_LT_TOK;
%token FP_GEQ_TOK;
%token FP_GT_TOK;
%token FP_EQ_TOK;
%token FP_TO_REAL_TOK;
%token FP_TO_IEEE_BV_TOK;
%token FP_ISNORMAL_TOK;
%token FP_ISSUBNORMAL_TOK;
%token FP_ISZERO_TOK;
%token FP_ISINFINITE_TOK;
%token FP_ISNAN_TOK;
%token FP_ISNEGATIVE_TOK;
%token FP_ISPOSITIVE_TOK;

 /* fp rounding modes */
%token FP_RM_ROUNDTOWARDZERO_TOK;
%token FP_RM_ROUNDNEARESTTIESTOEVEN_TOK;
%token FP_RM_ROUNDNEARESTTIESTOAWAY_TOK;
%token FP_RM_ROUNDTOWARDPOSITIVE_TOK;
%token FP_RM_ROUNDTOWARDNEGATIVE_TOK;

 /* fp constants */
%token FP_NAN_TOK;
%token FP_NEG_INF_TOK;
%token FP_POS_INF_TOK;
%token FP_NEG_ZERO_TOK;
%token FP_POS_ZERO_TOK;

%token END 0 "end of file"

%%
command_numeral:
  NUMERAL_TOK
{
  $$ = $1;
}
| REAL_NUMERAL_TOK
{
  $$ = exactCommandNumeral($1);
}
;

cmd: commands END
{
       stp::GlobalParserInterface->cleanUp();
       YYACCEPT;
}
/* SMT-LIB's <script> is <command>*: an input with no command is one too. */
| END
{
       stp::GlobalParserInterface->cleanUp();
       YYACCEPT;
}
;

command_open:
LPAREN_TOK
{
  stp::GlobalParserInterface->beginCurrentCommand();
}
;

commands: commands command_open cmdi RPAREN_TOK
{
  stp::GlobalParserInterface->finishCurrentCommand();
}
| command_open cmdi RPAREN_TOK
{
  stp::GlobalParserInterface->finishCurrentCommand();
}
;

cmdi:
     ASSERT_TOK an_formula
    {
      stp::GlobalParserInterface->addParsedAssertion(*$2);
      stp::GlobalParserInterface->deleteNode($2);
      stp::GlobalParserInterface->success();
    }
|
     CHECK_SAT_TOK
    {
      stp::GlobalParserInterface->checkSat(stp::GlobalParserInterface->getAssertVector());
    }
|
     CHECK_SAT_ASSUMING_TOK LPAREN_TOK an_formulas RPAREN_TOK
    {
      // The standard's argument is a list of prop_literals, i.e. boolean
      // symbols or their negations. We accept any boolean formula, which
      // is a superset of that.
      stp::GlobalParserInterface->checkSatAssuming(*$3);
      stp::releaseParserValue($3);
    }
|
     CHECK_SAT_ASSUMING_TOK LPAREN_TOK RPAREN_TOK
    {
      // No assumptions: same as (check-sat), through the same path so the
      // two commands cannot drift apart.
      stp::GlobalParserInterface->checkSatAssuming(stp::ASTVec());
    }
|
     DECLARE_CONST_TOK const_decl
    {
      stp::GlobalParserInterface->success();
    }
|
     DECLARE_FUNCTION_TOK var_decl
    {
      stp::GlobalParserInterface->success();
    }
|
     DEFINE_FUNCTION_TOK function_def
    {
      stp::GlobalParserInterface->success();
    }
|
     DEFINE_CONST_TOK function_def_name resolved_sort definition_body
    {
      if ($3->kind() == stp::SourceSort::Kind::Unknown)
        fatal_yyerror("define-const: unknown sort");
      if (*$3 != $4->GetSourceSort())
        fatal_yyerror("define-const: the body's sort does not match the declared result sort");
      stp::GlobalParserInterface->storeFunction(*$2, ASTVec(), *$4);
      stp::releaseParserValue($2);
      stp::releaseParserValue($3);
      stp::GlobalParserInterface->deleteNode($4);
      stp::GlobalParserInterface->success();
    }
|
     ECHO_TOK STRING_LITERAL_TOK
    {
      stp::GlobalParserInterface->echo(*$2);
      stp::releaseParserValue($2);
    }
|
     EXIT_TOK
    {
       stp::GlobalParserInterface->cleanUp();
       stp::GlobalParserInterface->success();
       YYACCEPT;
    }
|
     GET_MODEL_TOK
    {
       stp::GlobalParserInterface->getModel();
    }
|
     GET_VALUE_TOK LPAREN_TOK an_mixed RPAREN_TOK
    {
      stp::GlobalParserInterface->getValue(*$3);
      stp::releaseParserValue($3);
    }
|
     SET_OPTION_TOK attribute
    {
      setParsedOption(*$2);
      stp::releaseParserValue($2);
    }
|
     GET_OPTION_TOK ATTRIBUTE_KEYWORD_TOK
    {
      stp::GlobalParserInterface->getOption(*$2);
      stp::releaseParserValue($2);
    }
|
     GET_INFO_TOK ATTRIBUTE_KEYWORD_TOK
    {
      stp::GlobalParserInterface->getInfo(*$2);
      stp::releaseParserValue($2);
    }
|
     GET_ASSERTIONS_TOK
    {
       stp::GlobalParserInterface->getAssertions();
    }
|
     RESET_ASSERTIONS_TOK
    {
       stp::GlobalParserInterface->resetAssertions();
       stp::GlobalParserInterface->success();
    }
|
     /* Commands STP has no way to answer. The standard asks for the response
        "unsupported" rather than an error, and for the rest of the script to
        be processed regardless. */
     GET_ASSIGNMENT_TOK
    {
       stp::GlobalParserInterface->getAssignment();
    }
|
     GET_PROOF_TOK
    {
       stp::GlobalParserInterface->unavailableQuery("get-proof", "produce-proofs");
    }
|
     GET_UNSAT_CORE_TOK
    {
       stp::GlobalParserInterface->getUnsatCore();
    }
|
     GET_UNSAT_ASSUMPTIONS_TOK
    {
       stp::GlobalParserInterface->getUnsatAssumptions();
    }
|
     /* A nullary uninterpreted sort gets an identity of its own and a
        bit-vector carrier wide enough that nothing the query can say
        distinguishes more elements than it holds. The sort has no operation
        but equality, so a query mentioning k terms of it is satisfiable
        exactly when it is satisfiable over k elements: a wider carrier is
        always sound, and only a narrower one would not be. The width has to be
        chosen here, before any term of the sort exists, so it cannot be
        derived from k -- see uf_sort_width.

        The identity is the part that took two attempts. Registered as its bare
        carrier, the sort *was* that bit-vector: two declared sorts were one
        sort and each was the same sort as a genuine bit-vector of the same
        width, so (= s t) across two sorts and (bvadd e e) on an element were
        both accepted. Every frontend guard compares a full SourceSort and
        every one of them already refuses a float of the same packed width;
        none of them was at fault.

       Parametric sorts (arity > 0) have no such reading and stay
       unsupported. Nullary sorts are accepted either when the UF frontend is
       enabled or when QF_AX selected them for array indices and elements. */
     DECLARE_SORT_TOK STRING_TOK command_numeral
    {
       if ($3 != 0 ||
           !stp::GlobalParserInterface->declaredSortsEnabled())
         stp::GlobalParserInterface->unsupported();
       else
       {
         stp::GlobalParserInterface->addSortAlias(
             *$2, stp::registerUninterpretedSort(
                      *$2, stp::GlobalParserInterface->getUserFlags()
                               .uf_sort_width));
         stp::GlobalParserInterface->success();
       }
       stp::releaseParserValue($2);
    }
|
     DECLARE_SORT_PARAMETER_TOK STRING_TOK
    {
       // Global sort parameters require polymorphic declarations and solving.
       stp::GlobalParserInterface->unsupported();
       stp::releaseParserValue($2);
    }
|
     DEFINE_SORT_TOK STRING_TOK sort_parameter_open sort_parameters sort_parameter_close sort_expression
    {
      stp::GlobalParserInterface->defineSort(*$2, *$6);
      stp::SMT2SetSortContext(false);
      stp::releaseParserValue($2);
      stp::releaseParserValue($6);
      stp::GlobalParserInterface->success();
    }
|
     DEFINE_FUN_REC_TOK
    {
       stp::GlobalParserInterface->unsupported();
    }
|
     DEFINE_FUNS_REC_TOK
    {
       stp::GlobalParserInterface->unsupported();
    }
|
     DECLARE_DATATYPE_TOK
    {
       stp::GlobalParserInterface->unsupported();
    }
|
     DECLARE_DATATYPES_TOK
    {
       stp::GlobalParserInterface->unsupported();
    }
|
     PUSH_TOK command_numeral
    {
        for (unsigned i=0; i < $2;i++)
            stp::GlobalParserInterface->push();
        stp::GlobalParserInterface->success();
    }
|
     POP_TOK command_numeral
    {
        for (unsigned i=0; i < $2;i++)
            stp::GlobalParserInterface->pop();
        stp::GlobalParserInterface->success();
    }
|
     RESET_TOK
    {
       stp::GlobalParserInterface->reset();
       // reset clears the logic, and with it the theory keyword gates a
       // set-logic opened; the gates a caller opened for the whole parse
       // (all_theory_tokens) stay open.
       stp::SMT2SetFloatTokens(stp::GlobalParserInterface->all_theory_tokens);
       stp::SMT2SetRealTokens(stp::GlobalParserInterface->all_theory_tokens);
       stp::SMT2SetBitVectorTokens(stp::GlobalParserInterface->all_theory_tokens);
       stp::GlobalParserInterface->success();
    }
|
     LOGIC_TOK STRING_TOK
    {
      // The *FPLRA logics are the FP logics plus the theory of reals, and
      // they open both theories' keywords: Real declarations and linear
      // arithmetic, fp.to_real, and a Real constant under to_fp, which the
      // Real keywords lex as a Real term and createFPToFP folds exactly as
      // the literal forms are. Only a symbolic Real under to_fp is refused.
      // A numeral inside an indexed identifier stays an index (the lexer
      // tracks "(_ ... )"), so (_ BitVec 8) and ((_ to_fp 8 24) RNE 1) read
      // as they do in the FP logics.
      // A logic containing UF enables the SMT-LIB UF frontend. The command
      // line flag remains useful for inputs whose declared logic omits UF,
      // but a correctly classified input must not need a second, nonstandard
      // switch to make its own logic work. The UF+FP names are floating-point
      // logics in their own right: outside one, "RoundingMode" is not even a
      // token (see SMT2SetFloatTokens below).
      //
      // SMT-LIB orders the theory letters A, UF, BV, FP, so the name a
      // benchmark carries for arrays with uninterpreted functions and floats
      // is QF_AUFBVFP -- the same order this file already uses for QF_AUFBV.
      // QF_UFABVFP is accepted as an alias for it: it is the spelling this
      // branch shipped first and several fixtures name it. Apply the same
      // rule to the FPLRA forms accepted for each non-UF FP logic.
      const bool uf_fp_logic =
            0 == strcmp($2->c_str(),"QF_UFFP") ||
            0 == strcmp($2->c_str(),"QF_UFBVFP") ||
            0 == strcmp($2->c_str(),"QF_AUFBVFP") ||
            0 == strcmp($2->c_str(),"QF_UFABVFP") ||
            0 == strcmp($2->c_str(),"QF_UFFPLRA") ||
            0 == strcmp($2->c_str(),"QF_UFBVFPLRA") ||
            0 == strcmp($2->c_str(),"QF_AUFBVFPLRA") ||
            0 == strcmp($2->c_str(),"QF_UFABVFPLRA");
      const bool uf_logic =
            0 == strcmp($2->c_str(),"QF_UFLRA") ||
            0 == strcmp($2->c_str(),"QF_AUFLRA") ||
            0 == strcmp($2->c_str(),"QF_UF") ||
            0 == strcmp($2->c_str(),"QF_UFBV") ||
            0 == strcmp($2->c_str(),"QF_AUFBV") ||
            uf_fp_logic;
      const bool fp_logic =
            0 == strcmp($2->c_str(),"QF_FP") ||
            0 == strcmp($2->c_str(),"QF_BVFP") ||
            0 == strcmp($2->c_str(),"QF_ABVFP") ||
            0 == strcmp($2->c_str(),"QF_FPLRA") ||
            0 == strcmp($2->c_str(),"QF_BVFPLRA") ||
            0 == strcmp($2->c_str(),"QF_ABVFPLRA") ||
            uf_fp_logic;
      const bool fp_lra_logic =
            0 == strcmp($2->c_str(),"QF_FPLRA") ||
            0 == strcmp($2->c_str(),"QF_BVFPLRA") ||
            0 == strcmp($2->c_str(),"QF_ABVFPLRA") ||
            0 == strcmp($2->c_str(),"QF_UFFPLRA") ||
            0 == strcmp($2->c_str(),"QF_UFBVFPLRA") ||
            0 == strcmp($2->c_str(),"QF_AUFBVFPLRA") ||
            0 == strcmp($2->c_str(),"QF_UFABVFPLRA");
      const bool real_logic = 0 == strcmp($2->c_str(),"QF_LRA") ||
                         0 == strcmp($2->c_str(),"QF_UFLRA") ||
                         0 == strcmp($2->c_str(),"QF_AUFLRA") ||
                         fp_lra_logic;
      const bool all_logic = *$2 == "ALL";
      const bool supported_logic = all_logic ||
            0 == strcmp($2->c_str(),"QF_BV") ||
            0 == strcmp($2->c_str(),"QF_ABV") ||
            0 == strcmp($2->c_str(),"QF_AX") ||
            uf_logic ||
            fp_logic ||
            real_logic;
      // A logic STP cannot decide ends the session. STP answers
      // (get-info :error-behavior) with immediate-exit, and continuing here
      // was the one place that answer was untrue: the refusal was printed,
      // the rest of the script ran anyway, and a check-sat inside it reported
      // a verdict for a benchmark STP had just said it could not accept.
      // Which of the two diagnostics is right is the only thing left to
      // decide, and neither one returns.
      if (!supported_logic)
      {
        std::string message = isSMTLIBLogicName(*$2)
                                  ? "unsupported logic: STP decides "
                                  : "unknown logic: SMT-LIB names no logic "
                                    "this way, and STP decides ";
        message += supportedLogicsPhrase();
        fatal_yyerror(message.c_str());
      }
      // The incremental frontend needs only this validated logic name to
      // choose its measured automatic-engagement policy. reset clears the
      // classification; reset-assertions retains it with the SMT-LIB logic.
      stp::GlobalParserInterface->setLogic(*$2);
      // The floating-point keywords exist only inside the FP logics;
      // everywhere else names like "fp" or "NaN" stay ordinary symbols,
      // exactly as before floating-point support existed.
      stp::SMT2SetFloatTokens(all_logic || fp_logic);
      stp::SMT2SetRealTokens(all_logic || real_logic);
      stp::SMT2SetBitVectorTokens(stp::GlobalParserInterface->all_theory_tokens ||
                                all_logic || fp_logic || $2->find("BV") != std::string::npos);
      stp::GlobalParserInterface->success();
      stp::releaseParserValue($2);
    }
|
     NOTES_TOK attribute
    {
      setParsedInfo(*$2);
      stp::releaseParserValue($2);
    }

;

definition_body:
  an_term { $$ = $1; }
| an_formula { $$ = $1; }
;

function_param_open:
LPAREN_TOK
{
  stp::SMT2ExpectFunctionParameterName();
}
;

function_param:
function_param_open STRING_TOK resolved_sort RPAREN_TOK
{
  $$ = new ASTNode(stp::GlobalParserInterface->CreateParameterSymbol($2->c_str(), *$3));
  stp::GlobalParserInterface->addTemporarySymbol(*$$);
  stp::releaseParserValue($2);
  stp::releaseParserValue($3);
}
;

/* Returns a vector of parameters.*/
function_params:
function_param
{
  $$ = new ASTVec;
  $$->push_back(*$1);
  stp::GlobalParserInterface->deleteNode($1);
}
| function_params function_param
{
  $$ = $1;
  $$->push_back(*$2);
  stp::GlobalParserInterface->deleteNode($2);
};

function_def_name:
STRING_TOK
{
  requireFreeTopLevelDeclarationName(*$1);
  $$ = $1;
}
;

function_def:
function_def_name LPAREN_TOK function_params RPAREN_TOK resolved_sort definition_body
{
  if ($6->GetSourceSort() != *$5)
    fatal_yyerror("define-fun: the body's sort does not match the declared result sort");
  stp::GlobalParserInterface->storeFunction(*$1, *$3, *$6);
  for (const ASTNode& parameter : *$3)
    stp::GlobalParserInterface->removeSymbol(parameter);
  stp::releaseParserValue($1);
  stp::releaseParserValue($3);
  stp::releaseParserValue($5);
  stp::GlobalParserInterface->deleteNode($6);
}
|
function_def_name LPAREN_TOK RPAREN_TOK resolved_sort definition_body
{
  if ($5->GetSourceSort() != *$4)
    fatal_yyerror("define-fun: the body's sort does not match the declared result sort");
  stp::GlobalParserInterface->storeFunction(*$1, ASTVec(), *$5);
  stp::releaseParserValue($1);
  stp::releaseParserValue($4);
  stp::GlobalParserInterface->deleteNode($5);
}
;

annotation_open:
LPAREN_TOK EXCLAIMATION_MARK_TOK { stp::SMT2BeginAnnotation(); $$ = $1; }
;

annotation_attributes:
%empty { stp::SMT2BeginAttributes(); }
;

attributes:
attribute
{
  $$ = new std::vector<stp::SMT2Attribute>{*$1};
  stp::releaseParserValue($1);
}
| attributes attribute
{
  $$ = $1;
  $$->push_back(*$2);
  stp::releaseParserValue($2);
}
;

attribute:
ATTRIBUTE_KEYWORD_TOK
{
  $$ = new stp::SMT2Attribute{*$1, {}};
  stp::releaseParserValue($1);
}
| ATTRIBUTE_KEYWORD_TOK attribute_value
{
  if ($2->kind == stp::SMT2AttributeValue::Kind::Reserved)
    fatal_yyerror("reserved word is not an attribute value outside an s-expression");
  $$ = new stp::SMT2Attribute{*$1, *$2};
  stp::releaseParserValue($1);
  stp::releaseParserValue($2);
}
;

attribute_value:
ATTRIBUTE_VALUE_TOK { $$ = $1; }
| LPAREN_TOK sexpr_items RPAREN_TOK
{
  $$ = new stp::SMT2AttributeValue{stp::SMT2AttributeValue::Kind::List, ""};
}
;

sexpr_items:
  %empty
| sexpr_items attribute_value { stp::releaseParserValue($2); }
| sexpr_items ATTRIBUTE_KEYWORD_TOK { stp::releaseParserValue($2); }
;

an_fp_sort:
  FLOAT16_TOK
{
    $$ = namedFloatSize("Float16");
}
| FLOAT32_TOK
{
    $$ = namedFloatSize("Float32");
}
| FLOAT64_TOK
{
    $$ = namedFloatSize("Float64");
}
| FLOAT128_TOK
{
    $$ = namedFloatSize("Float128");
}
| LPAREN_TOK UNDERSCORE_TOK FLOATINGPOINT_TOK NUMERAL_TOK NUMERAL_TOK RPAREN_TOK
{
    // Through the shared funnel: the sort rule used to carry its own copy of
    // the floor, which is how the two came to disagree about what a usable
    // format is.
    checkFpFormatWidths($4, $5);
    $$ = new stp::float_size($4, $5);
}
;

sort_parameter_open:
LPAREN_TOK { stringOnly = true; }
;
sort_parameter_close:
RPAREN_TOK { stringOnly = false; }
;

sort_parameters:
  %empty
| sort_parameters sort_parameter_name
{
  stp::GlobalParserInterface->addSortParameter(*$2);
  stp::releaseParserValue($2);
}
;

sort_parameter_name:
  STRING_TOK { $$ = $1; }
| BOOL_TOK { $$ = new std::string("Bool"); }
| REAL_TOK { $$ = new std::string("Real"); }
| ROUNDINGMODE_TOK { $$ = new std::string("RoundingMode"); }
| FLOAT16_TOK { $$ = new std::string("Float16"); }
| FLOAT32_TOK { $$ = new std::string("Float32"); }
| FLOAT64_TOK { $$ = new std::string("Float64"); }
| FLOAT128_TOK { $$ = new std::string("Float128"); }
| ARRAY_TOK { $$ = new std::string("Array"); }
| BITVEC_TOK { $$ = new std::string("BitVec"); }
| FLOATINGPOINT_TOK { $$ = new std::string("FloatingPoint"); }
;

sort_context:
%empty { stp::SMT2SetSortContext(true); }
;

resolved_sort:
sort_context sort_expression
{
  $$ = new stp::SourceSort(stp::GlobalParserInterface->resolveSort(*$2));
  stp::releaseParserValue($2);
  stp::SMT2SetSortContext(false);
}
;

sort_expression:
  BOOL_TOK { $$ = new stp::SMT2Sort(stp::GlobalParserInterface->sortAtom("Bool", stp::SourceSort::boolean())); }
| REAL_TOK { $$ = new stp::SMT2Sort(stp::GlobalParserInterface->sortAtom("Real", stp::SourceSort::real())); }
| ROUNDINGMODE_TOK { $$ = new stp::SMT2Sort(stp::GlobalParserInterface->sortAtom("RoundingMode", stp::SourceSort::roundingMode())); }
| LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK command_numeral RPAREN_TOK
{
  checkBitVectorWidth($4);
  $$ = new stp::SMT2Sort(stp::SourceSort::bitVector($4));
}
| an_fp_sort
{
  $$ = new stp::SMT2Sort(stp::SourceSort::floatingPoint($1->exp_bits, $1->sig_bits));
  stp::releaseParserValue($1);
}
| STRING_TOK
{
  $$ = namedSortExpression(*$1);
  stp::releaseParserValue($1);
}
| sort_application { $$ = $1; }
| array_sort_expression { $$ = $1; }
;

sort_arguments:
sort_expression
{
  $$ = new std::vector<stp::SMT2Sort>{*$1};
  stp::releaseParserValue($1);
}
| sort_arguments sort_expression
{
  $$ = $1;
  $$->push_back(*$2);
  stp::releaseParserValue($2);
}
;

sort_application:
LPAREN_TOK STRING_TOK sort_arguments RPAREN_TOK
{
  $$ = namedSortExpression(*$2, *$3);
  stp::releaseParserValue($2);
  stp::releaseParserValue($3);
}
;

array_sort_expression:
LPAREN_TOK ARRAY_TOK sort_expression sort_expression RPAREN_TOK
{
  $$ = new stp::SMT2Sort(stp::SMT2Sort::array(*$3, *$4));
  stp::releaseParserValue($3);
  stp::releaseParserValue($4);
}
;

an_array_sort:
array_sort_expression
{
  const stp::SourceSort sort = stp::GlobalParserInterface->resolveSort(*$1);
  $$ = new stp::array_sort{stp::array_sort_component(sort.index()),
                          stp::array_sort_component(sort.element())};
  stp::releaseParserValue($1);
}
;

var_decl:
STRING_TOK LPAREN_TOK RPAREN_TOK resolved_sort
{
  ABANDON_IF_REDECLARED_ZERO_ARITY((stp::releaseParserValue($1), stp::releaseParserValue($4)));
  declareScalarSymbol($1, *$4);
  stp::releaseParserValue($4);
}
| uf_decl_name uf_domain_sorts RPAREN_TOK uf_codomain_sort
{
  std::vector<stp::SourceSort> domain;
  domain.reserve($2->size());
  for (size_t i = 0; i < $2->size(); ++i)
  {
    const stp::parsed_uf_sort& parsed = (*$2)[i];
    // The first unsupported sort is the one reported: refusing does not come
    // back, so there is no second one to suppress.
    if (!parsed.supported)
      stp::GlobalParserInterface->refuseCurrentCommand(
          unsupportedUFDomainSort(*$1, parsed, i));
    domain.push_back(parsed.sort);
  }
  if (!$4->supported)
    stp::GlobalParserInterface->refuseCurrentCommand(
        unsupportedUFResultSort(*$1, *$4));

  std::string diagnostic;
  const stp::UFDecl* declaration =
      stp::GlobalParserInterface->declareScopedUninterpretedFunction(
          *$1, domain, $4->sort, &diagnostic);
  if (declaration == NULL)
    stp::GlobalParserInterface->refuseCurrentCommand(diagnostic);
  stp::releaseParserValue($1);
  stp::releaseParserValue($2);
  stp::releaseParserValue($4);
}
;

// A nonempty domain distinguishes a UF declaration from the existing
// zero-arity symbol productions. The action runs only after the next token
// has selected this branch, so feature-off reports the pinned legacy error at
// the first domain sort and abandons the remainder of the script.
uf_decl_name:
STRING_TOK LPAREN_TOK
{
  if (!stp::GlobalParserInterface->getUserFlags()
           .enable_uninterpreted_functions)
  {
    // The first domain token selected this branch, and the legacy grammar
    // rejected the declaration at that token. Use Bison's generated symbol
    // table so the diagnostic retains the exact token name. yytname and
    // YYTRANSLATE are available throughout STP's supported Bison range;
    // yysymbol_name and the prefixed empty-token enum are newer additions.
    std::string message = "syntax error, unexpected ";
    message += yychar < 0 ? "end of file" : yytname[YYTRANSLATE(yychar)];
    message += ", expecting RPAREN_TOK";
    yyerror(message.c_str());
    stp::releaseParserValue($1);
    YYABORT;
  }
  // The first domain token proves this declaration is nonzero-arity: the
  // only shape that continues into the nonfatal UF declaration funnel over
  // a known name. Retire the lexer's record of the classification the name
  // would have carried; the funnel reports collisions itself.
  stp::SMT2ConsumeDeclassifiedName();
  $$ = $1;
}
;

uf_domain_sorts:
uf_sort
{
  $$ = new std::vector<stp::parsed_uf_sort>();
  $$->push_back(std::move(*$1));
  stp::releaseParserValue($1);
}
| uf_domain_sorts uf_sort
{
  $1->push_back(std::move(*$2));
  stp::releaseParserValue($2);
  $$ = $1;
}
;

uf_sort:
LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK
{
  if ($4 == 0)
    $$ = new stp::parsed_uf_sort(stp::SourceSort::unknown(),
                                 "(_ BitVec 0)", false);
  else
  {
    const stp::SourceSort sort = stp::SourceSort::bitVector($4);
    $$ = new stp::parsed_uf_sort(
        sort, stp::sourceSortToSMTLib(sort), true);
  }
}
| BOOL_TOK
{
  $$ = new stp::parsed_uf_sort(stp::SourceSort::boolean(), "Bool", true);
}
| REAL_TOK
{
  // Solved at its own sort, like Bool: no carrier, no packed width. The
  // congruence relation over Real applications is decided from equality
  // atoms rather than from byte patterns.
  $$ = new stp::parsed_uf_sort(stp::SourceSort::real(), "Real", true);
}
| an_array_sort
{
  const stp::SourceSort sort = $1->sourceSort();
  $$ = new stp::parsed_uf_sort(
      sort, stp::sourceSortToSMTLib(sort), false);
  stp::releaseParserValue($1);
}
| an_fp_sort
{
  const stp::SourceSort sort =
      stp::SourceSort::floatingPoint($1->exp_bits, $1->sig_bits);
  $$ = new stp::parsed_uf_sort(
      sort, stp::sourceSortToSMTLib(sort), true);
  stp::releaseParserValue($1);
}
| ROUNDINGMODE_TOK
{
  $$ = new stp::parsed_uf_sort(
      stp::SourceSort::roundingMode(), "RoundingMode", true);
}
| STRING_TOK
{
  // A bare name in a signature: a sort the script introduced, by declare-sort
  // or by define-sort. Anything else is genuinely unknown and is reported
  // with its spelling by the caller.
  stp::SourceSort resolved;
  if (stp::GlobalParserInterface->lookupSortAlias(*$1, resolved))
    $$ = new stp::parsed_uf_sort(resolved, *$1, resolved.kind() != stp::SourceSort::Kind::Array);
  else
    $$ = new stp::parsed_uf_sort(
        stp::SourceSort::unknown(), *$1, false, false);
  stp::releaseParserValue($1);
}
| sort_application
{
  const stp::SourceSort sort = stp::GlobalParserInterface->resolveSort(*$1);
  $$ = new stp::parsed_uf_sort(sort, stp::sourceSortToSMTLib(sort),
                              sort.kind() != stp::SourceSort::Kind::Array);
  stp::releaseParserValue($1);
}

;

uf_codomain_sort:
LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK
{
  if ($4 == 0)
    $$ = new stp::parsed_uf_sort(stp::SourceSort::unknown(),
                                 "(_ BitVec 0)", false);
  else
  {
    const stp::SourceSort sort = stp::SourceSort::bitVector($4);
    $$ = new stp::parsed_uf_sort(
        sort, stp::sourceSortToSMTLib(sort), true);
  }
}
| BOOL_TOK
{
  $$ = new stp::parsed_uf_sort(stp::SourceSort::boolean(), "Bool", true);
}
| REAL_TOK
{
  // Solved at its own sort, like Bool: no carrier, no packed width. The
  // congruence relation over Real applications is decided from equality
  // atoms rather than from byte patterns.
  $$ = new stp::parsed_uf_sort(stp::SourceSort::real(), "Real", true);
}
| an_array_sort
{
  const stp::SourceSort sort = $1->sourceSort();
  $$ = new stp::parsed_uf_sort(
      sort, stp::sourceSortToSMTLib(sort), false);
  stp::releaseParserValue($1);
}
| an_fp_sort
{
  const stp::SourceSort sort =
      stp::SourceSort::floatingPoint($1->exp_bits, $1->sig_bits);
  $$ = new stp::parsed_uf_sort(
      sort, stp::sourceSortToSMTLib(sort), true);
  stp::releaseParserValue($1);
}
| ROUNDINGMODE_TOK
{
  $$ = new stp::parsed_uf_sort(
      stp::SourceSort::roundingMode(), "RoundingMode", true);
}
| STRING_TOK
{
  stp::SourceSort resolved;
  if (stp::GlobalParserInterface->lookupSortAlias(*$1, resolved))
    $$ = new stp::parsed_uf_sort(resolved, *$1, resolved.kind() != stp::SourceSort::Kind::Array);
  else
    $$ = new stp::parsed_uf_sort(
        stp::SourceSort::unknown(), *$1, false, false);
  stp::releaseParserValue($1);
}
| sort_application
{
  const stp::SourceSort sort = stp::GlobalParserInterface->resolveSort(*$1);
  $$ = new stp::parsed_uf_sort(sort, stp::sourceSortToSMTLib(sort),
                              sort.kind() != stp::SourceSort::Kind::Array);
  stp::releaseParserValue($1);
}

;

const_decl:
STRING_TOK resolved_sort
{
  declareScalarSymbol($1, *$2);
  stp::releaseParserValue($2);
}
;

an_mixed:
an_formula
{
  $$ = new ASTVec;
  if ($1 != NULL) {
    $$->push_back(*$1);
    stp::GlobalParserInterface->deleteNode($1);
  }
}
|
an_term
{
  $$ = new ASTVec;
  if ($1 != NULL) {
    $$->push_back(*$1);
    stp::GlobalParserInterface->deleteNode($1);
  }
}
|
an_mixed an_formula
{
  if ($1 != NULL && $2 != NULL) {
    $1->push_back(*$2);
    $$ = $1;
    stp::GlobalParserInterface->deleteNode($2);
  }
}
|
an_mixed an_term
{
  if ($1 != NULL && $2 != NULL) {
    $1->push_back(*$2);
    $$ = $1;
    stp::GlobalParserInterface->deleteNode($2);
  }
};

an_formulas:
an_formula
{
  $$ = new ASTVec;
  if ($1 != NULL) {
    $$->push_back(*$1);
    stp::GlobalParserInterface->deleteNode($1);
  }
}
|
an_formulas an_formula
{
  if ($1 != NULL && $2 != NULL) {
    $1->push_back(*$2);
    $$ = $1;
    stp::GlobalParserInterface->deleteNode($2);
  }
}
;

/* Qualified identifiers: qualification selects a result sort; it never
   converts a value. Separate heads keep the existing term/formula grammar
   conflict-free and share every operation's original construction path. */

id_and:
  AND_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK AND_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_array_functionid:
  ARRAY_FUNCTIONID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK ARRAY_FUNCTIONID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->function.GetSourceSort());
  $$ = $3;
}
;

id_bitvector_functionid:
  BITVECTOR_FUNCTIONID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK BITVECTOR_FUNCTIONID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->function.GetSourceSort());
  $$ = $3;
}
;

id_boolean_functionid:
  BOOLEAN_FUNCTIONID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK BOOLEAN_FUNCTIONID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->function.GetSourceSort());
  $$ = $3;
}
;

id_bvand:
  BVAND_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVAND_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvarithrightshift:
  BVARITHRIGHTSHIFT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVARITHRIGHTSHIFT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvcomp:
  BVCOMP_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVCOMP_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvconcat:
  BVCONCAT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVCONCAT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvdiv:
  BVDIV_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVDIV_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvge:
  BVGE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVGE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvgt:
  BVGT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVGT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvle:
  BVLE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVLE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvleftshift_1:
  BVLEFTSHIFT_1_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVLEFTSHIFT_1_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvlt:
  BVLT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVLT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvmod:
  BVMOD_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVMOD_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvmult:
  BVMULT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVMULT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvnand:
  BVNAND_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVNAND_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvneg:
  BVNEG_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVNEG_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvnego:
  BVNEGO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVNEGO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvnor:
  BVNOR_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVNOR_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvnot:
  BVNOT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVNOT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvor:
  BVOR_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVOR_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvplus:
  BVPLUS_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVPLUS_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvrightshift_1:
  BVRIGHTSHIFT_1_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVRIGHTSHIFT_1_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvsaddo:
  BVSADDO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVSADDO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvsdivo:
  BVSDIVO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVSDIVO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvsge:
  BVSGE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVSGE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvsgt:
  BVSGT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVSGT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvsle:
  BVSLE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVSLE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvslt:
  BVSLT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVSLT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvsmulo:
  BVSMULO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVSMULO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvssubo:
  BVSSUBO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVSSUBO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvsub:
  BVSUB_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVSUB_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvuaddo:
  BVUADDO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVUADDO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvumulo:
  BVUMULO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVUMULO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvusubo:
  BVUSUBO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVUSUBO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvxnor:
  BVXNOR_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVXNOR_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvxor:
  BVXOR_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK BVXOR_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_declaredsort_functionid:
  DECLAREDSORT_FUNCTIONID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK DECLAREDSORT_FUNCTIONID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->function.GetSourceSort());
  $$ = $3;
}
;

id_distinct:
  DISTINCT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK DISTINCT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_eq:
  EQ_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK EQ_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_false:
  FALSE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FALSE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_floatingpoint_functionid:
  FLOATINGPOINT_FUNCTIONID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK FLOATINGPOINT_FUNCTIONID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->function.GetSourceSort());
  $$ = $3;
}
;

id_formid:
  FORMID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK FORMID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->GetSourceSort());
  $$ = $3;
}
;

id_fp:
  FP_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_abs:
  FP_ABS_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ABS_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_add:
  FP_ADD_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ADD_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_div:
  FP_DIV_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_DIV_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_eq:
  FP_EQ_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_EQ_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_fma:
  FP_FMA_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_FMA_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_geq:
  FP_GEQ_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_GEQ_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_gt:
  FP_GT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_GT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_isinfinite:
  FP_ISINFINITE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ISINFINITE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_isnan:
  FP_ISNAN_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ISNAN_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_isnegative:
  FP_ISNEGATIVE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ISNEGATIVE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_isnormal:
  FP_ISNORMAL_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ISNORMAL_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_ispositive:
  FP_ISPOSITIVE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ISPOSITIVE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_issubnormal:
  FP_ISSUBNORMAL_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ISSUBNORMAL_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_iszero:
  FP_ISZERO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ISZERO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_leq:
  FP_LEQ_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_LEQ_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_lt:
  FP_LT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_LT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_max:
  FP_MAX_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_MAX_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_min:
  FP_MIN_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_MIN_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_mul:
  FP_MUL_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_MUL_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_neg:
  FP_NEG_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_NEG_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_rem:
  FP_REM_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_REM_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_rm_roundnearesttiestoaway:
  FP_RM_ROUNDNEARESTTIESTOAWAY_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_RM_ROUNDNEARESTTIESTOAWAY_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_rm_roundnearesttiestoeven:
  FP_RM_ROUNDNEARESTTIESTOEVEN_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_RM_ROUNDNEARESTTIESTOEVEN_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_rm_roundtowardnegative:
  FP_RM_ROUNDTOWARDNEGATIVE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_RM_ROUNDTOWARDNEGATIVE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_rm_roundtowardpositive:
  FP_RM_ROUNDTOWARDPOSITIVE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_RM_ROUNDTOWARDPOSITIVE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_rm_roundtowardzero:
  FP_RM_ROUNDTOWARDZERO_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_RM_ROUNDTOWARDZERO_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_roundtointegral:
  FP_ROUNDTOINTEGRAL_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_ROUNDTOINTEGRAL_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_sqrt:
  FP_SQRT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_SQRT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_sub:
  FP_SUB_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_SUB_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_to_ieee_bv:
  FP_TO_IEEE_BV_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_TO_IEEE_BV_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_fp_to_real:
  FP_TO_REAL_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK FP_TO_REAL_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_implies:
  IMPLIES_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK IMPLIES_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_ite:
  ITE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK ITE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_not:
  NOT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK NOT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_or:
  OR_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK OR_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_real_add:
  REAL_ADD_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK REAL_ADD_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_real_div:
  REAL_DIV_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK REAL_DIV_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_real_functionid:
  REAL_FUNCTIONID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK REAL_FUNCTIONID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->function.GetSourceSort());
  $$ = $3;
}
;

id_real_ge:
  REAL_GE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK REAL_GE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_real_gt:
  REAL_GT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK REAL_GT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_real_le:
  REAL_LE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK REAL_LE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_real_lt:
  REAL_LT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK REAL_LT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_real_mul:
  REAL_MUL_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK REAL_MUL_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_real_sub:
  REAL_SUB_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK REAL_SUB_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_roundingmode_functionid:
  ROUNDINGMODE_FUNCTIONID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK ROUNDINGMODE_FUNCTIONID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->function.GetSourceSort());
  $$ = $3;
}
;

id_sbvdiv:
  SBVDIV_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK SBVDIV_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_sbvmod:
  SBVMOD_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK SBVMOD_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_sbvrem:
  SBVREM_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK SBVREM_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_select:
  SELECT_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK SELECT_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_store:
  STORE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK STORE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_termid:
  TERMID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK TERMID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->GetSourceSort());
  $$ = $3;
}
;

id_true:
  TRUE_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK TRUE_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_uf_bool_functionid:
  UF_BOOL_FUNCTIONID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK UF_BOOL_FUNCTIONID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->signature().codomain());
  $$ = $3;
}
;

id_uf_bv_functionid:
  UF_BV_FUNCTIONID_TOK { $$ = $1; }
| LPAREN_TOK AS_TOK UF_BV_FUNCTIONID_TOK resolved_sort RPAREN_TOK
{
  checkQualifiedSort($4, $3->signature().codomain());
  $$ = $3;
}
;

id_xor:
  XOR_TOK { $$ = nullptr; }
| LPAREN_TOK AS_TOK XOR_TOK resolved_sort RPAREN_TOK { $$ = $4; }
;

id_bvconst_decimal:
  id_bvconst_decimal_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_bvconst_decimal_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_bvconst_decimal_bare:
  LPAREN_TOK UNDERSCORE_TOK BVCONST_DECIMAL_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->digits = *$3;
  stp::releaseParserValue($3);
  $$->first = $4;
}
;

id_bvextract:
  id_bvextract_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_bvextract_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_bvextract_bare:
  LPAREN_TOK UNDERSCORE_TOK BVEXTRACT_TOK NUMERAL_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
  $$->second = $5;
}
;

id_bvrepeat:
  id_bvrepeat_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_bvrepeat_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_bvrepeat_bare:
  LPAREN_TOK UNDERSCORE_TOK BVREPEAT_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
}
;

id_bvrotate_left:
  id_bvrotate_left_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_bvrotate_left_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_bvrotate_left_bare:
  LPAREN_TOK UNDERSCORE_TOK BVROTATE_LEFT_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
}
;

id_bvrotate_right:
  id_bvrotate_right_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_bvrotate_right_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_bvrotate_right_bare:
  LPAREN_TOK UNDERSCORE_TOK BVROTATE_RIGHT_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
}
;

id_bvsx:
  id_bvsx_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_bvsx_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_bvsx_bare:
  LPAREN_TOK UNDERSCORE_TOK BVSX_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
}
;

id_bvzx:
  id_bvzx_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_bvzx_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_bvzx_bare:
  LPAREN_TOK UNDERSCORE_TOK BVZX_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
}
;

id_fp_special:
  id_fp_special_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_fp_special_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_fp_special_bare:
  LPAREN_TOK UNDERSCORE_TOK an_fp_const NUMERAL_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->tag = $3;
  $$->first = $4;
  $$->second = $5;
}
;

id_fp_to_sbv:
  id_fp_to_sbv_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_fp_to_sbv_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_fp_to_sbv_bare:
  LPAREN_TOK UNDERSCORE_TOK FP_TO_SBV_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
}
;

id_fp_to_ubv:
  id_fp_to_ubv_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_fp_to_ubv_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_fp_to_ubv_bare:
  LPAREN_TOK UNDERSCORE_TOK FP_TO_UBV_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
}
;

id_fp_tofp:
  id_fp_tofp_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_fp_tofp_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_fp_tofp_bare:
  LPAREN_TOK UNDERSCORE_TOK FP_TOFP_TOK NUMERAL_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
  $$->second = $5;
}
;

id_fp_tofp_unsigned:
  id_fp_tofp_unsigned_bare { $$ = $1; }
| LPAREN_TOK AS_TOK id_fp_tofp_unsigned_bare resolved_sort RPAREN_TOK
{
  $$ = $3;
  $$->qualifier = $4;
}
;
id_fp_tofp_unsigned_bare:
  LPAREN_TOK UNDERSCORE_TOK FP_TOFP_UNSIGNED_TOK NUMERAL_TOK NUMERAL_TOK RPAREN_TOK
{
  $$ = new ParsedIndexedIdentifier;
  $$->first = $4;
  $$->second = $5;
}
;

an_formula:
id_true
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(TRUE));
  assert(0 == $$->GetIndexWidth());
  assert(0 == $$->GetValueWidth());
  checkQualifiedResult($1, $$);
}
| id_false
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(FALSE));
  assert(0 == $$->GetIndexWidth());
  assert(0 == $$->GetValueWidth());
  checkQualifiedResult($1, $$);
}
|
id_formid
{
  $$ = stp::GlobalParserInterface->newNode(*$1); //todo creating then deleting same?
  stp::GlobalParserInterface->deleteNode($1);
}
| LPAREN_TOK an_fp_predicate RPAREN_TOK
{
   $$ = $2;
}
| LPAREN_TOK id_real_lt an_terms RPAREN_TOK
{
  $$ = createExactRealPredicate(stp::REAL_LT, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_real_le an_terms RPAREN_TOK
{
  $$ = createExactRealPredicate(stp::REAL_LE, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_real_gt an_terms RPAREN_TOK
{
  $$ = createExactRealPredicate(stp::REAL_GT, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_real_ge an_terms RPAREN_TOK
{
  $$ = createExactRealPredicate(stp::REAL_GE, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_eq an_mixed RPAREN_TOK
{
  const ASTVec& terms = *$3;

  // Reject an ill-sorted = up front. The simplifying factory folds constant
  // operands before any type check can see them, so a width mismatch here
  // would otherwise be "solved" (to false) rather than diagnosed.
  checkSameSourceSort(terms, "= requires operands of the same sort");

  bool one_float = false;
  bool one_boolean = false;
  for (unsigned i = 0; i < terms.size();i++)
  {
    one_float |= (terms[i].GetSourceSort().kind() ==
                  stp::SourceSort::Kind::FloatingPoint);
    one_boolean |= (terms[i].GetSourceSort().kind() ==
                    stp::SourceSort::Kind::Bool);
  }

  Kind k = one_float ? FP_SMT_EQ : (one_boolean ? IFF : EQ);

  if (terms.size() ==2)
  {
    $$ = createNode(k, $3);
  }
  else  if (terms.size() >2) 
  {
    ASTVec result;
    result.reserve(terms.size()-1);
    for (unsigned i =1; i < terms.size();i++)
    {
        result.push_back(stp::GlobalParserInterface->CreateNode(k, terms[i], terms[i-1]));
    }
    $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(AND, result));
    stp::releaseParserValue($3);
  }
  else
  {
    fatal_yyerror("too few arguments to eq."); 
  }
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_distinct an_terms RPAREN_TOK
{
  using namespace stp;

  ASTVec terms = *$3;

  checkSameSourceSort(terms, "distinct requires operands of the same sort");

  // More operands than the sort has values: refuse the group here rather than
  // hand the solver the C(n, 2) encoding of a pigeonhole it cannot search.
  if (!terms.empty() &&
      distinctExceedsCardinality(terms[0].GetSourceSort(), terms.size()))
  {
    $$ = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->CreateNode(FALSE));
  }
  else
  {
    if (terms.size() < 2)
      fatal_yyerror("too few arguments to distinct");
    $$ = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->CreateNode(DISTINCT, terms));
  }

  stp::releaseParserValue($3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_distinct an_formulas RPAREN_TOK
{
  using namespace stp;

  ASTVec terms = *$3;

  checkSameSourceSort(terms, "distinct requires operands of the same sort");

  // More operands than the sort has values: refuse the group here rather than
  // hand the solver the C(n, 2) encoding of a pigeonhole it cannot search.
  if (!terms.empty() &&
      distinctExceedsCardinality(terms[0].GetSourceSort(), terms.size()))
  {
    $$ = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->CreateNode(FALSE));
  }
  else
  {
    if (terms.size() < 2)
      fatal_yyerror("too few arguments to distinct");
    $$ = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->CreateNode(DISTINCT, terms));
  }

  stp::releaseParserValue($3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvslt an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSLT, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvsle an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSLE, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvsgt an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSGT, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvsge an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSGE, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvlt an_term an_term RPAREN_TOK
{
  $$ = createNode(BVLT, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvle an_term an_term RPAREN_TOK
{
  $$ = createNode(BVLE, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvgt an_term an_term RPAREN_TOK
{
  $$ = createNode(BVGT, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvge an_term an_term RPAREN_TOK
{
  $$ = createNode(BVGE, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvuaddo an_term an_term RPAREN_TOK
{
  $$ = createNode(BVUADDO, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvsaddo an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSADDO, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvumulo an_term an_term RPAREN_TOK
{
  $$ = createNode(BVUMULO, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvsmulo an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSMULO, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvusubo an_term an_term RPAREN_TOK
{
  $$ = createNode(BVUSUBO, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvssubo an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSSUBO, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvsdivo an_term an_term RPAREN_TOK
{
  $$ = createSDivOverflow($3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvnego an_term RPAREN_TOK
{
  $$ = createNegOverflow($3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK an_formula RPAREN_TOK
{
  $$ = $2;
}
| LPAREN_TOK id_not an_formula RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateNode(NOT, *$3));
  stp::GlobalParserInterface->deleteNode( $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_implies an_formulas RPAREN_TOK
{
  ASTVec forms = *$3;

  if(forms.size() < 2)
    fatal_yyerror("implies should have 2 or more operands");

  while(forms.size() >=2 )
  {
     ASTNode n1 = forms.back();
     forms.pop_back();
     ASTNode n0 = forms.back();
     forms.pop_back();

     ASTNode n = stp::GlobalParserInterface->nf->CreateNode(IMPLIES, n0, n1);
     forms.push_back(n);
  }

  $$ = stp::GlobalParserInterface->newNode(forms[0]);
  stp::releaseParserValue($3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_ite an_formula an_formula an_formula RPAREN_TOK
{
  if (!$4->GetSourceSort().isKnown() ||
      $4->GetSourceSort() != $5->GetSourceSort())
    fatal_yyerror("ite branches must have the same sort");
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateNode(ITE, *$3, *$4, *$5));
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
  stp::GlobalParserInterface->deleteNode( $5);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_and an_formulas RPAREN_TOK
{
 $$ = createNode(AND, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_or an_formulas RPAREN_TOK
{
  $$ = createNode(OR, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_xor an_formulas RPAREN_TOK
{
  $$ = createNode(XOR, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK LET_TOK lets an_formula RPAREN_TOK
  {
    $$ = $4;
    stp::GlobalParserInterface->letMgr->pop();
  }
| LPAREN_TOK id_boolean_functionid an_mixed RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(applyFunctionChecked(*$2,*$3));
  stp::releaseParserValue($3);
}
| LPAREN_TOK id_uf_bool_functionid an_mixed RPAREN_TOK
{
  $$ = applyParsedUF($2, *$3);
  stp::releaseParserValue($3);
}
| LPAREN_TOK id_uf_bool_functionid RPAREN_TOK
{
  $$ = applyParsedUF($2, ASTVec());
}
| id_boolean_functionid
{
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(applyFunctionChecked(*$1,empty));
}
| annotation_open an_formula annotation_attributes attributes RPAREN_TOK
{
  annotateTerm($1, *$2, *$4);
  stp::releaseParserValue($4);
  $$ = $2;
}
;

lets: LPAREN_TOK
{
    stp::GlobalParserInterface->letMgr->push();
}
inside-lets
RPAREN_TOK
{
  // We don't want any of the lets we've just created to intefere with each other, so keep them out of resolution until now.

  stp::GlobalParserInterface->letMgr->commit();
};

inside-lets: let inside-lets
| let
{};

let: LPAREN_TOK
{
  // Set lexer to only return symbols.
  stringOnly = true;
} 
  STRING_TOK
{
  // Set it back to normal.
  stringOnly = false;
}
  definition_body RPAREN_TOK
{
  stp::GlobalParserInterface->letMgr->LetExprMgr(*$3, *$5);
  stp::releaseParserValue($3);
  stp::releaseParserValue($5);
}
;

an_terms:
an_term
{
  $$ = new ASTVec;
  if ($1 != NULL) {
    $$->push_back(*$1);
    stp::GlobalParserInterface->deleteNode( $1);

  }
}
|
an_terms an_term
{
  if ($1 != NULL && $2 != NULL) {
    $1->push_back(*$2);
    $$ = $1;
    stp::GlobalParserInterface->deleteNode( $2);
  }
}
;

an_const:
BVCONST_HEXIDECIMAL_TOK
{
  unsigned width = $1->length()*4;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst(*$1, 16, width));
  $$->SetValueWidth(width);
  stp::releaseParserValue($1);
}
| BVCONST_BINARY_TOK
{
  unsigned width = $1->length();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst(*$1, 2, width));
  $$->SetValueWidth(width);
  stp::releaseParserValue($1);
}
| id_fp an_term an_term an_term
{
  $$ = createFPFromParts($2, $3, $4);
  checkQualifiedResult($1, $$);
};

 /* The magnitude of a real constant: a decimal, or a numeral. Conversion is
    from the digits, so a magnitude is exact however many of them there are --
    the numerals that fit an unsigned arrive as their value and are printed
    back, the rest arrive as their text already. */
an_real_magnitude:
  DECIMAL_TOK
{
  $$ = $1;
}
| NUMERAL_TOK
{
  std::ostringstream os;
  os << $1;
  $$ = new std::string(os.str());
}
| BIG_NUMERAL_TOK
{
  $$ = $1;
}
;

 /* A concrete Real constant, the only Real term the QF_FP-family logics
    admit: a magnitude, (- x) negating one, or the rational spelling
    (/ p q), also negatable. '-' and '/' reach the parser as plain
    symbols (STRING_TOK), so which operator -- and its arity -- is
    checked in the action. */
an_real_constant:
  an_real_magnitude
{
  $$ = new ParsedRealConstant{$1, nullptr, false};
}
| LPAREN_TOK STRING_TOK an_real_constant RPAREN_TOK
{
  if (*$2 != "-")
  {
    fatal_yyerror("expected '-' (negation): the only unary operation on a "
                  "real constant");
  }
  stp::releaseParserValue($2);
  $$ = $3;
  $$->negative = !$$->negative;
}
| LPAREN_TOK STRING_TOK an_real_constant an_real_constant RPAREN_TOK
{
  if (*$2 != "/")
  {
    fatal_yyerror("expected '/' (a rational constant): the only binary "
                  "operation on real constants");
  }
  stp::releaseParserValue($2);
  if ($3->den != nullptr || $4->den != nullptr)
  {
    fatal_yyerror("a rational constant does not nest: write (/ p q), "
                  "(- (/ p q)) or (/ (- p) q)");
  }
  if ($4->negative)
  {
    fatal_yyerror("write a negative rational as (- (/ p q)) or (/ (- p) q), "
                  "not with a negative denominator");
  }
  $$ = $3;
  $$->den = $4->num;
  stp::releaseParserValue($4);
}
;

an_rounding_mode:
id_fp_rm_roundtowardzero
{
  $$ = stp::GlobalParserInterface->newNode(
      stp::GlobalParserInterface->CreateRMConst(ROUND_TOWARD_ZERO));
  checkQualifiedResult($1, $$);
}
| id_fp_rm_roundnearesttiestoeven
{
  $$ = stp::GlobalParserInterface->newNode(
      stp::GlobalParserInterface->CreateRMConst(ROUND_NEAREST_TIES_TO_EVEN));
  checkQualifiedResult($1, $$);
}
| id_fp_rm_roundnearesttiestoaway
{
  $$ = stp::GlobalParserInterface->newNode(
      stp::GlobalParserInterface->CreateRMConst(ROUND_NEAREST_TIES_TO_AWAY));
  checkQualifiedResult($1, $$);
}
| id_fp_rm_roundtowardpositive
{
  $$ = stp::GlobalParserInterface->newNode(
      stp::GlobalParserInterface->CreateRMConst(ROUND_TOWARD_POSITIVE));
  checkQualifiedResult($1, $$);
}
| id_fp_rm_roundtowardnegative
{
  $$ = stp::GlobalParserInterface->newNode(
      stp::GlobalParserInterface->CreateRMConst(ROUND_TOWARD_NEGATIVE));
  checkQualifiedResult($1, $$);
}
;

an_fp_const:
  FP_NAN_TOK { $$ = (unsigned)stp::FPSpecial::NaN; }
| FP_POS_INF_TOK { $$ = (unsigned)stp::FPSpecial::PlusInfinity; }
| FP_NEG_INF_TOK { $$ = (unsigned)stp::FPSpecial::MinusInfinity; }
| FP_POS_ZERO_TOK { $$ = (unsigned)stp::FPSpecial::PlusZero; }
| FP_NEG_ZERO_TOK { $$ = (unsigned)stp::FPSpecial::MinusZero; }
;

an_fp_term:
LPAREN_TOK id_fp_abs an_term RPAREN_TOK
{
  $$ = createFPUnary(FP_ABS, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_neg an_term RPAREN_TOK
{
  $$ = createFPUnary(FP_NEG, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_add an_term an_term an_term RPAREN_TOK
{
  $$ = createFPArith(FP_ADD, $3, $4, $5);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_sub an_term an_term an_term RPAREN_TOK
{
  $$ = createFPArith(FP_SUB, $3, $4, $5);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_mul an_term an_term an_term RPAREN_TOK
{
  $$ = createFPArith(FP_MUL, $3, $4, $5);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_div an_term an_term an_term RPAREN_TOK
{
  $$ = createFPArith(FP_DIV, $3, $4, $5);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_fma an_term an_term an_term an_term RPAREN_TOK
{
  $$ = createFPFma($3, $4, $5, $6);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_sqrt an_term an_term RPAREN_TOK
{
  $$ = createFPSqrt($3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_rem an_term an_term RPAREN_TOK
{
  $$ = createFPBinary(FP_REM, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_roundtointegral an_term an_term RPAREN_TOK
{
  $$ = createFPRoundToIntegral($3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_min an_term an_term RPAREN_TOK
{
  $$ = createFPBinary(FP_MIN, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_max an_term an_term RPAREN_TOK
{
  $$ = createFPBinary(FP_MAX, $3, $4);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_to_ubv an_term an_term RPAREN_TOK
{
  $$ = createFPToBV(FP_TO_UBV, $2->first, $3, $4);
  checkQualifiedResult($2->qualifier, $$);
  stp::releaseParserValue($2);
}
| LPAREN_TOK id_fp_to_sbv an_term an_term RPAREN_TOK
{
  $$ = createFPToBV(FP_TO_SBV, $2->first, $3, $4);
  checkQualifiedResult($2->qualifier, $$);
  stp::releaseParserValue($2);
}
| LPAREN_TOK id_fp_tofp an_term RPAREN_TOK
{
  // ((_ to_fp e s) bv) reinterprets the bits of a bitvector as an IEEE-754
  // float. STP already stores floats as their packed bit pattern, so this is
  // purely a retyping: keep the child and stamp the format onto it.
  $$ = createFPFromBits($2->first, $2->second, $3);
  checkQualifiedResult($2->qualifier, $$);
  stp::releaseParserValue($2);
}
| LPAREN_TOK id_fp_tofp an_term an_term RPAREN_TOK
{
  // ((_ to_fp e s) rm f) reformats an existing float under a rounding mode.
  $$ = createFPToFP($2->first, $2->second, $3, $4);
  checkQualifiedResult($2->qualifier, $$);
  stp::releaseParserValue($2);
}
| LPAREN_TOK id_fp_tofp_unsigned an_term an_term RPAREN_TOK
{
  $$ = createFPFromUnsignedBV($2->first, $2->second, $3, $4);
  checkQualifiedResult($2->qualifier, $$);
  stp::releaseParserValue($2);
}
| LPAREN_TOK id_fp_tofp an_term an_real_constant RPAREN_TOK
{
  $$ = createFPFromReal($2->first, $2->second, $3, $4);
  checkQualifiedResult($2->qualifier, $$);
  stp::releaseParserValue($2);
}
| LPAREN_TOK id_fp_tofp an_real_constant RPAREN_TOK
{
  $$ = nullptr;
  destroyParsedRealConstant($3);
  fatal_yyerror("converting a real literal needs a rounding mode, e.g. "
                "((_ to_fp 8 24) RNE 1.5); the one-argument form of to_fp "
                "reinterprets the packed bits of a bitvector");
  checkQualifiedResult($2->qualifier, $$);
  stp::releaseParserValue($2);
}
| LPAREN_TOK id_fp_to_real an_term RPAREN_TOK
{
  $$ = createFpToReal($3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_fp_to_ieee_bv an_term RPAREN_TOK
{
  $$ = createFPToIEEEBV($3);
  checkQualifiedResult($2, $$);
}
| id_fp_special
{
  // The special values are constants: build the packed interned constant
  // directly. A childless special-value node would hash-cons every format
  // of, say, NaN to one node, which whoever parsed last would re-stamp.
  uint32_t exp_width($1->first);
  uint32_t sig_width($1->second);
  checkFpFormatWidths(exp_width, sig_width);
  $$ = stp::GlobalParserInterface->newNode(
      stp::GlobalParserInterface->CreateFPSpecialConst(
          (stp::FPSpecial)$1->tag, exp_width, sig_width));
  checkQualifiedResult($1->qualifier, $$);
  stp::releaseParserValue($1);
}
;

// The Boolean-valued floating-point operations. Split from an_fp_term so
// that formula position derives exactly these (parenthesised by
// an_formula's rule) and term position derives exactly the float-valued
// ones -- the shared nonterminal used to make every fp expression reachable
// from both, which is where most of the grammar's reduce/reduce conflicts
// came from.
an_fp_predicate:
id_fp_leq an_terms
{
  $$ = createFPChain(FP_LEQ, $2, "fp.leq");
  checkQualifiedResult($1, $$);
}
| id_fp_lt an_terms
{
  $$ = createFPChain(FP_LT, $2, "fp.lt");
  checkQualifiedResult($1, $$);
}
| id_fp_geq an_terms
{
  $$ = createFPChain(FP_GEQ, $2, "fp.geq");
  checkQualifiedResult($1, $$);
}
| id_fp_gt an_terms
{
  $$ = createFPChain(FP_GT, $2, "fp.gt");
  checkQualifiedResult($1, $$);
}
| id_fp_eq an_terms
{
  // Through the same helper as the other chainable comparisons, gaining its
  // operand and format checks (the old inline version had none).
  $$ = createFPChain(FP_EQ, $2, "fp.eq");
  checkQualifiedResult($1, $$);
}
| id_fp_isnormal an_term
{
  $$ = createFPPredicate(FP_ISNORMAL, $2);
  checkQualifiedResult($1, $$);
}
| id_fp_issubnormal an_term
{
  $$ = createFPPredicate(FP_ISSUBNORMAL, $2);
  checkQualifiedResult($1, $$);
}
| id_fp_iszero an_term
{
  $$ = createFPPredicate(FP_ISZERO, $2);
  checkQualifiedResult($1, $$);
}
| id_fp_isinfinite an_term
{
  $$ = createFPPredicate(FP_ISINFINITE, $2);
  checkQualifiedResult($1, $$);
}
| id_fp_isnan an_term
{
  $$ = createFPPredicate(FP_ISNAN, $2);
  checkQualifiedResult($1, $$);
}
| id_fp_isnegative an_term
{
  $$ = createFPPredicate(FP_ISNEGATIVE, $2);
  checkQualifiedResult($1, $$);
}
| id_fp_ispositive an_term
{
  $$ = createFPPredicate(FP_ISPOSITIVE, $2);
  checkQualifiedResult($1, $$);
}
;

an_term:
LPAREN_TOK AS_TOK ABSTRACT_VALUE_TOK resolved_sort RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(
      stp::GlobalParserInterface->abstractValue(*$3, *$4));
  stp::releaseParserValue($3);
  stp::releaseParserValue($4);
}
| id_termid
{
  $$ = stp::GlobalParserInterface->newNode((*$1));
  stp::GlobalParserInterface->deleteNode( $1);
}
| id_real_functionid
{
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(
      applyFunctionChecked(*$1, empty));
  if ($$->GetSourceSort().kind() != stp::SourceSort::Kind::Real)
    fatal_yyerror("Real define-fun alias did not return Real sort");
}
| LPAREN_TOK id_real_functionid an_mixed RPAREN_TOK
{
  // A Real-returning macro applied to arguments. Substitution happens
  // here, so what leaves this rule is an ordinary Real term.
  $$ = stp::GlobalParserInterface->newNode(
      applyFunctionChecked(*$2, *$3));
  if ($$->GetSourceSort().kind() != stp::SourceSort::Kind::Real)
    fatal_yyerror("Real define-fun did not return Real sort");
  stp::releaseParserValue($3);
}
| REAL_NUMERAL_TOK
{
  $$ = createExactRealLiteral($1);
}
| REAL_DECIMAL_TOK
{
  $$ = createExactRealLiteral($1);
}
| id_array_functionid
{
  // A use of a nullary array-sorted define-fun expands to its body.
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(applyFunctionChecked(*$1,empty));
}
| LPAREN_TOK an_term RPAREN_TOK
{
  $$ = $2;
} 
| an_const
{
  $$ = $1;
}
| an_fp_term
{
  $$ = $1;
}
| an_rounding_mode
{
  /* A rounding mode is a term: it appears in equalities ((= r RNE), and the
     declaration constraint built from them), so it must be derivable here,
     not only in the dedicated rounding-mode operand slots. */
  $$ = $1;
}
| LPAREN_TOK id_real_add an_terms RPAREN_TOK
{
  $$ = createExactRealTerm(stp::REAL_ADD, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_real_sub an_terms RPAREN_TOK
{
  $$ = createExactRealTerm(stp::REAL_SUB, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_real_mul an_terms RPAREN_TOK
{
  $$ = createExactRealTerm(stp::REAL_MUL, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_real_div an_terms RPAREN_TOK
{
  $$ = createExactRealTerm(stp::REAL_DIV, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK AS_TOK STRING_TOK resolved_sort RPAREN_TOK an_term
{
  // ((as const (Array I E)) v): the array whose every cell is v, the only
  // constant-array extension. The manager registers the
  // symbol with its default and interns by (sort, default), so the same
  // text names the same array wherever it occurs.
  // Like select, store and the grammar's other operator productions, this
  // one has no parentheses of its own: the generic ( an_term ) rule gives
  // the standard form, and the bare (as const S) v inside another term is
  // accepted as a bare select a i always has been. STP prints the standard
  // form only.
  // Both refusals end the parse, not the process (fatal_yyerror): an API
  // parse reports them as a parse error, the command line exits with them.
  if (*$3 != "const")
  {
    stp::releaseParserValue($3);
    stp::releaseParserValue($4);
    stp::GlobalParserInterface->deleteNode($6);
    fatal_yyerror("only (as const ...) is supported after 'as'");
  }
  const stp::SourceSort array_sort = *$4;
  if (array_sort.kind() != stp::SourceSort::Kind::Array)
    fatal_yyerror("constant arrays require an Array result sort");
  ASTNode value = *$6;
  if (value.GetSourceSort() != array_sort.element())
  {
    stp::releaseParserValue($3);
    stp::releaseParserValue($4);
    stp::GlobalParserInterface->deleteNode($6);
    fatal_yyerror("the default of a constant array must have the array's "
                  "element sort");
  }
  // Only a value (STPMgr::CreateConstArray says why).
  const ASTNode free_symbol = stp::GlobalParserBM->firstFreeSymbol(value);
  if (!free_symbol.IsNull())
  {
    const std::string message =
        std::string("the default of a constant array must be a value, and "
                    "this one depends on ") +
        free_symbol.GetName();
    stp::releaseParserValue($3);
    stp::releaseParserValue($4);
    stp::GlobalParserInterface->deleteNode($6);
    fatal_yyerror(message.c_str());
  }
  $$ = stp::GlobalParserInterface->newNode(
      stp::GlobalParserBM->CreateConstArray(array_sort, value));
  stp::releaseParserValue($3);
  stp::releaseParserValue($4);
  stp::GlobalParserInterface->deleteNode($6);
}
| id_select an_term an_term
{
  //ARRAY READ
  // valuewidth is same as array, indexwidth is 0.
  ASTNode array = *$2;
  ASTNode index = *$3;
  checkArrayIndexSort(array, index);
  unsigned int width = array.GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(READ, width, array, index));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  checkQualifiedResult($1, $$);
}
| id_store an_term an_term an_term
{
  //ARRAY WRITE
  unsigned int width = $4->GetValueWidth();
  ASTNode array = *$2;
  ASTNode index = *$3;
  ASTNode writeval = *$4;
  checkArrayIndexSort(array, index);
  checkArrayValueSort(array, writeval);
  ASTNode write_term = stp::GlobalParserInterface->nf->CreateArrayTerm(WRITE,$2->GetIndexWidth(),width,array,index,writeval);
  $$ = stp::GlobalParserInterface->newNode(write_term);
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
  checkQualifiedResult($1, $$);
}
| id_bvextract an_term
{
  checkBitVectorTerm(*$2);
  // Bounds outside the operand end the parse: going on, the extract was
  // built anyway and folded, reading past a constant's bits.
  int width = $1->first - $1->second + 1;
  if (width < 0)
    fatal_yyerror("Negative width in extract");

  if((unsigned)$1->first >= $2->GetValueWidth())
    fatal_yyerror("Parsing: Wrong width in BVEXTRACT");

  ASTNode hi  =  stp::GlobalParserInterface->CreateBVConst(32, $1->first);
  ASTNode low =  stp::GlobalParserInterface->CreateBVConst(32, $1->second);
  ASTNode output = stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT, width, *$2,hi,low);
  ASTNode * n = stp::GlobalParserInterface->newNode(output);
  $$ = n;
    stp::GlobalParserInterface->deleteNode( $2);
  checkQualifiedResult($1->qualifier, $$);
  stp::releaseParserValue($1);
}
| id_bvzx an_term
{
  checkBitVectorTerm(*$2);
  unsigned w = $2->GetValueWidth() + $1->first;
  ASTNode width = stp::GlobalParserInterface->CreateBVConst(32,w);
  $$ =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVZX,w,*$2,width));
  stp::GlobalParserInterface->deleteNode( $2);
  checkQualifiedResult($1->qualifier, $$);
  stp::releaseParserValue($1);
}
| id_bvsx an_term
{
  checkBitVectorTerm(*$2);
  unsigned w = $2->GetValueWidth() + $1->first;
  ASTNode width = stp::GlobalParserInterface->CreateBVConst(32,w);
  $$ =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVSX,w,*$2,width));
  stp::GlobalParserInterface->deleteNode( $2);
  checkQualifiedResult($1->qualifier, $$);
  stp::releaseParserValue($1);
}

| id_ite an_formula an_term an_term
{
  // Reject branches of different floating-point formats up front, as the
  // (= ...) rule does for its operands: with a constant condition the
  // factory folds the if-then-else to one branch before any type check can
  // see the pair, and two formats can share one packed width -- (8, 24)
  // and (24, 8) are both 32 bits -- so the width checks cannot tell them
  // apart. (BVTypeCheck's ITE case backs this up for a symbolic
  // condition.) Packed bits are an internal representation, not a public
  // coercion: a float branch and a BitVec branch are different sorts.
  if (!$3->GetSourceSort().isKnown() ||
      $3->GetSourceSort() != $4->GetSourceSort())
  {
    fatal_yyerror("ite branches must have the same sort");
  }

  // A Real ite has no bit-vector width to carry, so it is built through the
  // Real constructor; the frontend later names it and states what it stands
  // for on each branch.
  if ($3->GetSourceSort().kind() == stp::SourceSort::Kind::Real)
  {
    ASTVec* branches = new ASTVec{*$2, *$3, *$4};
    $$ = createExactRealTerm(ITE, branches);
    stp::GlobalParserInterface->deleteNode( $2);
    stp::GlobalParserInterface->deleteNode( $3);
    stp::GlobalParserInterface->deleteNode( $4);
    checkQualifiedResult($1, $$);
    break;
  }
  const unsigned int width = $3->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateArrayTerm(ITE,$4->GetIndexWidth(), width,*$2, *$3, *$4));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
  checkQualifiedResult($1, $$);
}
| id_bvconcat an_term an_term
{
  checkBitVectorTerm(*$2);
  checkBitVectorTerm(*$3);
  const unsigned int width = $2->GetValueWidth() + $3->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVCONCAT, width, *$2, *$3));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  checkQualifiedResult($1, $$);
}
| id_bvnot an_term
{
  checkBitVectorTerm(*$2);
  //this is the BVNEG (term) in the CVCL language
  unsigned int width = $2->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, *$2));
  stp::GlobalParserInterface->deleteNode( $2);
  checkQualifiedResult($1, $$);
}
| id_bvneg an_term
{
  checkBitVectorTerm(*$2);
  //this is the BVUMINUS term in CVCL langauge
  unsigned width = $2->GetValueWidth();
  $$ =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVUMINUS,width,*$2));
  stp::GlobalParserInterface->deleteNode( $2);
  checkQualifiedResult($1, $$);
}
| LPAREN_TOK id_bvand an_terms RPAREN_TOK
{
 $$ = createTerm(BVAND, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvor an_terms RPAREN_TOK
{
  $$ = createTerm(BVOR, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvxor an_terms RPAREN_TOK
{
  $$ = createTerm(BVXOR, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvxnor an_term an_term RPAREN_TOK
{
  ASTNode *temp = createTerm(BVXOR, $3, $4);
  const unsigned int width = temp->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, *temp));
  stp::GlobalParserInterface->deleteNode( temp);
  checkQualifiedResult($2, $$);
}
| id_bvcomp an_term an_term
{
  checkBitVectorTerm(*$2);
  checkBitVectorTerm(*$3);
  checkSameWidth(*$2, *$3);
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(ITE, 1,
  stp::GlobalParserInterface->nf->CreateNode(EQ, *$2, *$3),
  stp::GlobalParserInterface->CreateOneConst(1),
  stp::GlobalParserInterface->CreateZeroConst(1)));

  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  checkQualifiedResult($1, $$);
}
| id_bvsub an_term an_term
{
  $$ = createTerm(BVSUB, $2, $3);
  checkQualifiedResult($1, $$);
}
| LPAREN_TOK id_bvplus an_terms RPAREN_TOK
{
  $$ = createTerm(BVPLUS, $3);
  checkQualifiedResult($2, $$);
}
| LPAREN_TOK id_bvmult an_terms RPAREN_TOK
{
  $$ = createTerm(BVMULT, $3);
  checkQualifiedResult($2, $$);
}
| id_bvdiv an_term an_term
{
  $$ = createTerm(BVDIV, $2, $3);
  checkQualifiedResult($1, $$);
}
| id_bvmod an_term an_term
{
  $$ = createTerm(BVMOD, $2, $3);
  checkQualifiedResult($1, $$);
}
| id_sbvdiv an_term an_term
{
  $$ = createTerm(SBVDIV, $2, $3);
  checkQualifiedResult($1, $$);
}
| id_sbvrem an_term an_term
{
  $$ = createTerm(SBVREM, $2, $3);
  checkQualifiedResult($1, $$);
}
| id_sbvmod an_term an_term
{
  $$ = createTerm(SBVMOD, $2, $3);
  checkQualifiedResult($1, $$);
}
| id_bvnand an_term an_term
{
  checkBitVectorTerm(*$2);
  checkBitVectorTerm(*$3);
  checkSameWidth(*$2, *$3);
  unsigned int width = $2->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, stp::GlobalParserInterface->nf->CreateTerm(BVAND, width, *$2, *$3)));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  checkQualifiedResult($1, $$);
}
| id_bvnor an_term an_term
{
  checkBitVectorTerm(*$2);
  checkBitVectorTerm(*$3);
  checkSameWidth(*$2, *$3);
  unsigned int width = $2->GetValueWidth();
  $$= stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, stp::GlobalParserInterface->nf->CreateTerm(BVOR, width, *$2, *$3)));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  checkQualifiedResult($1, $$);
}
| id_bvleftshift_1 an_term an_term
{
   $$ = createTerm(BVLEFTSHIFT, $2, $3);
  checkQualifiedResult($1, $$);
}
| id_bvrightshift_1 an_term an_term
{
   $$ = createTerm(BVRIGHTSHIFT, $2, $3);
  checkQualifiedResult($1, $$);
}
| id_bvarithrightshift an_term an_term
{
   $$ = createTerm(BVSRSHIFT, $2, $3);
  checkQualifiedResult($1, $$);
}
| id_bvrotate_left an_term
{
  checkBitVectorTerm(*$2);
  ASTNode *n;
  unsigned width = $2->GetValueWidth();
  unsigned rotate = $1->first % width;
  if (0 == rotate)
  {
      n = $2;
      $2 = nullptr;
  }
  else
  {
    ASTNode high = stp::GlobalParserInterface->CreateBVConst(32,width-1);
    ASTNode zero = stp::GlobalParserInterface->CreateBVConst(32,0);
    ASTNode cut = stp::GlobalParserInterface->CreateBVConst(32,width-rotate);
    ASTNode cutMinusOne = stp::GlobalParserInterface->CreateBVConst(32,width-rotate-1);

    ASTNode top =  stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT,rotate,*$2,high, cut);
    ASTNode bottom =  stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT,width-rotate,*$2,cutMinusOne,zero);
    n =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVCONCAT,width,bottom,top));
    stp::GlobalParserInterface->deleteNode( $2);
  }
  $$ = n;
  checkQualifiedResult($1->qualifier, $$);
  stp::releaseParserValue($1);
}
| id_bvrotate_right an_term
{
  checkBitVectorTerm(*$2);
  ASTNode *n;
  unsigned width = $2->GetValueWidth();
  unsigned rotate = $1->first % width;
  if (0 == rotate)
  {
      n = $2;
      $2 = nullptr;
  }
  else
  {
    ASTNode high = stp::GlobalParserInterface->CreateBVConst(32,width-1);
    ASTNode zero = stp::GlobalParserInterface->CreateBVConst(32,0);
    ASTNode cut = stp::GlobalParserInterface->CreateBVConst(32,rotate);
    ASTNode cutMinusOne = stp::GlobalParserInterface->CreateBVConst(32,rotate-1);

    ASTNode bottom =  stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT,rotate,*$2,cutMinusOne, zero);
    ASTNode top =  stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT,width-rotate,*$2,high,cut);
    n =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVCONCAT,width,bottom,top));
    stp::GlobalParserInterface->deleteNode( $2);
  }
  $$ = n;
  checkQualifiedResult($1->qualifier, $$);
  stp::releaseParserValue($1);
}
| id_bvrepeat an_term
{
  checkBitVectorTerm(*$2);
  unsigned count = $1->first;
  if (count < 1)
      fatal_yyerror("One or more repeats please");

  unsigned w = $2->GetValueWidth();
  ASTNode n =  *$2;

  for (unsigned i =1; i < count; i++)
  {
        n = stp::GlobalParserInterface->nf->CreateTerm(BVCONCAT,w*(i+1),n,*$2);
  }
  $$ = stp::GlobalParserInterface->newNode(n);
  stp::GlobalParserInterface->deleteNode( $2);
  checkQualifiedResult($1->qualifier, $$);
  stp::releaseParserValue($1);
}
| id_bvconst_decimal
{
  // (_ bvN w): w is positive and N fits w bits, and saying so is the
  // parser's job (the engine's constructor treats either as fatal).
  if ($1->first == 0)
  {
    fatal_yyerror("bit-vectors must be of positive length");
  }
  if (!decimalFitsWidth($1->digits, $1->first))
  {
    const std::string diagnostic = "(_ bv" + $1->digits + " " + std::to_string($1->first) +
                                   "): the value does not fit in " +
                                   std::to_string($1->first) + " bits";
    fatal_yyerror(diagnostic.c_str());
  }
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst($1->digits, 10, $1->first));
  $$->SetValueWidth($1->first);
  checkQualifiedResult($1->qualifier, $$);
  stp::releaseParserValue($1);
}
| LPAREN_TOK id_bitvector_functionid an_mixed RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(applyFunctionChecked(*$2,*$3));

  if ($$->GetType() != BITVECTOR_TYPE)
      yyerror("Must be bitvector type");

  stp::releaseParserValue($3);
}
| LPAREN_TOK id_uf_bv_functionid an_mixed RPAREN_TOK
{
  $$ = applyParsedUF($2, *$3);
  stp::releaseParserValue($3);
}
| LPAREN_TOK id_uf_bv_functionid RPAREN_TOK
{
  $$ = applyParsedUF($2, ASTVec());
}
| LPAREN_TOK id_floatingpoint_functionid an_mixed RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(applyFunctionChecked(*$2,*$3));

  if ($$->GetType() != FLOATINGPOINT_TYPE)
      yyerror("Must be floating-point type");

  stp::releaseParserValue($3);
}
| id_floatingpoint_functionid
{
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(applyFunctionChecked(*$1,empty));

  if ($$->GetType() != FLOATINGPOINT_TYPE)
    yyerror("Must be floating-point type");
}
| id_bitvector_functionid
{
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(applyFunctionChecked(*$1,empty));

  if ($$->GetType() != BITVECTOR_TYPE)
    yyerror("Must be bitvector type");
}
| LPAREN_TOK id_roundingmode_functionid an_mixed RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(
      applyFunctionChecked(*$2, *$3));
  if ($$->GetSourceSort().kind() != stp::SourceSort::Kind::RoundingMode)
    yyerror("Must be RoundingMode type");
  stp::releaseParserValue($3);
}
| id_roundingmode_functionid
{
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(
      applyFunctionChecked(*$1, empty));
  if ($$->GetSourceSort().kind() != stp::SourceSort::Kind::RoundingMode)
    yyerror("Must be RoundingMode type");
}
| LPAREN_TOK id_declaredsort_functionid an_mixed RPAREN_TOK
{
  // A define-fun whose result sort is one declared by declare-sort. Its own
  // token for the same reason RoundingMode has one: the lexer dispatches a
  // function name by its result sort, and before this sort had a kind of its
  // own such a function reached the bit-vector token and was accepted as a
  // bit-vector term.
  $$ = stp::GlobalParserInterface->newNode(
      applyFunctionChecked(*$2, *$3));
  if ($$->GetSourceSort().kind() != stp::SourceSort::Kind::Uninterpreted)
    yyerror("Must be a declared sort");
  stp::releaseParserValue($3);
}
| id_declaredsort_functionid
{
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(
      applyFunctionChecked(*$1, empty));
  if ($$->GetSourceSort().kind() != stp::SourceSort::Kind::Uninterpreted)
    yyerror("Must be a declared sort");
}
| annotation_open an_term annotation_attributes attributes RPAREN_TOK
{
  annotateTerm($1, *$2, *$4);
  stp::releaseParserValue($4);
  $$ = $2;
}
| LPAREN_TOK LET_TOK lets an_term RPAREN_TOK
  {
    $$ = $4;
    stp::GlobalParserInterface->letMgr->pop();
  }
;

%%

// The pinned response to `(declare-fun name ...)` over an already-known
// name in every shape but the nonzero-arity one: exactly the syntax error
// bison raised when the lexer classified the name into a typed token that
// no var_decl alternative accepts -- same message, same token-kind name
// (from the parser's own symbol table, so it tracks the grammar), same
// token text as recorded by the lexer at the name -- through the same
// rejection path an ordinary syntax error takes. The caller abandons the
// parse. Defined after the grammar because yytname and YYTRANSLATE live in
// the generated parser body.
void reportRedeclaredName()
{
  std::ostringstream o;
  o << "syntax error: line " << stp::SMT2DeclassifiedNameLine()
    << " syntax error, unexpected "
    << yytname[YYTRANSLATE(stp::SMT2DeclassifiedNameToken())]
    << ", expecting STRING_TOK  token: " << stp::SMT2DeclassifiedNameText();
  stp::SMT2ConsumeDeclassifiedName();
  stp::GlobalParserInterface->rejectCurrentCommand(o.str());
}

namespace stp {
  int SMT2Parse() {
    GlobalParserInterface->beginOutputRouting();
    struct RestoreOutput
    {
      Cpp_interface* interface;
      ~RestoreOutput() { interface->endOutputRouting(); }
    } restoreOutput{GlobalParserInterface};
    // Each SMT2Parse is one script: the floating-point keywords start
    // disabled and turn on at an FP set-logic.
    SMT2SetFloatTokens(GlobalParserInterface->all_theory_tokens);
    SMT2SetRealTokens(GlobalParserInterface->all_theory_tokens);
    SMT2SetBitVectorTokens(GlobalParserInterface->all_theory_tokens);
    SMT2ResetCommandLexerState();
    SMT2ResetLexMode();
    int result;
    bool ended = false;
    try
    {
      result = smt2parse();
    }
    catch (const stp::ParseAbandon&)
    {
      result = 1;
    }
    catch (const stp::EngineFatal& e)
    {
      GlobalParserInterface->rejectCurrentCommand(e.what());
      // An engine failure in the engine's own work -- a check the script
      // ran, a model it read -- is the engine's. Any other came out of
      // building the script's terms: the type checker refusing operands of
      // two widths, a let binding one name twice. That is the script's
      // refusal of itself, a failed parse like any other.
      if (GlobalParserInterface->engine_work_failed)
        throw;
      result = 1;
    }
    catch (const stp::ScriptEnded&)
    {
      // The run ended at a check's first CNF: the script did what it was
      // asked, and the check-sat that ended it is not finished.
      result = 0;
      ended = true;
    }
    if (result != 0 || ended)
      GlobalParserInterface->abortCurrentCommand();
    SMT2ResetCommandLexerState();
    return result;
  }
}
