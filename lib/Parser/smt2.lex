/*%option reentrant
%option bison-bridge*/
%option noyywrap
%option noreject
%option nounput
%option noyymore

/* %option debug */

%{
/********************************************************************
* AUTHORS: Trevor Hansen, Vijay Ganesh, David L. Dill
*
* BEGIN DATE: July, 2006
*
* This file is modified version of the CVCL's smtlib.lex file. Please
* see CVCL license below
********************************************************************/

/********************************************************************
* Author: Sergey Berezin, Clark Barrett
*
* Created: Apr 30 2005
*
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
********************************************************************/
#include "stp/Parser/parser.h"
#include "stp/cpp_interface.h"
#include "stp/Parser/SMT2Attribute.h"
#include "parsesmt2.tab.h"

#include <cerrno>
#include <cstdlib>
#include <limits>

  extern char *smt2text;
  extern int smt2leng;
  extern int smt2error (const char *msg);
  bool stringOnly = false;

  // Line counting for syntax-error messages, maintained by hand (in the
  // flex-provided smt2lineno) in the few rules whose matches can contain a
  // newline. '%option yylineno' made flex check a can-this-rule-match-eol
  // table on every token instead, which cost a load and a branch per match
  // across the whole input.
  static void countNewlines(const char* s, size_t len)
  {
    const char* p = s;
    const char* const end = s + len;
    while ((p = (const char*)memchr(p, '\n', end - p)) != NULL)
    {
      smt2lineno++;
      p++;
    }
  }

  // Whether the floating-point keywords are live. Off until the parser sees
  // an FP set-logic: SMT-LIB reserves theory names per-logic, and QF_BV
  // inputs legitimately declare symbols named "fp", "NaN", "RNE" and so on
  // (they parsed before floating-point support existed, and must keep
  // parsing). See fpKeyword() below and stp::SMT2SetFloatTokens.
  static thread_local bool floatTokensActive = false;
  static thread_local bool realTokensActive = false;
  static thread_local bool bitVectorTokensActive = false;
  static thread_local bool commandNamePending = false;
  static thread_local bool qualifiedNamePending = false;
  static thread_local bool declarationSortsAfterName = false;

  // Inside an indexed identifier -- between "(_" and its ")" -- a numeral
  // is an index, a width or a count, never a Real literal, whatever the
  // Real gate says. Set by the "_" rule, cleared by the next ")".
  static thread_local bool indexedIdentifierOpen = false;

  // The most recent floating-point name that the gate above handed back as an
  // ordinary identifier without finding a declaration for it. A missing
  // set-logic surfaces far from its cause -- the grammar just trips over an
  // undeclared symbol, and says so in those terms -- so the diagnostic asks
  // for this to name the token and what would have made it a keyword. Only
  // *unresolved* names are recorded: a QF_BV file that really did declare
  // "fp" is using its own symbol and must not be told about FP logics.
  static thread_local std::string unresolvedFpKeyword;

  // With the UF feature enabled, the next identifier sits in declare-fun's
  // name position. A name that is already classified in some namespace is
  // handed back UNclassified there -- as a plain STRING_TOK -- so that the
  // grammar can see the declaration's shape and route a NONZERO-ARITY
  // collision into the nonfatal UF declaration funnel. Every other shape
  // owes the pinned legacy response, so what the classification would have
  // been is recorded (below) for the grammar to replicate it from. Only the
  // declare-fun name is treated this way: declare-const and define-fun are
  // UF-free shapes and keep the legacy classified-token syntax error at
  // the name, feature on or off. Feature-off lexing remains byte-for-byte
  // on the legacy path.
  static thread_local bool ufDeclarationNamePending = false;

  // The declassification record (see SMT2DeclassifiedNamePending in
  // parser.h): the token kind the name would have carried, where, and the
  // token text exactly as yyerror would have printed it. For |quoted| names
  // lookup() chops the closing bar in place, so smt2text is "|name" --
  // that is what the legacy error printed, and what is recorded.
  static thread_local bool declassifiedNamePending = false;
  static thread_local int declassifiedNameToken = 0;
  static thread_local int declassifiedNameLine = 0;
  static thread_local std::string declassifiedNameText;

  // Set by the grammar immediately after the '(' that opens one define-fun
  // formal. The following identifier is a declaration site, not a reference
  // to a top-level function, UF, or symbol.
  static thread_local bool functionParameterNamePending = false;

#ifdef _MSC_VER
  #include <io.h>
  // defining isatty to avoid dll symbol export inconsistencies
  #define isatty(x) _isatty(x)
#endif

  // File-static (local to this file) variables and functions
  static THREAD_LOCAL_IE std::string _string_lit;

  // Nesting depth while skipping the arguments of a command we don't
  // interpret. Zero means the next ')' closes the command itself.
  static THREAD_LOCAL_IE int skippedDepth = 0;

  // A get-value term as the script spelled it. The response echoes each term
  // (SMT-LIB 2.6, 4.2.6), and no node can stand in for it: the node factory
  // rewrites and folds while the grammar builds, and NOT(NOT x) cannot exist
  // as a node at all. So the term list is scanned twice. The GET_VALUE_TERM
  // condition copies one term's text here with its whitespace normalised and
  // comments dropped, hands it to the grammar as GET_VALUE_TERM_TOK, then
  // pushes the same text back as input so the ordinary rules build the node.
  static THREAD_LOCAL_IE std::string capturedTerm;
  // Parentheses open inside the term being captured. Zero means the next
  // ')' closes the get-value list itself.
  static thread_local int capturedDepth = 0;
  // Input buffers holding a captured term, pushed over the script's own.
  static thread_local unsigned rescanDepth = 0;

  static void captureText(const char* s, size_t len)
  {
    if (!capturedTerm.empty() && capturedTerm.back() != '(' && s[0] != ')')
      capturedTerm += ' ';
    capturedTerm.append(s, len);
  }

  static void dropCapturedTerms()
  {
    capturedTerm.clear();
    capturedDepth = 0;
  }

  static thread_local bool sortContext = false;
  static thread_local unsigned attributeDepth = 0;
  // Carried by each '(' token so parser lookahead cannot change an
  // annotation's syntactic position before its reduction.
  static thread_local unsigned parenthesisDepth = 0;
  struct AnnotationScope { size_t letDepth; bool closed; };
  static thread_local std::vector<AnnotationScope> annotations;

namespace stp
{
  void SMT2SetSortContext(bool enable) { sortContext = enable; }

  void SMT2SetFloatTokens(bool enable)
  {
    floatTokensActive = enable;
    // Either direction starts a fresh script's worth of history -- set-logic
    // opens one, reset closes one -- and these are thread-locals that outlive
    // a single parse. A name left behind by an earlier script must not attach
    // its hint to this one's first error.
    unresolvedFpKeyword.clear();
  }

  void SMT2SetBitVectorTokens(bool enable) { bitVectorTokensActive = enable; }
  void SMT2ExpectCommand() { commandNamePending = true; }

  void SMT2SetRealTokens(bool enable)
  {
    realTokensActive = enable;
  }

  void SMT2ExpectFunctionParameterName()
  {
    assert(!functionParameterNamePending);
    functionParameterNamePending = true;
  }

  void SMT2ResetCommandLexerState()
  {
    // A parse abandoned inside a get-value term leaves its re-scan buffers
    // pushed; the next input would be read from them.
    while (rescanDepth > 0)
    {
      yypop_buffer_state();
      --rescanDepth;
    }
    dropCapturedTerms();
    indexedIdentifierOpen = false;
    commandNamePending = false;
    qualifiedNamePending = false;
    declarationSortsAfterName = false;
    sortContext = false;
    annotations.clear();
    ufDeclarationNamePending = false;
    functionParameterNamePending = false;
    declassifiedNamePending = false;
    // The let rule sets it for its binder and clears it once the binder is
    // read; a parse abandoned in between left every identifier of the next
    // parse lexed as an unknown name.
    stringOnly = false;
  }

  bool SMT2DeclassifiedNamePending() { return declassifiedNamePending; }
  int SMT2DeclassifiedNameToken() { return declassifiedNameToken; }
  int SMT2DeclassifiedNameLine() { return declassifiedNameLine; }
  const std::string& SMT2DeclassifiedNameText()
  {
    return declassifiedNameText;
  }
  void SMT2ConsumeDeclassifiedName() { declassifiedNamePending = false; }

  // Whether the token a diagnostic is about is a floating-point name that the
  // gate demoted for want of an FP set-logic. Matched against the offending
  // text rather than answered from the flag alone, so that an unrelated error
  // later in the file cannot inherit an earlier name's hint.
  bool SMT2FpKeywordNeedsLogic(const char* text)
  {
    return !floatTokensActive && text != NULL && !unresolvedFpKeyword.empty() &&
           unresolvedFpKeyword == text;
  }
}

  static int theoryToken(std::string_view name, bool includeInactiveFP = false)
  {
    {
      static const ankerl::unordered_dense::map<std::string_view, int> names = {
          {"Array", ARRAY_TOK},
          {"Bool", BOOL_TOK},
          {"true", TRUE_TOK},
          {"false", FALSE_TOK},
          {"not", NOT_TOK},
          {"and", AND_TOK},
          {"or", OR_TOK},
          {"xor", XOR_TOK},
          {"ite", ITE_TOK},
          {"=", EQ_TOK},
          {"=>", IMPLIES_TOK},
          {"distinct", DISTINCT_TOK},
          {"select", SELECT_TOK},
          {"store", STORE_TOK}};
      const auto found = names.find(name);
      if (found != names.end()) return found->second;
    }
    if (bitVectorTokensActive)
    {
      static const ankerl::unordered_dense::map<std::string_view, int> names = {
          {"BitVec", BITVEC_TOK},
          {"bvshl", BVLEFTSHIFT_1_TOK},
          {"bvlshr", BVRIGHTSHIFT_1_TOK},
          {"bvashr", BVARITHRIGHTSHIFT_TOK},
          {"bvadd", BVPLUS_TOK},
          {"bvsub", BVSUB_TOK},
          {"bvnot", BVNOT_TOK},
          {"bvmul", BVMULT_TOK},
          {"bvudiv", BVDIV_TOK},
          {"bvsdiv", SBVDIV_TOK},
          {"bvurem", BVMOD_TOK},
          {"bvsrem", SBVREM_TOK},
          {"bvsmod", SBVMOD_TOK},
          {"bvneg", BVNEG_TOK},
          {"bvand", BVAND_TOK},
          {"bvor", BVOR_TOK},
          {"bvxor", BVXOR_TOK},
          {"bvnand", BVNAND_TOK},
          {"bvnor", BVNOR_TOK},
          {"bvxnor", BVXNOR_TOK},
          {"concat", BVCONCAT_TOK},
          {"extract", BVEXTRACT_TOK},
          {"bvult", BVLT_TOK},
          {"bvugt", BVGT_TOK},
          {"bvule", BVLE_TOK},
          {"bvuge", BVGE_TOK},
          {"bvslt", BVSLT_TOK},
          {"bvsgt", BVSGT_TOK},
          {"bvsle", BVSLE_TOK},
          {"bvsge", BVSGE_TOK},
          {"bvcomp", BVCOMP_TOK},
          {"zero_extend", BVZX_TOK},
          {"sign_extend", BVSX_TOK},
          {"repeat", BVREPEAT_TOK},
          {"rotate_left", BVROTATE_LEFT_TOK},
          {"rotate_right", BVROTATE_RIGHT_TOK},
          {"bvnego", BVNEGO_TOK},
          {"bvuaddo", BVUADDO_TOK},
          {"bvsaddo", BVSADDO_TOK},
          {"bvumulo", BVUMULO_TOK},
          {"bvsmulo", BVSMULO_TOK},
          {"bvusubo", BVUSUBO_TOK},
          {"bvssubo", BVSSUBO_TOK},
          {"bvsdivo", BVSDIVO_TOK}};
      const auto found = names.find(name);
      if (found != names.end()) return found->second;
    }
    if (floatTokensActive || includeInactiveFP)
    {
      static const ankerl::unordered_dense::map<std::string_view, int> names = {
          {"FloatingPoint", FLOATINGPOINT_TOK},
          {"RoundingMode", ROUNDINGMODE_TOK},
          {"Float16", FLOAT16_TOK},
          {"Float32", FLOAT32_TOK},
          {"Float64", FLOAT64_TOK},
          {"Float128", FLOAT128_TOK},
          {"fp", FP_TOK},
          {"to_fp", FP_TOFP_TOK},
          {"to_fp_unsigned", FP_TOFP_UNSIGNED_TOK},
          {"fp.to_ubv", FP_TO_UBV_TOK},
          {"fp.to_sbv", FP_TO_SBV_TOK},
          {"fp.to_real", FP_TO_REAL_TOK},
          {"fp.to_ieee_bv", FP_TO_IEEE_BV_TOK},
          {"fp.abs", FP_ABS_TOK},
          {"fp.neg", FP_NEG_TOK},
          {"fp.add", FP_ADD_TOK},
          {"fp.sub", FP_SUB_TOK},
          {"fp.mul", FP_MUL_TOK},
          {"fp.div", FP_DIV_TOK},
          {"fp.fma", FP_FMA_TOK},
          {"fp.sqrt", FP_SQRT_TOK},
          {"fp.rem", FP_REM_TOK},
          {"fp.roundToIntegral", FP_ROUNDTOINTEGRAL_TOK},
          {"fp.min", FP_MIN_TOK},
          {"fp.max", FP_MAX_TOK},
          {"fp.leq", FP_LEQ_TOK},
          {"fp.lt", FP_LT_TOK},
          {"fp.geq", FP_GEQ_TOK},
          {"fp.gt", FP_GT_TOK},
          {"fp.eq", FP_EQ_TOK},
          {"fp.isNormal", FP_ISNORMAL_TOK},
          {"fp.isSubnormal", FP_ISSUBNORMAL_TOK},
          {"fp.isZero", FP_ISZERO_TOK},
          {"fp.isInfinite", FP_ISINFINITE_TOK},
          {"fp.isNaN", FP_ISNAN_TOK},
          {"fp.isNegative", FP_ISNEGATIVE_TOK},
          {"fp.isPositive", FP_ISPOSITIVE_TOK},
          {"roundTowardZero", FP_RM_ROUNDTOWARDZERO_TOK},
          {"roundNearestTiesToEven", FP_RM_ROUNDNEARESTTIESTOEVEN_TOK},
          {"roundNearestTiesToAway", FP_RM_ROUNDNEARESTTIESTOAWAY_TOK},
          {"roundTowardPositive", FP_RM_ROUNDTOWARDPOSITIVE_TOK},
          {"roundTowardNegative", FP_RM_ROUNDTOWARDNEGATIVE_TOK},
          {"RTZ", FP_RM_ROUNDTOWARDZERO_TOK},
          {"RNE", FP_RM_ROUNDNEARESTTIESTOEVEN_TOK},
          {"RNA", FP_RM_ROUNDNEARESTTIESTOAWAY_TOK},
          {"RTP", FP_RM_ROUNDTOWARDPOSITIVE_TOK},
          {"RTN", FP_RM_ROUNDTOWARDNEGATIVE_TOK},
          {"NaN", FP_NAN_TOK},
          {"-oo", FP_NEG_INF_TOK},
          {"+oo", FP_POS_INF_TOK},
          {"-zero", FP_NEG_ZERO_TOK},
          {"+zero", FP_POS_ZERO_TOK}};
      const auto found = names.find(name);
      if (found != names.end()) return found->second;
    }
    if (realTokensActive)
    {
      static const ankerl::unordered_dense::map<std::string_view, int> names = {
          {"Real", REAL_TOK},
          {"+", REAL_ADD_TOK},
          {"-", REAL_SUB_TOK},
          {"*", REAL_MUL_TOK},
          {"/", REAL_DIV_TOK},
          {"<", REAL_LT_TOK},
          {"<=", REAL_LE_TOK},
          {">", REAL_GT_TOK},
          {">=", REAL_GE_TOK}};
      const auto found = names.find(name);
      if (found != names.end()) return found->second;
    }
    return 0;
  }

  static bool isSortToken(int token)
  {
    switch (token)
    {
      case BOOL_TOK: case BITVEC_TOK: case ARRAY_TOK: case REAL_TOK:
      case FLOATINGPOINT_TOK: case ROUNDINGMODE_TOK:
      case FLOAT16_TOK: case FLOAT32_TOK: case FLOAT64_TOK: case FLOAT128_TOK:
        return true;
      default: return false;
    }
  }

  static int termTheoryToken(std::string_view name)
  {
    const int token = theoryToken(name);
    return isSortToken(token) ? 0 : token;
  }

  static int classify(char* s);

  static int lookup(char* s)
  {
    // declare-fun's domain and codomain belong to the sort namespace. Its
    // name is classified first, then the entire signature uses that namespace.
    struct SignatureScope
    {
      bool begin;
      ~SignatureScope() { if (begin) sortContext = true; }
    } signature{declarationSortsAfterName};
    declarationSortsAfterName = false;
    const bool qualifiedName = qualifiedNamePending;
    qualifiedNamePending = false;
    // The SMTLIB2 specifications sez that the outter bars aren't part of the
    // name. This means that we can create an empty string symbol name.
    // Strip them in place: s is always yytext (writable, and dead once the
    // action returns), so overwriting the closing bar saves a malloc+copy
    // per occurrence.
    if (s[0] == '|') {
      const size_t len = smt2leng;
      assert(len >= 2);
      if (s[len-1] == '|')
      {
        s[len-1] = '\0'; // chop off first and last characters.
        s++;
      }
    }

    if (qualifiedName && s[0] == '@')
    {
      smt2lval.str = new std::string(s);
      return ABSTRACT_VALUE_TOK;
    }

    if (stringOnly)
    {
      smt2lval.str = new std::string(s);
      return STRING_TOK;
    }

    if (sortContext)
    {
      if (!stp::GlobalParserInterface->isSortParameter(s))
      {
        const int token = theoryToken(s);
        if (isSortToken(token)) return token;
      }
      if (!floatTokensActive && theoryToken(s) == 0 && theoryToken(s, true) != 0)
        unresolvedFpKeyword = s;
      smt2lval.str = new std::string(s);
      return STRING_TOK;
    }

    if (ufDeclarationNamePending)
    {
      // Declare-fun's name position, feature on. Classify exactly as the
      // legacy lexer would, then hand a classified name back unclassified
      // and record what it would have been (see the statics above).
      ufDeclarationNamePending = false;
      if (s[0] == '@')
      {
        smt2lval.str = new std::string(s);
        return STRING_TOK;
      }
      if (const int builtin = termTheoryToken(s))
        return builtin;
      const int token = classify(s);
      if (token == STRING_TOK)
        return token;
      if (token == FORMID_TOK || token == TERMID_TOK)
      {
        // classify() handed the grammar a fresh node it will never see.
        stp::GlobalParserInterface->deleteNode(smt2lval.node);
        smt2lval.node = NULL;
      }
      declassifiedNamePending = true;
      declassifiedNameToken = token;
      declassifiedNameLine = smt2lineno;
      declassifiedNameText = smt2text;
      smt2lval.str = new std::string(s);
      return STRING_TOK;
    }

    return classify(s);
  }

  // The legacy classification of an identifier: a let binder, a define-fun
  // formal, a define-fun, an uninterpreted function, a declared symbol, or
  // -- unseen before -- a plain string carrying its spelling.
  static int classify(char* s)
  {
    stp::ASTNode nptr;
    bool found = false;

    if (functionParameterNamePending)
    {
      functionParameterNamePending = false;
      // Preserve the existing rejection of duplicate formals: an earlier
      // formal with this spelling is already a binder, not a global name to
      // be shadowed. Every other spelling is returned unresolved here.
      if (!stp::GlobalParserInterface->LookupTemporarySymbol(s, nptr))
      {
        smt2lval.str = new std::string(s);
        return STRING_TOK;
      }
      found = true;
    }

    if (!found)
    {
      if (const stp::ASTNode* let =
              stp::GlobalParserInterface->letMgr->lookupLet(s))
      {
        nptr = *let;
        found = true;
        for (auto& annotation : annotations)
          if (stp::GlobalParserInterface->letMgr->boundOutside(s, annotation.letDepth))
            annotation.closed = false;
      }
      // Function formals are lexical binders and therefore resolve before
      // all top-level namespaces. Lets remain first because a nested let may
      // shadow a formal in the define-fun body.
      else if (stp::GlobalParserInterface->LookupTemporarySymbol(s, nptr))
      {
        found = true;
        for (auto& annotation : annotations)
          annotation.closed = false;
      }
    }
    if (!found)
    {
      if (indexedIdentifierOpen && bitVectorTokensActive && s[0] == 'b' && s[1] == 'v' &&
          s[2] != '\0' && strspn(s + 2, "0123456789") == strlen(s + 2))
      {
        smt2lval.str = new std::string(s + 2);
        return BVCONST_DECIMAL_TOK;
      }
      if (const int builtin = termTheoryToken(s))
        return builtin;
    }
    if (!found)
    {
      // Checking functions before ordinary top-level symbols saves a symbol
      // table probe in files built almost entirely from define-funs. Legal
      // top-level input cannot occupy both namespaces.
      if (stp::GlobalParserInterface->hasFunctions())
      {
        const stp::Cpp_interface::Function* fn =
            stp::GlobalParserInterface->lookupFunction(s);
        if (fn != NULL)
        {
          if (unresolvedFpKeyword == s) unresolvedFpKeyword.clear();
          smt2lval.fn = fn;
          switch (fn->function.GetSourceSort().kind())
          {
            case stp::SourceSort::Kind::RoundingMode:
              return ROUNDINGMODE_FUNCTIONID_TOK;
            case stp::SourceSort::Kind::BitVector:
              return BITVECTOR_FUNCTIONID_TOK;
            case stp::SourceSort::Kind::Bool:
              return BOOLEAN_FUNCTIONID_TOK;
            case stp::SourceSort::Kind::FloatingPoint:
              return FLOATINGPOINT_FUNCTIONID_TOK;
            case stp::SourceSort::Kind::Array:
              return ARRAY_FUNCTIONID_TOK;
            case stp::SourceSort::Kind::Real:
              return REAL_FUNCTIONID_TOK;
            case stp::SourceSort::Kind::Uninterpreted:
              return DECLAREDSORT_FUNCTIONID_TOK;
            case stp::SourceSort::Kind::Unknown:
              smt2error("Function with underivable return sort.");
          }
        }
      }

      if (stp::GlobalParserInterface->getUserFlags()
              .enable_uninterpreted_functions &&
          stp::GlobalParserInterface->hasUninterpretedFunctions())
      {
        const stp::UFDecl* declaration =
            stp::GlobalParserInterface->lookupUninterpretedFunction(s);
        if (declaration != NULL)
        {
          if (unresolvedFpKeyword == s) unresolvedFpKeyword.clear();
          smt2lval.ufdecl = declaration;
          return declaration->signature().codomain().kind() ==
                         stp::SourceSort::Kind::Bool
                     ? UF_BOOL_FUNCTIONID_TOK
                     : UF_BV_FUNCTIONID_TOK;
        }
      }

      if (stp::GlobalParserInterface->LookupSymbol(s,nptr))
        found = true;
    }

    if (found)
    {
      if (unresolvedFpKeyword == s) unresolvedFpKeyword.clear();
      // Check valuesize to see if it's a prop var.  I don't like doing
      // type determination in the lexer, but it's easier than rewriting
      // the whole grammar to eliminate the term/formula distinction.
      smt2lval.node = stp::GlobalParserInterface->newNode(nptr);
      if ((smt2lval.node)->GetType() == stp::BOOLEAN_TYPE)
        return FORMID_TOK;
      else
        return TERMID_TOK;
    }
    else
    {
      // it has not been seen before.
      if (!floatTokensActive && theoryToken(s) == 0 && theoryToken(s, true) != 0)
        unresolvedFpKeyword = s;
      smt2lval.str = new std::string(s);
      return STRING_TOK;
    }
  }

  static int commandToken(int token)
  {
    if (!commandNamePending)
      return lookup(smt2text);
    commandNamePending = false;
    stp::GlobalParserInterface->requireCommand(smt2text);
    return token;
  }

  // Defined after the rules: it needs INITIAL.
  static int capturedTermToken();

  // Where the input comes from when it is not the FILE* (setSMT2Reader in
  // parser.h): the 3.x API reads a caller's stream through one. Without a
  // reader the lexer reads its FILE* as flex always has -- flex's own
  // YY_INPUT, spelled out because defining the macro replaces it.
  static stp::ParserReader smt2Reader = NULL;
  static void* smt2ReaderOpaque = NULL;
#define YY_INPUT(buf, result, max_size)                                        \
  if (smt2Reader != NULL)                                                      \
    result = static_cast<int>(                                                 \
        smt2Reader((buf), static_cast<size_t>(max_size), smt2ReaderOpaque));   \
  else if (YY_CURRENT_BUFFER_LVALUE->yy_is_interactive)                        \
  {                                                                            \
    int c = '*';                                                               \
    int n;                                                                     \
    for (n = 0; n < max_size && (c = getc(yyin)) != EOF && c != '\n'; ++n)     \
      buf[n] = (char)c;                                                        \
    if (c == '\n')                                                             \
      buf[n++] = (char)c;                                                      \
    if (c == EOF && ferror(yyin))                                              \
      YY_FATAL_ERROR("input in flex scanner failed");                          \
    result = n;                                                                \
  }                                                                            \
  else                                                                         \
  {                                                                            \
    errno = 0;                                                                 \
    while ((result = (int)fread(buf, 1, (yy_size_t)max_size, yyin)) == 0 &&    \
           ferror(yyin))                                                       \
    {                                                                          \
      if (errno != EINTR)                                                      \
      {                                                                        \
        YY_FATAL_ERROR("input in flex scanner failed");                        \
        break;                                                                 \
      }                                                                        \
      errno = 0;                                                               \
      clearerr(yyin);                                                          \
    }                                                                          \
  }
%}

%x  COMMENT
%x  STRING_LITERAL
%x  ATTRIBUTE
%x  SKIP_SEXPR
%x  GET_VALUE_LIST
%x  GET_VALUE_TERM

LETTER  ([a-zA-Z])
DIGIT  ([0-9])
OPCHAR  ([~!@$%^&*\_\-+=<>\.?/])

ANYTHING  ({LETTER}|{DIGIT}|{OPCHAR})

%%
<ATTRIBUTE>[ \n\t\r]+ { countNewlines(yytext, yyleng); }
<ATTRIBUTE>";"[^\n]* { }
<ATTRIBUTE>":"({LETTER}|{OPCHAR}){ANYTHING}* {
  smt2lval.str = new std::string(smt2text + 1); return ATTRIBUTE_KEYWORD_TOK;
}
<ATTRIBUTE>"(" { ++attributeDepth; smt2lval.uintval = ++parenthesisDepth; return LPAREN_TOK; }
<ATTRIBUTE>")" {
  --parenthesisDepth;
  if (attributeDepth == 0) BEGIN INITIAL;
  else --attributeDepth;
  return RPAREN_TOK;
}
<ATTRIBUTE>"\""([^"]|"\"\"")*"\"" {
  countNewlines(yytext, yyleng);
  std::string decoded;
  for (int i = 1; i < yyleng - 1; ++i) {
    decoded += yytext[i];
    if (yytext[i] == '"') ++i;
  }
  smt2lval.attribute_value = new stp::SMT2AttributeValue{
      stp::SMT2AttributeValue::Kind::String, decoded};
  return ATTRIBUTE_VALUE_TOK;
}
<ATTRIBUTE>"|"[^|\\]*"|" {
  countNewlines(yytext, yyleng);
  smt2lval.attribute_value = new stp::SMT2AttributeValue{
      stp::SMT2AttributeValue::Kind::Symbol, std::string(yytext + 1, yyleng - 2)};
  return ATTRIBUTE_VALUE_TOK;
}
<ATTRIBUTE>(0|[1-9]{DIGIT}*) {
  smt2lval.attribute_value = new stp::SMT2AttributeValue{
      stp::SMT2AttributeValue::Kind::Numeral, yytext};
  return ATTRIBUTE_VALUE_TOK;
}
<ATTRIBUTE>((0|[1-9]{DIGIT}*)"."{DIGIT}+|#b[01]+|#x[0-9a-fA-F]+) {
  smt2lval.attribute_value = new stp::SMT2AttributeValue{
      stp::SMT2AttributeValue::Kind::Constant, yytext};
  return ATTRIBUTE_VALUE_TOK;
}
<ATTRIBUTE>({LETTER}|{OPCHAR}){ANYTHING}* {
  using Kind = stp::SMT2AttributeValue::Kind;
  const std::string name(yytext);
  const bool reserved = name == "!" || name == "_" || name == "as" ||
      name == "let" || name == "exists" || name == "forall" || name == "match" ||
      name == "par" || name == "lambda" || name == "BINARY" ||
      name == "DECIMAL" || name == "HEXADECIMAL" || name == "NUMERAL" ||
      name == "STRING";
  smt2lval.attribute_value = new stp::SMT2AttributeValue{
      reserved ? Kind::Reserved : Kind::Symbol, name};
  return ATTRIBUTE_VALUE_TOK;
}
<ATTRIBUTE>. { smt2error("invalid attribute character"); return 0; }
<ATTRIBUTE><<EOF>> { BEGIN INITIAL; return 0; }

[ \n\t\r\f] { if (*smt2text == '\n') smt2lineno++; /* skip whitespace */ }

 /* Numerals are arbitrary precision in the specification, but every numeral
    STP reads as a number is an index, a width or a count, all of which fit an
    unsigned. One that does not is kept as its digits and returned as a
    different token: a real literal converts from the digits and so stays
    exact, while every other use of a numeral is a syntax error rather than
    the silently wrapped value strtoul would hand back. */
(0|[1-9]{DIGIT}*)      {
                         if (realTokensActive && !indexedIdentifierOpen)
                         {
                           smt2lval.str = new std::string(smt2text);
                           return REAL_NUMERAL_TOK;
                         }
                         errno = 0;
                         const unsigned long value = strtoul(smt2text, NULL, 10);
                         if (errno == ERANGE ||
                             value > std::numeric_limits<unsigned>::max())
                         {
                           smt2lval.str = new std::string(smt2text);
                           return BIG_NUMERAL_TOK;
                         }
                         smt2lval.uintval = static_cast<unsigned>(value);
                         return NUMERAL_TOK;
                       }
bv{DIGIT}+             { return lookup(smt2text); }
#b[01]+             { smt2lval.str = new std::string(smt2text+2); return BVCONST_BINARY_TOK; }
#x({DIGIT}|[a-fA-F])+  { smt2lval.str = new std::string(smt2text+2); return BVCONST_HEXIDECIMAL_TOK; }
(0|[1-9]{DIGIT}*)"."{DIGIT}+    { smt2lval.str = new std::string(smt2text);
                         return realTokensActive ? REAL_DECIMAL_TOK
                                                 : DECIMAL_TOK;}

";" { BEGIN COMMENT; }
<COMMENT>"\n" { smt2lineno++; BEGIN INITIAL; /* return to normal mode */}
<COMMENT>.    { /* stay in comment mode */ }

<INITIAL>"\""   { BEGIN STRING_LITERAL;
          _string_lit.clear(); }
<STRING_LITERAL>"\"\""  {
            /* double quote is the only escape. */
          _string_lit.insert(_string_lit.end(),'"'); }
<STRING_LITERAL>"\""  { BEGIN INITIAL;
          smt2lval.str = new std::string(_string_lit);
          return STRING_LITERAL_TOK; }
<STRING_LITERAL>.     { _string_lit.insert(_string_lit.end(),*smt2text); }
<STRING_LITERAL>"\n"  { smt2lineno++;
                        _string_lit.insert(_string_lit.end(),*smt2text); }

<STRING_LITERAL><<EOF>> { BEGIN INITIAL; smt2error("unterminated string literal");
                           throw stp::ParseAbandon(); }

 /* Valid character are: ~ ! @ # $ % ^ & * _ - + = | \ : ; " < > . ? / ( )     */
"("             { qualifiedNamePending = false; smt2lval.uintval = ++parenthesisDepth; return LPAREN_TOK; }
")"             { indexedIdentifierOpen = false; --parenthesisDepth; return RPAREN_TOK; }
"_"             { indexedIdentifierOpen = true; return UNDERSCORE_TOK; }
"!"             { return EXCLAIMATION_MARK_TOK; }
":"             { return COLON_TOK; }

 /* Set info types */
 /* This is a very restricted set of the possible keywords */
":source"           { return SOURCE_TOK;}
":category"         { return CATEGORY_TOK;}
":difficulty"       { return DIFFICULTY_TOK; }
":smt-lib-version"  { return VERSION_TOK; }
":status"           { return STATUS_TOK; }
":license"          { return LICENSE_TOK; }


  /* Attributes */
":named"        { return NAMED_ATTRIBUTE_TOK; }


 /* COMMANDS */
"assert"                  { return commandToken(ASSERT_TOK); }
"check-sat"               { return commandToken(CHECK_SAT_TOK); }
"check-sat-assuming"      { return commandToken(CHECK_SAT_ASSUMING_TOK);}
"declare-const"           { return commandToken(DECLARE_CONST_TOK); }
"declare-fun"             {
                              if (!commandNamePending) return lookup(smt2text);
                              const int token = commandToken(DECLARE_FUNCTION_TOK);
                              declarationSortsAfterName = true;
                              ufDeclarationNamePending =
                                  stp::GlobalParserInterface->getUserFlags()
                                      .enable_uninterpreted_functions;
                              return token;
                            }
"declare-sort"            { if (!commandNamePending) return lookup(smt2text);
                            sortContext = true; return commandToken(DECLARE_SORT_TOK);}
"declare-sort-parameter"  { if (!commandNamePending) return lookup(smt2text);
                            sortContext = true; return commandToken(DECLARE_SORT_PARAMETER_TOK);}
"define-fun"              { return commandToken(DEFINE_FUNCTION_TOK); }
"define-const"            { return commandToken(DEFINE_CONST_TOK); }
"echo"                    { return commandToken(ECHO_TOK);}
"exit"                    { return commandToken(EXIT_TOK);}
"get-assertions"          { return commandToken(GET_ASSERTIONS_TOK);}
"get-assignment"          { return commandToken(GET_ASSIGNMENT_TOK);}
"get-info"                { if (!commandNamePending) return lookup(smt2text); stp::SMT2BeginAttributes(); return commandToken(GET_INFO_TOK);}
"get-model"               { return commandToken(GET_MODEL_TOK);}
"get-option"              { if (!commandNamePending) return lookup(smt2text); stp::SMT2BeginAttributes(); return commandToken(GET_OPTION_TOK);}
"get-proof"               { return commandToken(GET_PROOF_TOK);}
"get-unsat-assumptions"   { return commandToken(GET_UNSAT_ASSUMPTIONS_TOK);}
"get-unsat-core"          { return commandToken(GET_UNSAT_CORE_TOK);}
"get-value"               { if (!commandNamePending) return lookup(smt2text);
                            const int token = commandToken(GET_VALUE_TOK);
                            BEGIN GET_VALUE_LIST;
                            return token; }
"pop"                     { return commandToken(POP_TOK);}
"push"                    { return commandToken(PUSH_TOK);}
"reset"                   { return commandToken(RESET_TOK);}
"reset-assertions"        { return commandToken(RESET_ASSERTIONS_TOK);}
"set-info"                { if (!commandNamePending) return lookup(smt2text); stp::SMT2BeginAttributes(); return commandToken(NOTES_TOK);  }
"set-logic"               { return commandToken(LOGIC_TOK); }
"set-option"              { if (!commandNamePending) return lookup(smt2text); stp::SMT2BeginAttributes(); return commandToken(SET_OPTION_TOK); }

 /* Commands STP cannot interpret, but which must still parse so that the
  * rest of the script survives. The standard requires the response
  * "unsupported" rather than an error. Their arguments (sorts, recursive
  * function bodies, datatype declarations) are of no use to us, so the
  * lexer swallows the remainder of the s-expression and hands the parser
  * the closing parenthesis. */
"define-fun-rec"   { if (!commandNamePending) return lookup(smt2text); skippedDepth = 0; BEGIN SKIP_SEXPR; return commandToken(DEFINE_FUN_REC_TOK);}
"define-funs-rec"  { if (!commandNamePending) return lookup(smt2text); skippedDepth = 0; BEGIN SKIP_SEXPR; return commandToken(DEFINE_FUNS_REC_TOK);}
"define-sort"      { if (!commandNamePending) return lookup(smt2text);
                     sortContext = true;
                     stp::GlobalParserInterface->beginSortDefinition();
                     return commandToken(DEFINE_SORT_TOK); }

"declare-datatype" { if (!commandNamePending) return lookup(smt2text); skippedDepth = 0; BEGIN SKIP_SEXPR; return commandToken(DECLARE_DATATYPE_TOK);}
"declare-datatypes" { if (!commandNamePending) return lookup(smt2text); skippedDepth = 0; BEGIN SKIP_SEXPR; return commandToken(DECLARE_DATATYPES_TOK);}

 /* Consume a command's arguments without interpreting them, tracking nesting
  * so that the parenthesis returned is the one that closes the command
  * itself. String literals and quoted symbols are matched as units, since
  * either may contain an unbalanced parenthesis. */
<SKIP_SEXPR>"\""([^"]|"\"\"")*"\""  { countNewlines(yytext, yyleng);
                                       /* string literal */ }
<SKIP_SEXPR>"|"[^|]*"|"             { countNewlines(yytext, yyleng);
                                       /* quoted symbol */ }
<SKIP_SEXPR>";"[^\n]*               { /* comment: not captured */ }
<SKIP_SEXPR>"("                     { skippedDepth++;  }
<SKIP_SEXPR>")"                     { if (skippedDepth == 0)
                                        {
                                          BEGIN INITIAL;
                                          --parenthesisDepth;
                                          return RPAREN_TOK;
                                        }
                                      skippedDepth--;  }
<SKIP_SEXPR>[^()|;\"]+              { countNewlines(yytext, yyleng);
                                       }
<SKIP_SEXPR>.                       {  }
<SKIP_SEXPR><<EOF>>                 { BEGIN INITIAL;
                                      return 0; }

 /* The get-value term list: see capturedTerm above. GET_VALUE_LIST reads up
  * to the '(' that opens the list. Anything else there is a syntax error the
  * grammar reports itself, so it is handed back to the ordinary rules.
  * GET_VALUE_TERM copies one term at a time. A bare atom, quoted symbol or
  * string at depth zero is a whole term; a '(' opens one that ends at its
  * matching ')'. Newlines are counted here only outside quotes: the re-scan
  * counts those inside a quoted symbol or string, and sees no others. */
<GET_VALUE_LIST>[ \t\r\f]+            { }
<GET_VALUE_LIST>\n                    { smt2lineno++; }
<GET_VALUE_LIST>";"[^\n]*             { }
<GET_VALUE_LIST>"("                   { smt2lval.uintval = ++parenthesisDepth;
                                        dropCapturedTerms();
                                        BEGIN GET_VALUE_TERM;
                                        return LPAREN_TOK; }
<GET_VALUE_LIST>.                     { yyless(0); BEGIN INITIAL; }
<GET_VALUE_LIST><<EOF>>               { BEGIN INITIAL; return 0; }

<GET_VALUE_TERM>[ \t\r\f]+            { }
<GET_VALUE_TERM>\n                    { smt2lineno++; }
<GET_VALUE_TERM>";"[^\n]*             { }
<GET_VALUE_TERM>"\""([^"]|"\"\"")*"\""  { captureText(smt2text, smt2leng);
                                        if (capturedDepth == 0)
                                          return capturedTermToken(); }
<GET_VALUE_TERM>"|"[^|\\]*"|"          { captureText(smt2text, smt2leng);
                                        if (capturedDepth == 0)
                                          return capturedTermToken(); }
<GET_VALUE_TERM>"("                   { captureText(smt2text, smt2leng);
                                        ++capturedDepth; }
<GET_VALUE_TERM>")"                   { if (capturedDepth == 0)
                                        {
                                          --parenthesisDepth;
                                          BEGIN INITIAL;
                                          return RPAREN_TOK;
                                        }
                                        captureText(smt2text, smt2leng);
                                        if (--capturedDepth == 0)
                                          return capturedTermToken(); }
<GET_VALUE_TERM>[^()|;\" \t\r\n\f]+    { captureText(smt2text, smt2leng);
                                        if (capturedDepth == 0)
                                          return capturedTermToken(); }
<GET_VALUE_TERM>.                     { captureText(smt2text, smt2leng);
                                        if (capturedDepth == 0)
                                          return capturedTermToken(); }
<GET_VALUE_TERM><<EOF>>               { BEGIN INITIAL; return 0; }

 /* The end of a captured term's re-scan: back to the list for the next term
  * or the ')' that closes it. The script's own end is unchanged. */
<INITIAL><<EOF>>                      { if (rescanDepth == 0)
                                          yyterminate();
                                        yypop_buffer_state();
                                        --rescanDepth;
                                        BEGIN GET_VALUE_TERM; }



 /* Syntactically reserved words. Quoted spellings are ordinary symbols.
  * Keep accepting lambda as an SMT-LIB 2.6 identifier, like cvc5 and
  * Bitwuzla. Higher-order lambda terms are not implemented. */
"as"  { qualifiedNamePending = true; return AS_TOK; }
"let" { return LET_TOK; }
"exists"|"forall"|"match"|"par"|"BINARY"|"DECIMAL"|"HEXADECIMAL"|"NUMERAL"|"STRING" {
  return RESERVED_TOK;
}

({LETTER}|{OPCHAR})({ANYTHING})*  {return lookup(smt2text);}
\|[^\|\\]*\| { countNewlines(smt2text, smt2leng); return lookup(smt2text); }

. {
    // Downstream of a declassified declare-fun name the pinned response is
    // the name-position error alone (smt2error prints it in place of this
    // message), and the parse abandons there: the legacy grammar never
    // reached this character. Otherwise report and keep scanning, as ever.
    const bool abandon = stp::SMT2DeclassifiedNamePending();
    smt2error("Illegal input character.");
    if (abandon)
      throw stp::DeclassifiedNameAbandon();
    throw stp::ParseAbandon();
  }
%%

// A captured get-value term is complete: hand its text to the grammar and
// queue the same text as the next input, so the term's node is built by
// the ordinary rules. The pushed buffer pops at its end (<INITIAL><<EOF>>).
static int capturedTermToken()
{
  smt2lval.str = new std::string(capturedTerm);
  yypush_buffer_state(YY_CURRENT_BUFFER);
  yy_scan_string(capturedTerm.c_str());
  ++rescanDepth;
  dropCapturedTerms();
  BEGIN INITIAL;
  return GET_VALUE_TERM_TOK;
}

namespace stp {
  void SMT2ScanString (const char *yy_str) {
    smt2_scan_string(yy_str);
  }

  void setSMT2In(FILE* file) {
    smt2in = file;
  }

  void setSMT2Reader(ParserReader reader, void* opaque) {
    smt2Reader = reader;
    smt2ReaderOpaque = opaque;
  }
}

namespace stp
{
bool SMT2IsTheorySymbol(const std::string& name)
{
  return termTheoryToken(name) != 0;
}
void SMT2BeginAnnotation()
{
  annotations.push_back({GlobalParserInterface->letMgr->depth(), true});
}
bool SMT2EndAnnotation()
{
  assert(!annotations.empty());
  const bool closed = annotations.back().closed;
  annotations.pop_back();
  return closed;
}
void SMT2BeginAttributes()
{
  attributeDepth = 0;
  BEGIN ATTRIBUTE;
}
void SMT2ResetLexMode()
{
  parenthesisDepth = 0;
  BEGIN INITIAL;
}
}
