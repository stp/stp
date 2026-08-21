/*%option reentrant
%option bison-bridge*/
%option noyywrap
%option noreject
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

  // The skipped text, comments excluded, for the one command that is only
  // MOSTLY uninterpreted: define-sort inspects it for the nullary
  // floating-point alias shape (see tryRegisterFpSortAlias in smt2.y).
  //
  // define-sort's token is emitted AFTER the swallowing (deferredDefineSort
  // below), not before like its neighbours': its parser action reads the
  // captured text, and bison runs that action as a default reduction,
  // without fetching the lookahead that would otherwise drive the lexer
  // through the s-expression first.
  static thread_local std::string skippedText;
  static thread_local bool deferredDefineSort = false;

namespace stp
{
  const std::string& smt2_skipped_text() { return skippedText; }

  void SMT2SetFloatTokens(bool enable)
  {
    floatTokensActive = enable;
    // Either direction starts a fresh script's worth of history -- set-logic
    // opens one, reset closes one -- and these are thread-locals that outlive
    // a single parse. A name left behind by an earlier script must not attach
    // its hint to this one's first error.
    unresolvedFpKeyword.clear();
  }

  // define-sort's body never reaches the rules below -- SKIP_SEXPR swallows
  // it and the grammar re-tokenises the text by hand -- so it has to ask the
  // gate itself rather than being answered by it. See tryRegisterFpSortAlias.
  bool SMT2FloatTokensActive() { return floatTokensActive; }

  void SMT2ExpectFunctionParameterName()
  {
    assert(!functionParameterNamePending);
    functionParameterNamePending = true;
  }

  void SMT2ResetCommandLexerState()
  {
    ufDeclarationNamePending = false;
    functionParameterNamePending = false;
    declassifiedNamePending = false;
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

  static int classify(char* s);

  static int lookup(char* s)
  {
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

    if (stringOnly)
    {
      smt2lval.str = new std::string(s);
      return STRING_TOK;
    }

    if (ufDeclarationNamePending)
    {
      // Declare-fun's name position, feature on. Classify exactly as the
      // legacy lexer would, then hand a classified name back unclassified
      // and record what it would have been (see the statics above).
      ufDeclarationNamePending = false;
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
      }
      // Function formals are lexical binders and therefore resolve before
      // all top-level namespaces. Lets remain first because a nested let may
      // shadow a formal in the define-fun body.
      else if (stp::GlobalParserInterface->LookupTemporarySymbol(s, nptr))
        found = true;
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
      smt2lval.str = new std::string(s);
      return STRING_TOK;
    }
  }

  // A name that is a keyword only in the FP logics: outside them it takes
  // the ordinary identifier path, resolving to a declared symbol or coming
  // back as a plain string.
  static int fpKeyword(int token)
  {
    if (floatTokensActive)
      return token;
    const int fallback = lookup(smt2text);
    if (fallback == STRING_TOK)
      unresolvedFpKeyword = smt2text;
    else if (unresolvedFpKeyword == smt2text)
    {
      // The name resolved this time, so the earlier record of it is stale:
      // declaring "NaN" is exactly how a QF_BV file makes it its own, and a
      // later error mentioning it deserves no floating-point hint.
      unresolvedFpKeyword.clear();
    }
    return fallback;
  }
%}

%x  COMMENT
%x  STRING_LITERAL
%x  SYMBOL
%x  SKIP_SEXPR

LETTER  ([a-zA-Z])
DIGIT  ([0-9])
OPCHAR  ([~!@$%^&*\_\-+=<>\.?/])

ANYTHING  ({LETTER}|{DIGIT}|{OPCHAR})

%%
[ \n\t\r\f] { if (*smt2text == '\n') smt2lineno++; /* skip whitespace */ }

 /* Numerals are arbitrary precision in the specification, but every numeral
    STP reads as a number is an index, a width or a count, all of which fit an
    unsigned. One that does not is kept as its digits and returned as a
    different token: a real literal converts from the digits and so stays
    exact, while every other use of a numeral is a syntax error rather than
    the silently wrapped value strtoul would hand back. */
{DIGIT}+               {
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
bv{DIGIT}+             { smt2lval.str = new std::string(smt2text+2); return BVCONST_DECIMAL_TOK; }
#b{DIGIT}+             { smt2lval.str = new std::string(smt2text+2); return BVCONST_BINARY_TOK; }
#x({DIGIT}|[a-fA-F])+  { smt2lval.str = new std::string(smt2text+2); return BVCONST_HEXIDECIMAL_TOK; }
{DIGIT}+"."{DIGIT}+    { smt2lval.str = new std::string(smt2text); return DECIMAL_TOK;}

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
          return STRING_TOK; }
<STRING_LITERAL>.     { _string_lit.insert(_string_lit.end(),*smt2text); }
<STRING_LITERAL>"\n"  { smt2lineno++;
                        _string_lit.insert(_string_lit.end(),*smt2text); }

 /* Valid character are: ~ ! @ # $ % ^ & * _ - + = | \ : ; " < > . ? / ( )     */
"("             { return LPAREN_TOK; }
")"             { return RPAREN_TOK; }
"_"             { return UNDERSCORE_TOK; }
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
"assert"                  { return ASSERT_TOK; }
"check-sat"               { return CHECK_SAT_TOK; }
"check-sat-assuming"      { return CHECK_SAT_ASSUMING_TOK;}
"declare-const"           { return DECLARE_CONST_TOK; }
"declare-fun"             {
                              ufDeclarationNamePending =
                                  stp::GlobalParserInterface->getUserFlags()
                                      .enable_uninterpreted_functions;
                              return DECLARE_FUNCTION_TOK;
                            }
"declare-sort"            { return DECLARE_SORT_TOK;}
"define-fun"              { return DEFINE_FUNCTION_TOK; }
"echo"                    { return ECHO_TOK;}
"exit"                    { return EXIT_TOK;}
"get-assertions"          { return GET_ASSERTIONS_TOK;}
"get-assignment"          { return GET_ASSIGNMENT_TOK;}
"get-info"                { return GET_INFO_TOK;}
"get-model"               { return GET_MODEL_TOK;}
"get-option"              { return GET_OPTION_TOK;}
"get-proof"               { return GET_PROOF_TOK;}
"get-unsat-assumptions"   { return GET_UNSAT_ASSUMPTIONS_TOK;}
"get-unsat-core"          { return GET_UNSAT_CORE_TOK;}
"get-value"               { return GET_VALUE_TOK;}
"pop"                     { return POP_TOK;}
"push"                    { return PUSH_TOK;}
"reset"                   { return RESET_TOK;}
"reset-assertions"        { return RESET_ASSERTIONS_TOK;}
"set-info"                { return NOTES_TOK;  }
"set-logic"               { return LOGIC_TOK; }
"set-option"              { return SET_OPTION_TOK; }

 /* Commands STP cannot interpret, but which must still parse so that the
  * rest of the script survives. The standard requires the response
  * "unsupported" rather than an error. Their arguments (sorts, recursive
  * function bodies, datatype declarations) are of no use to us, so the
  * lexer swallows the remainder of the s-expression and hands the parser
  * the closing parenthesis. */
"define-fun-rec"   { skippedDepth = 0; BEGIN SKIP_SEXPR; return DEFINE_FUN_REC_TOK;}
"define-funs-rec"  { skippedDepth = 0; BEGIN SKIP_SEXPR; return DEFINE_FUNS_REC_TOK;}
"define-sort"      { skippedDepth = 0; skippedText.clear();
                     deferredDefineSort = true; BEGIN SKIP_SEXPR; }
"declare-datatype" { skippedDepth = 0; BEGIN SKIP_SEXPR; return DECLARE_DATATYPE_TOK;}
"declare-datatypes" { skippedDepth = 0; BEGIN SKIP_SEXPR; return DECLARE_DATATYPES_TOK;}

 /* Consume a command's arguments without interpreting them, tracking nesting
  * so that the parenthesis returned is the one that closes the command
  * itself. String literals and quoted symbols are matched as units, since
  * either may contain an unbalanced parenthesis. */
<SKIP_SEXPR>"\""([^"]|"\"\"")*"\""  { countNewlines(yytext, yyleng);
                                      skippedText += yytext; /* string literal */ }
<SKIP_SEXPR>"|"[^|]*"|"             { countNewlines(yytext, yyleng);
                                      skippedText += yytext; /* quoted symbol */ }
<SKIP_SEXPR>";"[^\n]*               { /* comment: not captured */ }
<SKIP_SEXPR>"("                     { skippedDepth++; skippedText += '('; }
<SKIP_SEXPR>")"                     { if (skippedDepth == 0)
                                        {
                                          BEGIN INITIAL;
                                          if (deferredDefineSort)
                                          {
                                            // Hand back the closer so it
                                            // arrives as the next token.
                                            deferredDefineSort = false;
                                            unput(')');
                                            return DEFINE_SORT_TOK;
                                          }
                                          return RPAREN_TOK;
                                        }
                                      skippedDepth--; skippedText += ')'; }
<SKIP_SEXPR>[^()|;\"]+              { countNewlines(yytext, yyleng);
                                      skippedText += yytext; }
<SKIP_SEXPR>.                       { skippedText += yytext; }
<SKIP_SEXPR><<EOF>>                 { BEGIN INITIAL; deferredDefineSort = false;
                                      return 0; }



 /* Types for QF_BV and QF_ABV. */
"BitVec"        { return BITVEC_TOK;}
"Array"         { return ARRAY_TOK;}
"Bool"          { return BOOL_TOK;}

 /* Types for QF_FP and QF_BVFP. These and every other floating-point
  * name go through fpKeyword(): they are keywords only while an FP logic
  * is set, and ordinary identifiers otherwise. */
"FloatingPoint" { return fpKeyword(FLOATINGPOINT_TOK); }
"RoundingMode" { return fpKeyword(ROUNDINGMODE_TOK); }
"Float16" { return fpKeyword(FLOAT16_TOK); }
"Float32" { return fpKeyword(FLOAT32_TOK); }
"Float64" { return fpKeyword(FLOAT64_TOK); }
"Float128" { return fpKeyword(FLOAT128_TOK); }


 /* CORE THEORY pg. 29 of the SMT-LIB2 standard 30-March-2010. */
"true"          { return TRUE_TOK; }
"false"         { return FALSE_TOK; }
"not"           { return NOT_TOK; }
"and"           { return AND_TOK; }
"or"            { return OR_TOK; }
"xor"           { return XOR_TOK;}
"ite"           { return ITE_TOK;} // PARAMETRIC
"="             { return EQ_TOK;}
"=>"           { return IMPLIES_TOK; }

 /* CORE THEORY. But not on pg 29. */
"distinct"      { return DISTINCT_TOK; }  // variadic
"let"           { return LET_TOK; }

 /* Functions for QF_BV and QF_AUFBV.  */
"bvshl"         { return BVLEFTSHIFT_1_TOK;}
"bvlshr"        { return BVRIGHTSHIFT_1_TOK;}
"bvashr"        { return BVARITHRIGHTSHIFT_TOK;}
"bvadd"         { return BVPLUS_TOK;}
"bvsub"         { return BVSUB_TOK;}
"bvnot"         { return BVNOT_TOK;}
"bvmul"         { return BVMULT_TOK;}
"bvudiv"        { return BVDIV_TOK;}
"bvsdiv"        { return SBVDIV_TOK;}
"bvurem"        { return BVMOD_TOK;}
"bvsrem"        { return SBVREM_TOK;}
"bvsmod"        { return SBVMOD_TOK;}
"bvneg"         { return BVNEG_TOK;}
"bvand"         { return BVAND_TOK;}
"bvor"          { return BVOR_TOK;}
"bvxor"         { return BVXOR_TOK;}
"bvnand"        { return BVNAND_TOK;}
"bvnor"         { return BVNOR_TOK;}
"bvxnor"        { return BVXNOR_TOK;}
"concat"        { return BVCONCAT_TOK;}
"extract"       { return BVEXTRACT_TOK;}
"bvult"         { return BVLT_TOK;}
"bvugt"         { return BVGT_TOK;}
"bvule"         { return BVLE_TOK;}
"bvuge"         { return BVGE_TOK;}
"bvslt"         { return BVSLT_TOK;}
"bvsgt"         { return BVSGT_TOK;}
"bvsle"         { return BVSLE_TOK;}
"bvsge"         { return BVSGE_TOK;}
"bvcomp"        { return BVCOMP_TOK;}
"zero_extend"   { return BVZX_TOK;}
"sign_extend"   { return BVSX_TOK;}
"repeat"        { return BVREPEAT_TOK;}
"rotate_left"   { return BVROTATE_LEFT_TOK;}
"rotate_right"  { return BVROTATE_RIGHT_TOK;}
"bvnego"        { return BVNEGO_TOK;}
"bvuaddo"       { return BVUADDO_TOK;}
"bvsaddo"       { return BVSADDO_TOK;}
"bvumulo"       { return BVUMULO_TOK;}
"bvsmulo"       { return BVSMULO_TOK;}
"bvusubo"       { return BVUSUBO_TOK;}
"bvssubo"       { return BVSSUBO_TOK;}
"bvsdivo"       { return BVSDIVO_TOK;}

 /* Functions for QF_AUFBV. */
"select"        { return SELECT_TOK; }
"store"         { return STORE_TOK; }

 /*
  * NOTE: the call to `lookup` below is *extremely* greedy -- it means we
  * cannot search for FP DOT ADD, we have to search for the whole thing --
  * c'est la vie
  */

 /* generic FP token*/
"fp" { return fpKeyword(FP_TOK); }

 /* FP conversions */
"to_fp" { return fpKeyword(FP_TOFP_TOK); }
"to_fp_unsigned" { return fpKeyword(FP_TOFP_UNSIGNED_TOK); }
"fp.to_ubv" { return fpKeyword(FP_TO_UBV_TOK); }
"fp.to_sbv" { return fpKeyword(FP_TO_SBV_TOK); }

 /* Functions for FP */
"fp.to_real" { return fpKeyword(FP_TO_REAL_TOK); }
"fp.abs" { return fpKeyword(FP_ABS_TOK); }
"fp.neg" { return fpKeyword(FP_NEG_TOK); }
"fp.add" { return fpKeyword(FP_ADD_TOK); }
"fp.sub" { return fpKeyword(FP_SUB_TOK); }
"fp.mul" { return fpKeyword(FP_MUL_TOK); }
"fp.div" { return fpKeyword(FP_DIV_TOK); }
"fp.fma" { return fpKeyword(FP_FMA_TOK); }
"fp.sqrt" { return fpKeyword(FP_SQRT_TOK); }
"fp.rem" { return fpKeyword(FP_REM_TOK); }
"fp.roundToIntegral" { return fpKeyword(FP_ROUNDTOINTEGRAL_TOK); }
"fp.min" { return fpKeyword(FP_MIN_TOK); }
"fp.max" { return fpKeyword(FP_MAX_TOK); }
"fp.leq" { return fpKeyword(FP_LEQ_TOK); }
"fp.lt" { return fpKeyword(FP_LT_TOK); }
"fp.geq" { return fpKeyword(FP_GEQ_TOK); }
"fp.gt" { return fpKeyword(FP_GT_TOK); }
"fp.eq" { return fpKeyword(FP_EQ_TOK); }
"fp.isNormal" { return fpKeyword(FP_ISNORMAL_TOK); }
"fp.isSubnormal" { return fpKeyword(FP_ISSUBNORMAL_TOK); }
"fp.isZero" { return fpKeyword(FP_ISZERO_TOK); }
"fp.isInfinite" { return fpKeyword(FP_ISINFINITE_TOK); }
"fp.isNaN" { return fpKeyword(FP_ISNAN_TOK); }
"fp.isNegative" { return fpKeyword(FP_ISNEGATIVE_TOK); }
"fp.isPositive" { return fpKeyword(FP_ISPOSITIVE_TOK); }

 /* rounding modes */
"roundTowardZero" { return fpKeyword(FP_RM_ROUNDTOWARDZERO_TOK); }
"roundNearestTiesToEven" { return fpKeyword(FP_RM_ROUNDNEARESTTIESTOEVEN_TOK); }
"roundNearestTiesToAway" { return fpKeyword(FP_RM_ROUNDNEARESTTIESTOAWAY_TOK); }
"roundTowardPositive" { return fpKeyword(FP_RM_ROUNDTOWARDPOSITIVE_TOK); }
"roundTowardNegative" { return fpKeyword(FP_RM_ROUNDTOWARDNEGATIVE_TOK); }

"RTZ" { return fpKeyword(FP_RM_ROUNDTOWARDZERO_TOK); }
"RNE" { return fpKeyword(FP_RM_ROUNDNEARESTTIESTOEVEN_TOK); }
"RNA" { return fpKeyword(FP_RM_ROUNDNEARESTTIESTOAWAY_TOK); }
"RTP" { return fpKeyword(FP_RM_ROUNDTOWARDPOSITIVE_TOK); }
"RTN" { return fpKeyword(FP_RM_ROUNDTOWARDNEGATIVE_TOK); }

 /* fp constants */
"NaN" { return fpKeyword(FP_NAN_TOK); }
"-oo" { return fpKeyword(FP_NEG_INF_TOK); }
"+oo" { return fpKeyword(FP_POS_INF_TOK); }
"-zero" { return fpKeyword(FP_NEG_ZERO_TOK); }
"+zero" { return fpKeyword(FP_POS_ZERO_TOK); }


({LETTER}|{OPCHAR})({ANYTHING})*  {return lookup(smt2text);}
\|([^\|]|[\x80-\xff]|\n)*\| { countNewlines(smt2text, smt2leng); return lookup(smt2text); }

. {
    // Downstream of a declassified declare-fun name the pinned response is
    // the name-position error alone (smt2error prints it in place of this
    // message), and the parse abandons there: the legacy grammar never
    // reached this character. Otherwise report and keep scanning, as ever.
    const bool abandon = stp::SMT2DeclassifiedNamePending();
    smt2error("Illegal input character.");
    if (abandon)
      throw stp::DeclassifiedNameAbandon();
  }
%%

namespace stp {
  void SMT2ScanString (const char *yy_str) {
    smt2_scan_string(yy_str);
  }

  FILE* getSMT2In() {
    return smt2in;
  }

  void setSMT2In(FILE* file) {
    smt2in = file;
  }

  void setSMT2Interactive(bool enable) {
    if (smt2in == NULL)
      smt2in = stdin;
    yy_set_interactive(enable ? 1 : 0);
  }
}
