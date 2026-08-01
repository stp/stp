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

#include "stp/cpp_interface.h"
#include "stp/Parser/LetMgr.h"
#include "stp/Parser/parser.h"
#include "stp/FloatBlaster/FloatBlaster.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "parsesmt2.tab.h"
#include "smt2_flex_header.h"

#include <cctype>
#include <cstdlib>
#include <string>
#include <vector>

namespace stp
{
  // Defined in smt2.lex: the text SKIP_SEXPR swallowed for the current
  // command, comments excluded. define-sort inspects it (see
  // tryRegisterFpSortAlias below).
  const std::string& smt2_skipped_text();
}


  using std::cout;
  using std::cerr;
  using std::endl;

  using stp::SYMBOL;       //!< Named expression (or variable), i.e. created via 'vc_varExpr'.
  using stp::BVNOT;        //!< Bitvector bitwise-not
  using stp::BVCONCAT;     //!< Bitvector concatenation
  using stp::BVOR;         //!< Bitvector bitwise-or
  using stp::BVAND;        //!< Bitvector bitwise-and
  using stp::BVXOR;        //!< Bitvector bitwise-xor
  using stp::BVNAND;       //!< Bitvector bitwise not-and; OR nand (TODO: does this still exist?)
  using stp::BVNOR;        //!< Bitvector bitwise not-or; OR nor (TODO: does this still exist?)
  using stp::BVXNOR;       //!< Bitvector bitwise not-xor; OR xnor (TODO: does this still exist?)
  using stp::BVEXTRACT;    //!< Bitvector extraction, i.e. via 'vc_bvExtract'.
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
  using stp::ARRAY;        //!< Array creation expression
  using stp::BITVECTOR;    //!< Bitvector creation expression
  using stp::BOOLEAN;      //!< Boolean creation expression

  using stp::UNDEFINED;    //!< An undefined expression.
  using stp::SYMBOL;       //!< Named expression (or variable), i.e. created via 'vc_varExpr'.
  using stp::BVCONST;      //!< Bitvector constant expression, i.e. created via 'vc_bvConstExprFromInt'.
  using stp::BVNOT;        //!< Bitvector bitwise-not
  using stp::BVCONCAT;     //!< Bitvector concatenation
  using stp::BVOR;         //!< Bitvector bitwise-or
  using stp::BVAND;        //!< Bitvector bitwise-and
  using stp::BVXOR;        //!< Bitvector bitwise-xor
  using stp::BVNAND;       //!< Bitvector bitwise not-and; OR nand (TODO: does this still exist?)
  using stp::BVNOR;        //!< Bitvector bitwise not-or; OR nor (TODO: does this still exist?)
  using stp::BVXNOR;       //!< Bitvector bitwise not-xor; OR xnor (TODO: does this still exist?)
  using stp::BVEXTRACT;    //!< Bitvector extraction, i.e. via 'vc_bvExtract'.
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
  using stp::ARRAY;        //!< Array creation expression
  using stp::BITVECTOR;    //!< Bitvector creation expression
  using stp::BOOLEAN;      //!< Boolean creation expression

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
  using stp::SOLVER_TIMEOUT;
  using stp::SOLVER_ERROR;
  using stp::SOLVER_UNSATISFIABLE;
  using stp::SOLVER_SATISFIABLE;

  extern char* smt2text;
  extern int smt2lineno;
  extern bool stringOnly;

  int yyerror(const char *s) {
    cout << "(error \"syntax error: line " << smt2lineno << " " << s << "  token: " << smt2text << "\")" << endl;
    return 1;
  }

  int fatal_yyerror(const char *s) 
  {
    yyerror(s);
    stp::FatalError("");
  }

  // STP's lowering layer intentionally treats a float's packed
  // representation as bits, but that is an internal implementation detail.
  // At the SMT-LIB boundary a BV operator accepts only a BitVec-sorted term;
  // callers must use fp.to_ieee_bv to expose a float's representation.
  void checkBitVectorTerm(const ASTNode& n)
  {
    if (n.GetType() != BITVECTOR_TYPE)
      fatal_yyerror("bitvector operator requires bitvector operands");
  }

  void checkBitVectorTerms(const ASTVec& terms)
  {
    for (const ASTNode& term : terms)
      checkBitVectorTerm(term);
  }

  ASTNode* createNode(Kind k, ASTVec * c)
  {
    if (c->size() < 2)
    {
      yyerror("Must be >=2 operands.");
      exit(1);
    }
   ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(k, *c));
   delete c;
   return n;
   }

  ASTNode* createNode(Kind k, ASTNode* c0, ASTNode *c1)
  {
    // Every binary call to this overload is a BV predicate/overflow
    // production. Boolean connectives use the vector overload.
    checkBitVectorTerm(*c0);
    checkBitVectorTerm(*c1);
    ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateNode(k, *c0, *c1));
    delete c0;
    delete c1;
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
    if (!stp::GlobalParserBM->isRoundingModeSortedTerm(*rm))
    {
      fatal_yyerror("expected a rounding mode.");
    }
  }

  // fp.add/fp.sub/fp.mul/fp.div. Each is ternary -- the rounding mode is
  // child 0, matching the arity declared in ASTKind.kinds -- so that the
  // blaster rounds as the input asked rather than assuming RNE.
  // The rounding-mode argument is taken as a plain an_term rather than an
  // an_rounding_mode: an_term already derives an_rounding_mode, so using the
  // narrower nonterminal here makes the position ambiguous and LALR resolves
  // it by swallowing the rounding mode as the first operand. Checking the
  // rounding mode here (and again in BVTypeCheck) costs nothing by comparison.
  ASTNode* createFPArith(Kind k, ASTNode* rm, ASTNode* lhs, ASTNode* rhs)
  {
    checkRoundingMode(rm);

    if (lhs->GetType() != FLOATINGPOINT_TYPE ||
        rhs->GetType() != FLOATINGPOINT_TYPE)
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
    delete rm;
    delete lhs;
    delete rhs;
    return n;
  }

  // fp.leq/fp.lt/fp.geq/fp.gt. These are chainable in SMT-LIB, so (fp.lt x y z)
  // means (and (fp.lt x y) (fp.lt y z)).
  ASTNode* createFPChain(Kind k, ASTVec* terms, const char* name)
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
      if ((*terms)[i].GetType() != FLOATINGPOINT_TYPE)
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
    delete terms;
    return n;
  }

  // fp.rem/fp.min/fp.max: two floats of the same format in, one out. Unlike
  // fp.add and friends these take no rounding mode.
  ASTNode* createFPBinary(Kind k, ASTNode* lhs, ASTNode* rhs)
  {
    if (lhs->GetType() != FLOATINGPOINT_TYPE ||
        rhs->GetType() != FLOATINGPOINT_TYPE)
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
    delete lhs;
    delete rhs;
    return n;
  }

  // fp.fma: a rounding mode and three floats of the same format.
  ASTNode* createFPFma(ASTNode* rm, ASTNode* x, ASTNode* y, ASTNode* z)
  {
    checkRoundingMode(rm);

    if (x->GetType() != FLOATINGPOINT_TYPE ||
        y->GetType() != FLOATINGPOINT_TYPE ||
        z->GetType() != FLOATINGPOINT_TYPE)
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
    delete rm;
    delete x;
    delete y;
    delete z;
    return n;
  }

  // fp.sqrt: a rounding mode and one float.
  ASTNode* createFPSqrt(ASTNode* rm, ASTNode* expr)
  {
    checkRoundingMode(rm);

    if (expr->GetType() != FLOATINGPOINT_TYPE)
    {
      fatal_yyerror("argument to fp.sqrt must be a float.");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(FP_SQRT,
                                                   expr->GetValueWidth(), *rm,
                                                   *expr));
    setFPFormat(n, expr->GetExpWidth(), expr->GetSigWidth());
    delete rm;
    delete expr;
    return n;
  }

  // (fp.roundToIntegral rm f). The mode is an ordinary term, exactly as in
  // fp.sqrt, so a RoundingMode variable is accepted as well as the five
  // literal modes.
  ASTNode* createFPRoundToIntegral(ASTNode* rm, ASTNode* expr)
  {
    checkRoundingMode(rm);

    if (expr->GetType() != FLOATINGPOINT_TYPE)
    {
      fatal_yyerror("argument to fp.roundToIntegral must be a float.");
    }

    // Every other operation works at these formats; only this one reaches
    // symfpu's off-by-one guard. Refused per operation, as fp.rem is, rather
    // than by taking the whole format away.
    if (!stp::FloatBlaster::roundToIntegralSupported(expr->GetExpWidth(),
                                                     expr->GetSigWidth()))
    {
      fatal_yyerror("fp.roundToIntegral is not supported at this format: "
                    "symfpu resizes its rounding point with matchWidth, "
                    "which may only widen, on a guard one bit short of the "
                    "width being resized");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(FP_ROUNDTOINTEGRAL,
                                                   expr->GetValueWidth(), *rm,
                                                   *expr));
    setFPFormat(n, expr->GetExpWidth(), expr->GetSigWidth());
    delete rm;
    delete expr;
    return n;
  }

  // On a build without floating-point support, reject floating-point input
  // at its first construct, with a line number and the fix. Called from
  // every path that introduces a float: the sort and conversion forms (via
  // checkFpFormatWidths), (fp ...) literals, and the QF_*FP* logics. The
  // STPMgr funnels (SetExpWidth/CreateFPConst) back this up for input that
  // arrives through the C API instead of the parser.
  void checkFpSupported()
  {
#ifndef STP_ENABLE_FLOATING_POINT
    fatal_yyerror("this STP was built without floating-point support; "
                  "reconfigure with -DENABLE_FLOATING_POINT=ON");
#endif
  }

  // The indexed to_fp forms and the special values carry the format as
  // numerals; apply the floor the sort rule enforces.
  void checkFpFormatWidths(unsigned int exp_width, unsigned int sig_width)
  {
    checkFpSupported();
    if (exp_width < 2 || sig_width < 2)
    {
      fatal_yyerror("a floating-point format needs at least 2 exponent and "
                    "2 significand bits");
    }

    // SMT-LIB's own floor stops above; this one is symfpu's. Refused here
    // rather than in the blaster, where the widths underflow into a
    // segfault -- see FloatBlaster::formatSupported.
    if (!stp::FloatBlaster::formatSupported(exp_width, sig_width))
    {
      fatal_yyerror("this floating-point format is not supported: symfpu "
                    "needs an unpacked exponent wider than the format's own, "
                    "which does not hold once the significand is 3 bits or "
                    "fewer; use at least 4 significand bits");
    }
  }

  // (define-sort <name> () <floating-point sort>) is the one define-sort STP
  // implements. The lexer swallows every define-sort's arguments (SKIP_SEXPR
  // in smt2.lex), which is what lets the uninterpreted shapes -- parametric
  // sorts, sorts STP lacks, parentheses hiding in comments -- be answered
  // "unsupported" without parsing them; this inspects the swallowed text
  // (comments already excluded) and registers the alias when it has the one
  // implemented shape. Returns false to answer "unsupported" instead.
  bool tryRegisterFpSortAlias(const std::string& text)
  {
    std::vector<std::string> toks;
    std::string cur;
    for (const char c : text)
    {
      if (c == '(' || c == ')')
      {
        if (!cur.empty())
        {
          toks.push_back(cur);
          cur.clear();
        }
        toks.push_back(std::string(1, c));
      }
      else if (isspace(static_cast<unsigned char>(c)))
      {
        if (!cur.empty())
        {
          toks.push_back(cur);
          cur.clear();
        }
      }
      else
      {
        cur += c;
      }
    }
    if (!cur.empty())
      toks.push_back(cur);

    // <name> ( ) followed by a named format or ( _ FloatingPoint eb sb ).
    if (toks.size() < 4 || toks[0] == "(" || toks[0] == ")" ||
        toks[1] != "(" || toks[2] != ")")
      return false;

    unsigned int exp_width, sig_width;
    if (toks.size() == 4)
    {
      if (toks[3] == "Float16")
      {
        exp_width = 5; sig_width = 11;
      }
      else if (toks[3] == "Float32")
      {
        exp_width = 8; sig_width = 24;
      }
      else if (toks[3] == "Float64")
      {
        exp_width = 11; sig_width = 53;
      }
      else if (toks[3] == "Float128")
      {
        exp_width = 15; sig_width = 113;
      }
      else
        return false;
    }
    else if (toks.size() == 9 && toks[3] == "(" && toks[4] == "_" &&
             toks[5] == "FloatingPoint" && toks[8] == ")" &&
             !toks[6].empty() && !toks[7].empty() &&
             toks[6].find_first_not_of("0123456789") == std::string::npos &&
             toks[7].find_first_not_of("0123456789") == std::string::npos)
    {
      exp_width = static_cast<unsigned int>(strtoul(toks[6].c_str(), NULL, 10));
      sig_width = static_cast<unsigned int>(strtoul(toks[7].c_str(), NULL, 10));
    }
    else
      return false;

    checkFpFormatWidths(exp_width, sig_width);
    // A real alias table: the name maps to a format, and is NOT interned as a
    // symbol -- the old scheme made the sort name usable as a term variable.
    stp::GlobalParserInterface->addSortAlias(toks[0], exp_width, sig_width);
    return true;
  }

  // ((_ to_fp_unsigned e s) rm bv) -- convert an unsigned integer held in a
  // bitvector to the nearest float.
  ASTNode* createFPFromUnsignedBV(unsigned int exp_width,
                                  unsigned int sig_width, ASTNode* rm,
                                  ASTNode* bits)
  {
    checkFpFormatWidths(exp_width, sig_width);
    checkRoundingMode(rm);

    if (bits->GetType() != BITVECTOR_TYPE)
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
    delete rm;
    delete bits;
    return n;
  }

  // ((_ fp.to_ubv m) rm x) / ((_ fp.to_sbv m) rm x): round a float to an
  // integer of width m. The result is a bitvector, not a float, so it gets no
  // floating-point format. The value for the inputs SMT-LIB leaves
  // unspecified is added later, by FpTotalise.
  ASTNode* createFPToBV(Kind k, unsigned int target_width, ASTNode* rm,
                        ASTNode* expr)
  {
    if (target_width == 0)
      fatal_yyerror("fp.to_ubv/fp.to_sbv width must be positive.");

    checkRoundingMode(rm);

    if (expr->GetType() != FLOATINGPOINT_TYPE)
      fatal_yyerror("argument to fp.to_ubv/fp.to_sbv must be a float.");

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(
            k, target_width,
            stp::GlobalParserInterface->CreateBVConst(32, target_width), *rm,
            *expr));
    delete rm;
    delete expr;
    return n;
  }

  // fp.abs/fp.neg: a float in, a float of the same format out.
  ASTNode* createFPUnary(Kind k, ASTNode* expr)
  {
    if (expr->GetType() != FLOATINGPOINT_TYPE)
    {
      fatal_yyerror("argument to a floating-point operation must be a float.");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(k, expr->GetValueWidth(),
                                                   *expr));
    setFPFormat(n, expr->GetExpWidth(), expr->GetSigWidth());
    delete expr;
    return n;
  }

  // fp.isNaN and friends: a float in, a Boolean out.
  ASTNode* createFPPredicate(Kind k, ASTNode* expr)
  {
    if (expr->GetType() != FLOATINGPOINT_TYPE)
    {
      fatal_yyerror("argument to a floating-point predicate must be a float.");
    }

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateNode(k, *expr));
    delete expr;
    return n;
  }

  // ((_ to_fp e s) bv) -- reinterpret a bitvector's bits as a float.
  ASTNode* createFPFromBits(unsigned int exp_width, unsigned int sig_width,
                            ASTNode* bits)
  {
    checkFpFormatWidths(exp_width, sig_width);
    if (bits->GetType() != BITVECTOR_TYPE)
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
    delete bits;
    return n;
  }

  // (fp sign exp sig) -- build a float from its three bitvector components:
  // a one-bit sign, an e-bit exponent, and the (s-1)-bit stored significand
  // (the hidden bit is implicit). SMT-LIB permits each component to be an
  // arbitrary bitvector term, not just a literal, so concatenate them and
  // reinterpret the packed bits -- folding to an interned float constant when
  // every component is literal, exactly as the one-argument to_fp does.
  ASTNode* createFPFromParts(ASTNode* sign, ASTNode* exp, ASTNode* sig)
  {
    checkFpSupported();
    if (sign->GetType() != BITVECTOR_TYPE || exp->GetType() != BITVECTOR_TYPE ||
        sig->GetType() != BITVECTOR_TYPE)
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

  // ((_ to_fp e s) rm f) -- reformat a float under a rounding mode.
  ASTNode* createFPToFP(unsigned int exp_width, unsigned int sig_width,
                        ASTNode* rm, ASTNode* expr)
  {
    checkFpFormatWidths(exp_width, sig_width);
    checkRoundingMode(rm);

    // The rm-taking form of to_fp covers three different operations,
    // distinguished by the source's sort: reformatting a float, converting a
    // signed integer held in a bitvector, and converting a real. The first
    // two are handled; a real cannot be represented here, and STP has no
    // real sort to reach this rule with anyway.
    if (expr->GetType() != FLOATINGPOINT_TYPE &&
        expr->GetType() != BITVECTOR_TYPE)
    {
      fatal_yyerror("to_fp's argument must be a float or a bitvector.");
    }

    // Which of the two it is has to be recorded now, in the kind. The sort is
    // only reliable here: a float is carried as its packed bits, so once the
    // operand has been lowered it is indistinguishable from the integer.
    const Kind k =
        (expr->GetType() == FLOATINGPOINT_TYPE) ? FP_TOFP : FP_TOFP_SIGNED;

    ASTNode* n = stp::GlobalParserInterface->newNode(
        stp::GlobalParserInterface->nf->CreateTerm(
            k, exp_width + sig_width,
            stp::GlobalParserInterface->CreateBVConst(32, exp_width),
            stp::GlobalParserInterface->CreateBVConst(32, sig_width), *rm,
            ASTVec(1, *expr)));
    setFPFormat(n, exp_width, sig_width);
    delete rm;
    delete expr;
    return n;
  }

  ASTNode* createTerm(Kind k, ASTVec * c)
  {
    assert(k != BVEXTRACT);
    assert(k != BVCONCAT); // width must be width of first operand.
        
    if (c->size() < 2)
    {
      yyerror("Must be >=2 operands");
      exit(1);
    }
    checkBitVectorTerms(*c);
    const unsigned int width = (*c)[0].GetValueWidth();
    ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(k, width,  *c));
    delete c;
    return n;
  }

  ASTNode* createTerm(Kind k, ASTNode* c0, ASTNode *c1)
  {
    checkBitVectorTerm(*c0);
    checkBitVectorTerm(*c1);
    const unsigned int width = c0->GetValueWidth();
    ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(k, width, *c0, *c1));
    delete c0;
    delete c1;
    return n;
  }

  // (bvnego s) is true iff negating s overflows, i.e. iff s is the signed
  // minimum value INT_MIN (100...0). Desugar it to (= s INT_MIN).
  ASTNode* createNegOverflow(ASTNode* c0)
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
    delete c0;
    return n;
  }

  // (bvsdivo s t) is true iff the signed division s/t overflows. This happens
  // only for INT_MIN / -1, so desugar it to (and (= s INT_MIN) (= t -1)).
  ASTNode* createSDivOverflow(ASTNode* c0, ASTNode* c1)
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
    delete c0;
    delete c1;
    return n;
  }

  // Declare an array symbol from a parsed (Array X Y) sort: the shared body
  // of the declare-fun and declare-const productions. Frees both arguments.
  void declareArraySymbol(std::string* name, stp::array_sort* sort)
  {
    ASTNode s =
        stp::GlobalParserInterface->LookupOrCreateSymbol(name->c_str());
    stp::GlobalParserInterface->addArraySymbol(s, *sort);

    if (s.GetType() != ARRAY_TYPE)
      fatal_yyerror("failed to declare an array.");

    delete name;
    delete sort;
  }

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
  unsigned uintval; /* for numerals in types. */
  stp::Kind kind;
  stp::float_size* fp_size;
  stp::array_sort_component* arr_component;
  stp::array_sort* arr_sort;

  //ASTNode,ASTVec
  stp::ASTNode *node;
  stp::ASTVec *vec;

  std::string *str;
};

%start cmd

%type <node> status
%type <vec> an_formulas an_terms function_params an_mixed


%type <node> an_term  an_formula function_param an_const an_fp_term an_fp_predicate an_rounding_mode
%type <uintval> an_fp_const
%type <str> info_flag

%type <fp_size> an_fp_sort
%type <arr_component> an_array_sort_component
%type <arr_sort> an_array_sort

%token <uintval> NUMERAL_TOK
%token <str> BVCONST_DECIMAL_TOK
%token <str> BVCONST_BINARY_TOK
%token <str> BVCONST_HEXIDECIMAL_TOK

 /* We have this so we can parse :smt-lib-version 2.0 */
%token  DECIMAL_TOK

%token <node> FORMID_TOK TERMID_TOK
%token <str> STRING_TOK BITVECTOR_FUNCTIONID_TOK BOOLEAN_FUNCTIONID_TOK FLOATINGPOINT_FUNCTIONID_TOK ARRAY_FUNCTIONID_TOK


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
%token LPAREN_TOK
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
%token FLOAT16_TOK
%token FLOAT32_TOK
%token FLOAT64_TOK
%token FLOAT128_TOK

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
%token DEFINE_FUNCTION_TOK
%token DEFINE_FUN_REC_TOK
%token DEFINE_FUNS_REC_TOK
%token DEFINE_SORT_TOK
%token DECLARE_DATATYPE_TOK
%token DECLARE_DATATYPES_TOK
%token ECHO_TOK
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
cmd: commands END
{
       stp::GlobalParserInterface->cleanUp();
       YYACCEPT;
}
;


commands: commands LPAREN_TOK cmdi RPAREN_TOK
| LPAREN_TOK cmdi RPAREN_TOK
{}
;

cmdi:
     ASSERT_TOK an_formula
    {
      stp::GlobalParserInterface->AddAssert(*$2);
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
      // symbols or their negations. We accept any boolean formula, which is a
      // superset, because the command is not supported either way.
      stp::GlobalParserInterface->unsupported();
      delete $3;
    }
|
     CHECK_SAT_ASSUMING_TOK LPAREN_TOK RPAREN_TOK
    {
      stp::GlobalParserInterface->unsupported();
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
     ECHO_TOK STRING_TOK
    {
      std::cout << "\"" << *$2  << "\"" << endl;
      delete $2;
      stp::GlobalParserInterface->success();
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
      delete $3;
    }
|
     SET_OPTION_TOK COLON_TOK STRING_TOK STRING_TOK
    {
       stp::GlobalParserInterface->setOption(*$3,*$4);
       delete $3;
       delete $4;
    }
|
     SET_OPTION_TOK COLON_TOK STRING_TOK FALSE_TOK
    {
       stp::GlobalParserInterface->setOption(*$3,"false");
       delete $3;
    }
|
     SET_OPTION_TOK COLON_TOK STRING_TOK TRUE_TOK
    {
       stp::GlobalParserInterface->setOption(*$3,"true");
       delete $3;
    }
|
     /* :random-seed, :verbosity and :reproducible-resource-limit take a
        numeral. */
     SET_OPTION_TOK COLON_TOK STRING_TOK NUMERAL_TOK
    {
       stp::GlobalParserInterface->setOption(*$3,std::to_string($4));
       delete $3;
    }
|
     GET_OPTION_TOK COLON_TOK STRING_TOK
    {
       stp::GlobalParserInterface->getOption(*$3);
       delete $3;
    }
|
     GET_INFO_TOK info_flag
    {
       stp::GlobalParserInterface->getInfo(*$2);
       delete $2;
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
       stp::GlobalParserInterface->unsupported();
    }
|
     GET_PROOF_TOK
    {
       stp::GlobalParserInterface->unsupported();
    }
|
     GET_UNSAT_CORE_TOK
    {
       stp::GlobalParserInterface->unsupported();
    }
|
     GET_UNSAT_ASSUMPTIONS_TOK
    {
       stp::GlobalParserInterface->unsupported();
    }
|
     /* STP's sorts are fixed: bitvectors, booleans and arrays of them. */
     DECLARE_SORT_TOK STRING_TOK NUMERAL_TOK
    {
       stp::GlobalParserInterface->unsupported();
       delete $2;
    }
|
     /* The arguments of these are swallowed by the lexer, which leaves us the
        parenthesis that closes the command. define-sort is the one of them
        STP partially implements: a nullary alias for a floating-point sort
        is registered from the swallowed text; every other shape -- other
        sorts, parameters -- is answered "unsupported". */
     DEFINE_SORT_TOK
    {
      if (tryRegisterFpSortAlias(stp::smt2_skipped_text()))
        stp::GlobalParserInterface->success();
      else
        stp::GlobalParserInterface->unsupported();
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
     PUSH_TOK NUMERAL_TOK
    {
        for (unsigned i=0; i < $2;i++)
            stp::GlobalParserInterface->push();
        stp::GlobalParserInterface->success();
    }
|
     POP_TOK NUMERAL_TOK
    {
        for (unsigned i=0; i < $2;i++)
            stp::GlobalParserInterface->pop();
        stp::GlobalParserInterface->success();
    }
|
     RESET_TOK
    {
       stp::GlobalParserInterface->reset();
       // reset clears the logic, and with it the floating-point keywords.
       stp::SMT2SetFloatTokens(false);
       stp::GlobalParserInterface->success();
    }
|
     LOGIC_TOK STRING_TOK
    {
      const bool fp_logic =
            0 == strcmp($2->c_str(),"QF_FP") ||
            0 == strcmp($2->c_str(),"QF_BVFP") ||
            0 == strcmp($2->c_str(),"QF_ABVFP");
      if (!(
            0 == strcmp($2->c_str(),"QF_BV") ||
            0 == strcmp($2->c_str(),"QF_ABV") ||
            0 == strcmp($2->c_str(),"QF_AUFBV") ||
            fp_logic
            )) {
        yyerror("Wrong input logic");
      }
      // Fail a well-formed floating-point benchmark on its set-logic line,
      // not at its first declaration.
      if (fp_logic) {
        checkFpSupported();
      }
      // The floating-point keywords exist only inside the FP logics;
      // everywhere else names like "fp" or "NaN" stay ordinary symbols,
      // exactly as before floating-point support existed.
      stp::SMT2SetFloatTokens(fp_logic);
      stp::GlobalParserInterface->success();
      delete $2;
    }
|
     NOTES_TOK attribute STRING_TOK
    {
      delete $3;
      stp::GlobalParserInterface->success();
    }
|
     NOTES_TOK attribute DECIMAL_TOK
    {
      stp::GlobalParserInterface->success();
    }
|
     NOTES_TOK attribute NUMERAL_TOK
    {
      stp::GlobalParserInterface->success();
    }
|
     NOTES_TOK attribute
    {
      stp::GlobalParserInterface->success();
    }

;

function_param:
LPAREN_TOK STRING_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK RPAREN_TOK
{
  $$ = new ASTNode(stp::GlobalParserInterface->LookupOrCreateSymbol($2->c_str()));
  stp::GlobalParserInterface->addSymbol(*$$);
  $$->SetIndexWidth(0);
  $$->SetValueWidth($6);
  delete $2;
}
|
LPAREN_TOK STRING_TOK an_fp_sort RPAREN_TOK
{
  $$ = new ASTNode(stp::GlobalParserInterface->LookupOrCreateSymbol($2->c_str()));
  stp::GlobalParserInterface->addSymbol(*$$);
  $$->SetExpWidth($3->exp_bits);
  $$->SetSigWidth($3->sig_bits);
  $$->SetIndexWidth(0);
  $$->SetValueWidth($3->exp_bits + $3->sig_bits);
  delete $2;
  delete $3;
}
|
LPAREN_TOK STRING_TOK ROUNDINGMODE_TOK RPAREN_TOK
{
  // Not implemented: applyFunction substitutes bitvector and float
  // parameters only. Named here so the failure is this message rather
  // than a bare syntax error.
  fatal_yyerror("define-fun: RoundingMode parameters are not supported");
  $$ = NULL; // fatal_yyerror does not return
};
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


function_def:
STRING_TOK LPAREN_TOK function_params RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK  an_term
{
  checkBitVectorTerm(*$10);
  if ($10->GetValueWidth() != $8)
  {
    char msg [100];
    sprintf(msg, "Different bit-widths specified: %d %d", $10->GetValueWidth(), $8);
    yyerror(msg);
  }

  stp::GlobalParserInterface->storeFunction(*$1, *$3, *$10);

  // Next time the variable is used, we want it to be fresh.
  for (size_t i = 0; i < $3->size(); i++)
    stp::GlobalParserInterface->removeSymbol((*$3)[i]);

  delete $1;
  delete $3;
  stp::GlobalParserInterface->deleteNode($10);
}
|
STRING_TOK LPAREN_TOK function_params RPAREN_TOK BOOL_TOK an_formula
{
  stp::GlobalParserInterface->storeFunction(*$1, *$3, *$6);

  // Next time the variable is used, we want it to be fresh.
  for (size_t i = 0; i < $3->size(); i++)
   stp::GlobalParserInterface->removeSymbol((*$3)[i]);

  delete $1;
  delete $3;
  stp::GlobalParserInterface->deleteNode($6);
}
|
STRING_TOK LPAREN_TOK RPAREN_TOK BOOL_TOK an_formula
{
  ASTVec empty;
  stp::GlobalParserInterface->storeFunction(*$1, empty, *$5);

  delete $1;
  stp::GlobalParserInterface->deleteNode($5);
}
|
STRING_TOK LPAREN_TOK RPAREN_TOK ROUNDINGMODE_TOK an_term
{
  if ($5->GetType() != stp::BITVECTOR_TYPE || $5->GetValueWidth() != 5)
  {
    fatal_yyerror("define-fun: the body is not a rounding mode");
  }

  ASTVec empty;
  stp::GlobalParserInterface->storeFunction(*$1, empty, *$5);

  delete $1;
  stp::GlobalParserInterface->deleteNode($5);
}
|
STRING_TOK LPAREN_TOK RPAREN_TOK an_fp_sort an_term
{
  if ($5->GetExpWidth() != (unsigned)$4->exp_bits ||
      $5->GetSigWidth() != (unsigned)$4->sig_bits)
  {
    fatal_yyerror("define-fun: the body's floating-point format does not "
                  "match the declared result sort");
  }

  ASTVec empty;
  stp::GlobalParserInterface->storeFunction(*$1, empty, *$5);

  delete $1;
  delete $4;
  stp::GlobalParserInterface->deleteNode($5);
}
|
STRING_TOK LPAREN_TOK function_params RPAREN_TOK an_fp_sort an_term
{
  // This action was empty: the function was silently dropped, and -- worse --
  // its parameter symbols stayed interned, resolvable as free variables that
  // were never declared.
  if ($6->GetExpWidth() != (unsigned)$5->exp_bits ||
      $6->GetSigWidth() != (unsigned)$5->sig_bits)
  {
    fatal_yyerror("define-fun: the body's floating-point format does not "
                  "match the declared result sort");
  }

  stp::GlobalParserInterface->storeFunction(*$1, *$3, *$6);

  // Next time the variable is used, we want it to be fresh.
  for (size_t i = 0; i < $3->size(); i++)
    stp::GlobalParserInterface->removeSymbol((*$3)[i]);

  delete $1;
  delete $3;
  delete $5;
  stp::GlobalParserInterface->deleteNode($6);
}
|
STRING_TOK LPAREN_TOK RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK an_term
{
  checkBitVectorTerm(*$9);
  if ($9->GetValueWidth() != $7)
  {
    char msg [100];
    sprintf(msg, "Different bit-widths specified: %d %d", $9->GetValueWidth(), $7);
    yyerror(msg);
  }

  ASTVec empty;
  stp::GlobalParserInterface->storeFunction(*$1,empty, *$9);

  delete $1;
  stp::GlobalParserInterface->deleteNode($9);
}
|
STRING_TOK LPAREN_TOK function_params RPAREN_TOK an_array_sort an_term
{
  stp::GlobalParserInterface->unsupported();

  // Match the other parameterised productions: leaving the parameter
  // symbols interned would let later input resolve them as free variables
  // that were never declared.
  for (size_t i = 0; i < $3->size(); i++)
    stp::GlobalParserInterface->removeSymbol((*$3)[i]);

  delete $1;
  delete $3;
  delete $5;
  stp::GlobalParserInterface->deleteNode($6);
}
|
STRING_TOK LPAREN_TOK RPAREN_TOK an_array_sort an_term
{
  // A nullary define-fun whose result is an array. This is just a name for
  // its body, stored like any other nullary function -- accepted with or
  // without --array-equality; the lexer resolves later references to it
  // back to that body. A body whose widths disagree with the declared sort
  // is reported -- mirroring the sibling bitvector define-fun productions
  // -- and still stored, so parsing continues. The sorts that share one
  // bit layout (a float index or element format, RoundingMode on either
  // side) get their own check: the widths cannot tell them apart.
  if ($5->GetIndexWidth() != $4->index.width ||
      $5->GetValueWidth() != $4->elem.width)
  {
    char msg [100];
    snprintf(msg, sizeof(msg),
             "Different array widths specified: (%u %u) vs (%u %u)",
             $5->GetIndexWidth(), $5->GetValueWidth(), $4->index.width,
             $4->elem.width);
    yyerror(msg);
  }
  else if (!stp::GlobalParserInterface->arraySortsAgree(*$5, *$4))
  {
    yyerror("The body's array index or element sorts differ from the "
            "declared ones");
  }

  ASTVec empty;
  stp::GlobalParserInterface->storeFunction(*$1, empty, *$5);
  delete $1;
  delete $4;
  stp::GlobalParserInterface->deleteNode($5);
}
;


status:
STRING_TOK {

  std::transform($1->begin(), $1->end(), $1->begin(), ::tolower);
  if (0 == strcmp($1->c_str(), "sat"))
      stp::input_status = TO_BE_SATISFIABLE;
  else if (0 == strcmp($1->c_str(), "unsat"))
    stp::input_status = TO_BE_UNSATISFIABLE;
  else if (0 == strcmp($1->c_str(), "unknown"))
      stp::input_status = TO_BE_UNKNOWN;
  else
      yyerror($1->c_str());
  delete $1;
  $$ = NULL;
}
;

/* The argument of get-info. The standard flags all arrive as a colon followed
   by an identifier; the keywords that the lexer gives a token of their own are
   accepted too, since ⟨info_flag⟩ admits any ⟨keyword⟩. */
info_flag:
COLON_TOK STRING_TOK
{
  $$ = $2;
}
| SOURCE_TOK
{
  $$ = new std::string("source");
}
| CATEGORY_TOK
{
  $$ = new std::string("category");
}
| DIFFICULTY_TOK
{
  $$ = new std::string("difficulty");
}
| VERSION_TOK
{
  $$ = new std::string("smt-lib-version");
}
| STATUS_TOK
{
  $$ = new std::string("status");
}
| LICENSE_TOK
{
  $$ = new std::string("license");
}
;

attribute:
SOURCE_TOK
{}
| CATEGORY_TOK
{}
| DIFFICULTY_TOK
{}
| VERSION_TOK
{}
| STATUS_TOK status
{}
| LICENSE_TOK
{}
| /* set-info accepts any keyword, not just the handful the lexer gives a
     token of its own. Benchmarks carry things like :notes freely. */
  COLON_TOK STRING_TOK
{
  delete $2;
}
;

an_fp_sort:
  // float_size is (exponent bits, significand bits), where the significand
  // includes the hidden bit -- the same (eb, sb) that (_ FloatingPoint eb sb)
  // uses. The named sorts had their widths set by naively splitting the total
  // in two (4+12, 16+48, 32+96) instead of using the IEEE fields, so every
  // one but Float32 named the wrong format.
  FLOAT16_TOK
{
    checkFpSupported();
    $$ = new stp::float_size(5, 11);
}
| FLOAT32_TOK
{
    checkFpSupported();
    $$ = new stp::float_size(8, 24);
}
| FLOAT64_TOK
{
    checkFpSupported();
    $$ = new stp::float_size(11, 53);
}
| FLOAT128_TOK
{
    checkFpSupported();
    $$ = new stp::float_size(15, 113);
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

an_array_sort_component:
  // An index or element sort of an (Array X Y) sort: a bitvector, a
  // floating-point sort, or RoundingMode. Widths are positive by
  // construction, so the array declarations need no further checks.
  LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK
{
  if ($4 == 0)
    fatal_yyerror("BITVECTORS must be of positive length");
  $$ = new stp::array_sort_component{stp::array_sort_component::BITVECTOR,
                                     $4, 0, 0};
}
| an_fp_sort
{
  $$ = new stp::array_sort_component{
      stp::array_sort_component::FLOATINGPOINT,
      (unsigned)($1->exp_bits + $1->sig_bits), (unsigned)$1->exp_bits,
      (unsigned)$1->sig_bits};
  delete $1;
}
| ROUNDINGMODE_TOK
{
  // Carried as a 5-bit one-hot bitvector, like every rounding mode.
  $$ = new stp::array_sort_component{stp::array_sort_component::ROUNDINGMODE,
                                     5, 0, 0};
}
;

an_array_sort:
LPAREN_TOK ARRAY_TOK an_array_sort_component an_array_sort_component RPAREN_TOK
{
  $$ = new stp::array_sort{*$3, *$4};
  delete $3;
  delete $4;
}
;


var_decl:
STRING_TOK LPAREN_TOK RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK
{
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  stp::GlobalParserInterface->addSymbol(s);
  //Sort_symbs has the indexwidth/valuewidth. Set those fields in
  //var
  s.SetIndexWidth(0);
  s.SetValueWidth($7);
  delete $1;
}
| STRING_TOK LPAREN_TOK RPAREN_TOK STRING_TOK
{
  // The sort position holds a bare name: a define-sort alias. (This used to
  // match any TERM symbol, so `(declare-fun y () x)` with x a variable
  // "worked" as an alias use.)
  unsigned eb, sb;
  if (!stp::GlobalParserInterface->lookupSortAlias(*$4, eb, sb))
  {
    fatal_yyerror("unknown sort (not built in, and not a define-sort alias)");
  }
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  stp::GlobalParserInterface->addSymbol(s);
  s.SetExpWidth(eb);
  s.SetSigWidth(sb);
  s.SetIndexWidth(0);
  s.SetValueWidth(eb + sb);
  delete $1;
  delete $4;
}
| STRING_TOK LPAREN_TOK RPAREN_TOK BOOL_TOK
{
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  s.SetIndexWidth(0);
  s.SetValueWidth(0);
  stp::GlobalParserInterface->addSymbol(s);
  delete $1;
}
| STRING_TOK LPAREN_TOK RPAREN_TOK an_array_sort
{
  // An array over any pairing of bitvector, floating-point and RoundingMode
  // index/element sorts. A float element's format lives on the array node
  // -- a read off it inherits the format (see deriveFPFormat) -- while a
  // float index format and the RoundingMode sorts land in the manager's
  // registries (see addArraySymbol). Either way the widths lay the array
  // out exactly like an array of bitvectors.
  declareArraySymbol($1, $4);
}
| STRING_TOK LPAREN_TOK RPAREN_TOK an_fp_sort
{
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  stp::GlobalParserInterface->addSymbol(s);
  s.SetExpWidth($4->exp_bits);
  s.SetSigWidth($4->sig_bits);
  s.SetIndexWidth(0);
  s.SetValueWidth($4->exp_bits + $4->sig_bits);
  delete $1;
  delete $4;
}
| STRING_TOK LPAREN_TOK RPAREN_TOK ROUNDINGMODE_TOK
{
  // A rounding mode is carried as a 5-bit one-hot bitvector, so a variable of
  // that sort is a 5-bit symbol. Declaring it as anything else -- or, as
  // before, not declaring it at all -- leaves every use of the name
  // unresolved, and the lexer hands it back as a bare string.
  // addRoundingModeSymbol also pins the symbol to the five legal encodings,
  // without which the sort would have 32 values instead of 5.
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  s.SetIndexWidth(0);
  s.SetValueWidth(5);
  stp::GlobalParserInterface->addRoundingModeSymbol(s);
  delete $1;
}
;


const_decl:
STRING_TOK  LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK
{
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  stp::GlobalParserInterface->addSymbol(s);
  //Sort_symbs has the indexwidth/valuewidth. Set those fields in
  //var
  s.SetIndexWidth(0);
  s.SetValueWidth($5);
  delete $1;
}
| STRING_TOK BOOL_TOK
{
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  s.SetIndexWidth(0);
  s.SetValueWidth(0);
  stp::GlobalParserInterface->addSymbol(s);
  delete $1;
}
| STRING_TOK an_array_sort
{
  // declare-const of an array: same surface as declare-fun's, including
  // float and RoundingMode index/element sorts (the float-element form
  // used to exist only for declare-fun).
  declareArraySymbol($1, $2);
}
| STRING_TOK an_fp_sort
{
  // The format must land on the symbol, or it types as a Boolean and every
  // use of the name is a syntax error (this branch used to forget it while
  // declare-fun's twin set it).
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  s.SetExpWidth($2->exp_bits);
  s.SetSigWidth($2->sig_bits);
  s.SetIndexWidth(0);
  s.SetValueWidth($2->exp_bits + $2->sig_bits);
  stp::GlobalParserInterface->addSymbol(s);
  delete $1;
  delete $2;
}
| STRING_TOK STRING_TOK
{
  // declare-const with a define-sort alias in sort position.
  unsigned eb, sb;
  if (!stp::GlobalParserInterface->lookupSortAlias(*$2, eb, sb))
  {
    fatal_yyerror("unknown sort (not built in, and not a define-sort alias)");
  }
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  s.SetExpWidth(eb);
  s.SetSigWidth(sb);
  s.SetIndexWidth(0);
  s.SetValueWidth(eb + sb);
  stp::GlobalParserInterface->addSymbol(s);
  delete $1;
  delete $2;
}
| STRING_TOK ROUNDINGMODE_TOK
{
  // As above: 5 bits, not 0 (a zero-width symbol would be a Boolean), and
  // pinned to the five legal encodings.
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  s.SetIndexWidth(0);
  s.SetValueWidth(5);
  stp::GlobalParserInterface->addRoundingModeSymbol(s);
  delete $1;
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

an_formula:
TRUE_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(TRUE));
  assert(0 == $$->GetIndexWidth());
  assert(0 == $$->GetValueWidth());
}
| FALSE_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(FALSE));
  assert(0 == $$->GetIndexWidth());
  assert(0 == $$->GetValueWidth());
}
|
FORMID_TOK
{
  $$ = stp::GlobalParserInterface->newNode(*$1); //todo creating then deleting same?
  stp::GlobalParserInterface->deleteNode($1);
}
| LPAREN_TOK an_fp_predicate RPAREN_TOK
{
   $$ = $2;
}
| LPAREN_TOK EQ_TOK an_terms RPAREN_TOK
{
  const ASTVec& terms = *$3;

  // Reject an ill-sorted = up front. The simplifying factory folds constant
  // operands before any type check can see them, so a width mismatch here
  // would otherwise be "solved" (to false) rather than diagnosed.
  for (unsigned i = 1; i < terms.size();i++)
  {
    if (terms[i].GetType() != terms[0].GetType() ||
        terms[i].GetValueWidth() != terms[0].GetValueWidth() ||
        terms[i].GetIndexWidth() != terms[0].GetIndexWidth())
    {
      fatal_yyerror("= requires operands of the same sort");
    }
    if (terms[i].GetType() == FLOATINGPOINT_TYPE &&
        (terms[i].GetExpWidth() != terms[0].GetExpWidth() ||
         terms[i].GetSigWidth() != terms[0].GetSigWidth()))
    {
      fatal_yyerror("= requires floating-point operands of the same format");
    }
  }

  bool one_float = false;
  for (unsigned i = 0; i < terms.size();i++)
  {
    one_float |= (terms[i].GetType() == FLOATINGPOINT_TYPE);
  }

  Kind k = one_float ? FP_SMT_EQ : EQ;

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
    delete $3;
  }
  else
  {
    fatal_yyerror("too few arguments to eq."); 
  }
}
| LPAREN_TOK DISTINCT_TOK an_terms RPAREN_TOK
{
  using namespace stp;

  ASTVec terms = *$3;
  ASTVec forms;

  for (size_t i = 1; i < terms.size(); i++)
  {
    if (terms[i].GetType() != terms[0].GetType() ||
        terms[i].GetIndexWidth() != terms[0].GetIndexWidth() ||
        terms[i].GetValueWidth() != terms[0].GetValueWidth())
      fatal_yyerror("distinct requires operands of the same sort");
    if (terms[i].GetType() == FLOATINGPOINT_TYPE &&
        (terms[i].GetExpWidth() != terms[0].GetExpWidth() ||
         terms[i].GetSigWidth() != terms[0].GetSigWidth()))
      fatal_yyerror("distinct requires floating-point operands of the same format");
  }

  for(ASTVec::const_iterator it=terms.begin(),itend=terms.end();
      it!=itend; it++)
  {
    for(ASTVec::const_iterator it2=it+1; it2!=itend; it2++) {
      // Equality of floats is FP_SMT_EQ, not the generic EQ -- the same
      // distinction the (= ...) rule makes. Building plain EQ over float
      // operands produces a node the later passes reject as a non-formula.
      const Kind eqk =
        ((*it).GetType() == FLOATINGPOINT_TYPE) ? FP_SMT_EQ : EQ;
      ASTNode n =
        stp::GlobalParserInterface->nf->CreateNode(NOT, stp::GlobalParserInterface->CreateNode(eqk, *it, *it2));

      forms.push_back(n);
    }
  }

  if(forms.size() == 0)
    fatal_yyerror("empty distinct");

  $$ = (forms.size() == 1) ?
    stp::GlobalParserInterface->newNode(forms[0]) :
    stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(AND, forms));

  delete $3;
}
| LPAREN_TOK DISTINCT_TOK an_formulas RPAREN_TOK
{
  using namespace stp;

  ASTVec terms = *$3;
  ASTVec forms;

  for (size_t i = 1; i < terms.size(); i++)
  {
    if (terms[i].GetType() != terms[0].GetType() ||
        terms[i].GetIndexWidth() != terms[0].GetIndexWidth() ||
        terms[i].GetValueWidth() != terms[0].GetValueWidth())
      fatal_yyerror("distinct requires operands of the same sort");
    if (terms[i].GetType() == FLOATINGPOINT_TYPE &&
        (terms[i].GetExpWidth() != terms[0].GetExpWidth() ||
         terms[i].GetSigWidth() != terms[0].GetSigWidth()))
      fatal_yyerror("distinct requires floating-point operands of the same format");
  }

  for(ASTVec::const_iterator it=terms.begin(),itend=terms.end();
      it!=itend; it++) {
    for(ASTVec::const_iterator it2=it+1; it2!=itend; it2++) {
      // Floats reach this (an_formulas) distinct rule too, since a
      // floating-point function-id reduces as a formula. Their equality is
      // FP_SMT_EQ, not IFF, which only holds between Booleans.
      const Kind eqk =
        ((*it).GetType() == FLOATINGPOINT_TYPE) ? FP_SMT_EQ : IFF;
      ASTNode n = (stp::GlobalParserInterface->nf->CreateNode(NOT, stp::GlobalParserInterface->CreateNode(eqk, *it, *it2)));
      forms.push_back(n);
    }
  }

  if(forms.size() == 0)
    fatal_yyerror("empty distinct");

  $$ = (forms.size() == 1) ?
    stp::GlobalParserInterface->newNode(forms[0]) :
    stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(AND, forms));

  delete $3;
}
| LPAREN_TOK BVSLT_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSLT, $3, $4);
}
| LPAREN_TOK BVSLE_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSLE, $3, $4);
}
| LPAREN_TOK BVSGT_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSGT, $3, $4);
}
| LPAREN_TOK BVSGE_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSGE, $3, $4);
}
| LPAREN_TOK BVLT_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVLT, $3, $4);
}
| LPAREN_TOK BVLE_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVLE, $3, $4);
}
| LPAREN_TOK BVGT_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVGT, $3, $4);
}
| LPAREN_TOK BVGE_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVGE, $3, $4);
}
| LPAREN_TOK BVUADDO_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVUADDO, $3, $4);
}
| LPAREN_TOK BVSADDO_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSADDO, $3, $4);
}
| LPAREN_TOK BVUMULO_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVUMULO, $3, $4);
}
| LPAREN_TOK BVSMULO_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSMULO, $3, $4);
}
| LPAREN_TOK BVUSUBO_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVUSUBO, $3, $4);
}
| LPAREN_TOK BVSSUBO_TOK an_term an_term RPAREN_TOK
{
  $$ = createNode(BVSSUBO, $3, $4);
}
| LPAREN_TOK BVSDIVO_TOK an_term an_term RPAREN_TOK
{
  $$ = createSDivOverflow($3, $4);
}
| LPAREN_TOK BVNEGO_TOK an_term RPAREN_TOK
{
  $$ = createNegOverflow($3);
}
| LPAREN_TOK an_formula RPAREN_TOK
{
  $$ = $2;
}
| LPAREN_TOK NOT_TOK an_formula RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateNode(NOT, *$3));
  stp::GlobalParserInterface->deleteNode( $3);
}
| LPAREN_TOK IMPLIES_TOK an_formulas RPAREN_TOK
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
  delete $3;
}
| LPAREN_TOK ITE_TOK an_formula an_formula an_formula RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateNode(ITE, *$3, *$4, *$5));
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
  stp::GlobalParserInterface->deleteNode( $5);
}
| LPAREN_TOK AND_TOK an_formulas RPAREN_TOK
{
 $$ = createNode(AND, $3);
}
| LPAREN_TOK OR_TOK an_formulas RPAREN_TOK
{
  $$ = createNode(OR, $3);
}
| LPAREN_TOK XOR_TOK an_formulas RPAREN_TOK
{
  $$ = createNode(XOR, $3);
}
| LPAREN_TOK EQ_TOK an_formulas RPAREN_TOK
{
  const ASTVec& forms = *$3;

  // As with = over terms: catch mismatched operands before the factory can
  // fold them. A float can reach this rule too (parenthesised fp terms parse
  // as formulas), in which case its width differs from a Boolean's zero.
  for (unsigned i = 1; i < forms.size();i++)
  {
    if (forms[i].GetType() != forms[0].GetType() ||
        forms[i].GetValueWidth() != forms[0].GetValueWidth() ||
        forms[i].GetIndexWidth() != forms[0].GetIndexWidth())
    {
      fatal_yyerror("= requires operands of the same sort");
    }
    if (forms[i].GetType() == FLOATINGPOINT_TYPE &&
        (forms[i].GetExpWidth() != forms[0].GetExpWidth() ||
         forms[i].GetSigWidth() != forms[0].GetSigWidth()))
    {
      fatal_yyerror("= requires floating-point operands of the same format");
    }
  }

  bool one_float = false;
  for (unsigned i = 0; i < forms.size();i++)
  {
    one_float |= (forms[i].GetType() == FLOATINGPOINT_TYPE);
  }

  Kind k = one_float ? FP_SMT_EQ : IFF;

  if (forms.size() ==2)
  {
    $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(k, forms));
    delete $3;
  }
  else  if (forms.size() >2) 
  {
    ASTVec result;
    result.reserve(forms.size()-1);
    for (unsigned i =1; i < forms.size();i++)
    {
        result.push_back(stp::GlobalParserInterface->CreateNode(k, forms[i], forms[i-1]));
    }
    $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(AND, result));
    delete $3;
  }
  else
  {
    fatal_yyerror("too few arguments to formula eq."); 
  }
}
| LPAREN_TOK LET_TOK lets an_formula RPAREN_TOK
  {
    $$ = $4;
    stp::GlobalParserInterface->letMgr->pop();
  }
| LPAREN_TOK BOOLEAN_FUNCTIONID_TOK an_mixed RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->applyFunction(*$2,*$3));
  delete $2;
  delete $3;
}
| BOOLEAN_FUNCTIONID_TOK
{
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->applyFunction(*$1,empty));
  delete $1;
}
| LPAREN_TOK EXCLAIMATION_MARK_TOK an_formula NAMED_ATTRIBUTE_TOK STRING_TOK RPAREN_TOK
{
  /*
    This implements (! <an_formula> :named foo)
    "foo" is created as a symbol that can be refered to by later commands.
  */

  // TODO, will fail if name is already defined?
  ASTNode s(stp::GlobalParserInterface->LookupOrCreateSymbol($5->c_str()));
  s.SetIndexWidth($3->GetIndexWidth());
  s.SetValueWidth($3->GetValueWidth());

  stp::GlobalParserInterface->addSymbol(s);

  ASTNode n = stp::GlobalParserInterface->CreateNode(IFF,s, *$3);

  stp::GlobalParserInterface->AddAssert(n);

  delete $5;

  $$ = $3;
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
  an_mixed RPAREN_TOK
{
  stp::GlobalParserInterface->letMgr->LetExprMgr(*$3,($5->back()));
  delete $3;
  delete $5;
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
  delete $1;
}
| BVCONST_BINARY_TOK
{
  unsigned width = $1->length();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst(*$1, 2, width));
  $$->SetValueWidth(width);
  delete $1;
}
| FP_TOK an_term an_term an_term
{
  $$ = createFPFromParts($2, $3, $4);
};

an_rounding_mode:
  FP_RM_ROUNDTOWARDZERO_TOK
{
  int width = 5;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst(width, ROUND_TOWARD_ZERO));
}
| FP_RM_ROUNDNEARESTTIESTOEVEN_TOK
{
  int width = 5;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst(width, ROUND_NEAREST_TIES_TO_EVEN));
}
| FP_RM_ROUNDNEARESTTIESTOAWAY_TOK
{
  int width = 5;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst(width, ROUND_NEAREST_TIES_TO_AWAY));
}
| FP_RM_ROUNDTOWARDPOSITIVE_TOK
{
  int width = 5;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst(width, ROUND_TOWARD_POSITIVE));
}
| FP_RM_ROUNDTOWARDNEGATIVE_TOK
{
  int width = 5;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst(width, ROUND_TOWARD_NEGATIVE));
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
  LPAREN_TOK FP_ABS_TOK an_term RPAREN_TOK
{
  $$ = createFPUnary(FP_ABS, $3);
}
| LPAREN_TOK FP_NEG_TOK an_term RPAREN_TOK
{
  $$ = createFPUnary(FP_NEG, $3);
}
| LPAREN_TOK FP_ADD_TOK an_term an_term an_term RPAREN_TOK
{
  $$ = createFPArith(FP_ADD, $3, $4, $5);
}
| LPAREN_TOK FP_SUB_TOK an_term an_term an_term RPAREN_TOK
{
  $$ = createFPArith(FP_SUB, $3, $4, $5);
}
| LPAREN_TOK FP_MUL_TOK an_term an_term an_term RPAREN_TOK
{
  $$ = createFPArith(FP_MUL, $3, $4, $5);
}
| LPAREN_TOK FP_DIV_TOK an_term an_term an_term RPAREN_TOK
{
  $$ = createFPArith(FP_DIV, $3, $4, $5);
}
| LPAREN_TOK FP_FMA_TOK an_term an_term an_term an_term RPAREN_TOK
{
  $$ = createFPFma($3, $4, $5, $6);
}
| LPAREN_TOK FP_SQRT_TOK an_term an_term RPAREN_TOK
{
  $$ = createFPSqrt($3, $4);
}
| LPAREN_TOK FP_REM_TOK an_term an_term RPAREN_TOK
{
  $$ = createFPBinary(FP_REM, $3, $4);
}
| LPAREN_TOK FP_ROUNDTOINTEGRAL_TOK an_term an_term RPAREN_TOK
{
  $$ = createFPRoundToIntegral($3, $4);
}
| LPAREN_TOK FP_MIN_TOK an_term an_term RPAREN_TOK
{
  $$ = createFPBinary(FP_MIN, $3, $4);
}
| LPAREN_TOK FP_MAX_TOK an_term an_term RPAREN_TOK
{
  $$ = createFPBinary(FP_MAX, $3, $4);
}
| LPAREN_TOK LPAREN_TOK UNDERSCORE_TOK FP_TO_UBV_TOK NUMERAL_TOK RPAREN_TOK an_term an_term RPAREN_TOK
{
  $$ = createFPToBV(FP_TO_UBV, $5, $7, $8);
}
| LPAREN_TOK LPAREN_TOK UNDERSCORE_TOK FP_TO_SBV_TOK NUMERAL_TOK RPAREN_TOK an_term an_term RPAREN_TOK
{
  $$ = createFPToBV(FP_TO_SBV, $5, $7, $8);
}
| LPAREN_TOK LPAREN_TOK UNDERSCORE_TOK FP_TOFP_TOK NUMERAL_TOK NUMERAL_TOK RPAREN_TOK an_term RPAREN_TOK
{
  // ((_ to_fp e s) bv) reinterprets the bits of a bitvector as an IEEE-754
  // float. STP already stores floats as their packed bit pattern, so this is
  // purely a retyping: keep the child and stamp the format onto it.
  $$ = createFPFromBits($5, $6, $8);
}
| LPAREN_TOK LPAREN_TOK UNDERSCORE_TOK FP_TOFP_TOK NUMERAL_TOK NUMERAL_TOK RPAREN_TOK an_term an_term RPAREN_TOK
{
  // ((_ to_fp e s) rm f) reformats an existing float under a rounding mode.
  $$ = createFPToFP($5, $6, $8, $9);
}
| LPAREN_TOK LPAREN_TOK UNDERSCORE_TOK FP_TOFP_UNSIGNED_TOK NUMERAL_TOK NUMERAL_TOK RPAREN_TOK an_term an_term RPAREN_TOK
{
  $$ = createFPFromUnsignedBV($5, $6, $8, $9);
}
| LPAREN_TOK LPAREN_TOK UNDERSCORE_TOK FP_TOFP_TOK NUMERAL_TOK NUMERAL_TOK RPAREN_TOK an_term DECIMAL_TOK RPAREN_TOK
{
  // ((_ to_fp e s) rm 1.5): conversion from a real literal. Deliberately
  // unsupported -- no QF_FP/QF_BVFP/QF_ABVFP benchmark uses it -- but say
  // so, rather than a bare syntax error at the literal.
  fatal_yyerror("real literals are not supported (STP's floating point is "
                "bit-precise); write the value as its packed bits, e.g. "
                "((_ to_fp 8 24) #x3fc00000) for 1.5, or as a "
                "(fp sign exponent significand) literal");
}
| LPAREN_TOK LPAREN_TOK UNDERSCORE_TOK FP_TOFP_TOK NUMERAL_TOK NUMERAL_TOK RPAREN_TOK DECIMAL_TOK RPAREN_TOK
{
  fatal_yyerror("real literals are not supported (STP's floating point is "
                "bit-precise); write the value as its packed bits, e.g. "
                "((_ to_fp 8 24) #x3fc00000) for 1.5, or as a "
                "(fp sign exponent significand) literal");
}
| LPAREN_TOK FP_TO_REAL_TOK an_term RPAREN_TOK
{
  fatal_yyerror("fp.to_real is not supported: STP has no theory of reals");
}
| UNDERSCORE_TOK an_fp_const NUMERAL_TOK NUMERAL_TOK
{
  // The special values are constants: build the packed interned constant
  // directly. A childless special-value node would hash-cons every format
  // of, say, NaN to one node, which whoever parsed last would re-stamp.
  uint32_t exp_width($3);
  uint32_t sig_width($4);
  checkFpFormatWidths(exp_width, sig_width);
  $$ = stp::GlobalParserInterface->newNode(
      stp::GlobalParserInterface->CreateFPSpecialConst(
          (stp::FPSpecial)$2, exp_width, sig_width));
}
;

// The Boolean-valued floating-point operations. Split from an_fp_term so
// that formula position derives exactly these (parenthesised by
// an_formula's rule) and term position derives exactly the float-valued
// ones -- the shared nonterminal used to make every fp expression reachable
// from both, which is where most of the grammar's reduce/reduce conflicts
// came from.
an_fp_predicate:
  FP_LEQ_TOK an_terms
{
  $$ = createFPChain(FP_LEQ, $2, "fp.leq");
}
| FP_LT_TOK an_terms
{
  $$ = createFPChain(FP_LT, $2, "fp.lt");
}
| FP_GEQ_TOK an_terms
{
  $$ = createFPChain(FP_GEQ, $2, "fp.geq");
}
| FP_GT_TOK an_terms
{
  $$ = createFPChain(FP_GT, $2, "fp.gt");
}
| FP_EQ_TOK an_terms
{
  // Through the same helper as the other chainable comparisons, gaining its
  // operand and format checks (the old inline version had none).
  $$ = createFPChain(FP_EQ, $2, "fp.eq");
}
| FP_ISNORMAL_TOK an_term
{
  $$ = createFPPredicate(FP_ISNORMAL, $2);
}
| FP_ISSUBNORMAL_TOK an_term
{
  $$ = createFPPredicate(FP_ISSUBNORMAL, $2);
}
| FP_ISZERO_TOK an_term
{
  $$ = createFPPredicate(FP_ISZERO, $2);
}
| FP_ISINFINITE_TOK an_term
{
  $$ = createFPPredicate(FP_ISINFINITE, $2);
}
| FP_ISNAN_TOK an_term
{
  $$ = createFPPredicate(FP_ISNAN, $2);
}
| FP_ISNEGATIVE_TOK an_term
{
  $$ = createFPPredicate(FP_ISNEGATIVE, $2);
}
| FP_ISPOSITIVE_TOK an_term
{
  $$ = createFPPredicate(FP_ISPOSITIVE, $2);
}
;

an_term:
TERMID_TOK
{
  $$ = stp::GlobalParserInterface->newNode((*$1));
  stp::GlobalParserInterface->deleteNode( $1);
}
| ARRAY_FUNCTIONID_TOK
{
  // A use of a nullary array-sorted define-fun expands to its body.
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->applyFunction(*$1,empty));
  delete $1;
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
| SELECT_TOK an_term an_term
{
  //ARRAY READ
  // valuewidth is same as array, indexwidth is 0.
  ASTNode array = *$2;
  ASTNode index = *$3;
  unsigned int width = array.GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(READ, width, array, index));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
| STORE_TOK an_term an_term an_term
{
  //ARRAY WRITE
  unsigned int width = $4->GetValueWidth();
  ASTNode array = *$2;
  ASTNode index = *$3;
  ASTNode writeval = *$4;
  ASTNode write_term = stp::GlobalParserInterface->nf->CreateArrayTerm(WRITE,$2->GetIndexWidth(),width,array,index,writeval);
  $$ = stp::GlobalParserInterface->newNode(write_term);
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK UNDERSCORE_TOK BVEXTRACT_TOK  NUMERAL_TOK  NUMERAL_TOK RPAREN_TOK an_term
{
  checkBitVectorTerm(*$7);
  int width = $4 - $5 + 1;
  if (width < 0)
    yyerror("Negative width in extract");

  if((unsigned)$4 >= $7->GetValueWidth())
    yyerror("Parsing: Wrong width in BVEXTRACT\n");

  ASTNode hi  =  stp::GlobalParserInterface->CreateBVConst(32, $4);
  ASTNode low =  stp::GlobalParserInterface->CreateBVConst(32, $5);
  ASTNode output = stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT, width, *$7,hi,low);
  ASTNode * n = stp::GlobalParserInterface->newNode(output);
  $$ = n;
    stp::GlobalParserInterface->deleteNode( $7);
}
| LPAREN_TOK UNDERSCORE_TOK BVZX_TOK  NUMERAL_TOK  RPAREN_TOK an_term
{
  checkBitVectorTerm(*$6);
  unsigned w = $6->GetValueWidth() + $4;
  ASTNode width = stp::GlobalParserInterface->CreateBVConst(32,w);
  $$ =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVZX,w,*$6,width));
  stp::GlobalParserInterface->deleteNode( $6);
}
|  LPAREN_TOK UNDERSCORE_TOK BVSX_TOK  NUMERAL_TOK  RPAREN_TOK an_term
{
  checkBitVectorTerm(*$6);
  unsigned w = $6->GetValueWidth() + $4;
  ASTNode width = stp::GlobalParserInterface->CreateBVConst(32,w);
  $$ =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVSX,w,*$6,width));
  stp::GlobalParserInterface->deleteNode( $6);
}

|  ITE_TOK an_formula an_term an_term
{
  // Reject branches of different floating-point formats up front, as the
  // (= ...) rule does for its operands: with a constant condition the
  // factory folds the if-then-else to one branch before any type check can
  // see the pair, and two formats can share one packed width -- (8, 24)
  // and (24, 8) are both 32 bits -- so the width checks cannot tell them
  // apart. (BVTypeCheck's ITE case backs this up for a symbolic
  // condition.) Packed bits are an internal representation, not a public
  // coercion: a float branch and a BitVec branch are different sorts.
  if ($3->GetType() != $4->GetType())
  {
    fatal_yyerror("ite branches must have the same sort");
  }
  if ($3->GetType() == FLOATINGPOINT_TYPE &&
      ($3->GetExpWidth() != $4->GetExpWidth() ||
       $3->GetSigWidth() != $4->GetSigWidth()))
  {
    fatal_yyerror("ite branches differ in floating-point format");
  }
  const unsigned int width = $3->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateArrayTerm(ITE,$4->GetIndexWidth(), width,*$2, *$3, *$4));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
|  BVCONCAT_TOK an_term an_term
{
  checkBitVectorTerm(*$2);
  checkBitVectorTerm(*$3);
  const unsigned int width = $2->GetValueWidth() + $3->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVCONCAT, width, *$2, *$3));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVNOT_TOK an_term
{
  checkBitVectorTerm(*$2);
  //this is the BVNEG (term) in the CVCL language
  unsigned int width = $2->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, *$2));
  stp::GlobalParserInterface->deleteNode( $2);
}
|  BVNEG_TOK an_term
{
  checkBitVectorTerm(*$2);
  //this is the BVUMINUS term in CVCL langauge
  unsigned width = $2->GetValueWidth();
  $$ =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVUMINUS,width,*$2));
  stp::GlobalParserInterface->deleteNode( $2);
}
|  LPAREN_TOK BVAND_TOK an_terms RPAREN_TOK
{
 $$ = createTerm(BVAND, $3);
}
|  LPAREN_TOK BVOR_TOK an_terms RPAREN_TOK
{
  $$ = createTerm(BVOR, $3);
}
|  LPAREN_TOK BVXOR_TOK an_terms RPAREN_TOK
{
  $$ = createTerm(BVXOR, $3);
}
| LPAREN_TOK BVXNOR_TOK an_term an_term RPAREN_TOK
{
  ASTNode *temp = createTerm(BVXOR, $3, $4);
  const unsigned int width = temp->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, *temp));
  stp::GlobalParserInterface->deleteNode( temp);
}
|  BVCOMP_TOK an_term an_term
{
  checkBitVectorTerm(*$2);
  checkBitVectorTerm(*$3);
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(ITE, 1,
  stp::GlobalParserInterface->nf->CreateNode(EQ, *$2, *$3),
  stp::GlobalParserInterface->CreateOneConst(1),
  stp::GlobalParserInterface->CreateZeroConst(1)));

  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVSUB_TOK an_term an_term
{
  $$ = createTerm(BVSUB, $2, $3);
}
|  LPAREN_TOK BVPLUS_TOK an_terms RPAREN_TOK
{
  $$ = createTerm(BVPLUS, $3);
}
|  LPAREN_TOK BVMULT_TOK an_terms RPAREN_TOK
{
  $$ = createTerm(BVMULT, $3);
}
|      BVDIV_TOK an_term an_term
{
  $$ = createTerm(BVDIV, $2, $3);
}
|      BVMOD_TOK an_term an_term
{
  $$ = createTerm(BVMOD, $2, $3);
}
|      SBVDIV_TOK an_term an_term
{
  $$ = createTerm(SBVDIV, $2, $3);
}
|      SBVREM_TOK an_term an_term
{
  $$ = createTerm(SBVREM, $2, $3);
}
|      SBVMOD_TOK an_term an_term
{
  $$ = createTerm(SBVMOD, $2, $3);
}
|  BVNAND_TOK an_term an_term
{
  checkBitVectorTerm(*$2);
  checkBitVectorTerm(*$3);
  unsigned int width = $2->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, stp::GlobalParserInterface->nf->CreateTerm(BVAND, width, *$2, *$3)));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVNOR_TOK an_term an_term
{
  checkBitVectorTerm(*$2);
  checkBitVectorTerm(*$3);
  unsigned int width = $2->GetValueWidth();
  $$= stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, stp::GlobalParserInterface->nf->CreateTerm(BVOR, width, *$2, *$3)));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVLEFTSHIFT_1_TOK an_term an_term
{
   $$ = createTerm(BVLEFTSHIFT, $2, $3);
}
| BVRIGHTSHIFT_1_TOK an_term an_term
{
   $$ = createTerm(BVRIGHTSHIFT, $2, $3);
}
|  BVARITHRIGHTSHIFT_TOK an_term an_term
{
   $$ = createTerm(BVSRSHIFT, $2, $3);
}
| LPAREN_TOK UNDERSCORE_TOK BVROTATE_LEFT_TOK  NUMERAL_TOK  RPAREN_TOK an_term
{
  checkBitVectorTerm(*$6);
  ASTNode *n;
  unsigned width = $6->GetValueWidth();
  unsigned rotate = $4 % width;
  if (0 == rotate)
  {
      n = $6;
  }
  else
  {
    ASTNode high = stp::GlobalParserInterface->CreateBVConst(32,width-1);
    ASTNode zero = stp::GlobalParserInterface->CreateBVConst(32,0);
    ASTNode cut = stp::GlobalParserInterface->CreateBVConst(32,width-rotate);
    ASTNode cutMinusOne = stp::GlobalParserInterface->CreateBVConst(32,width-rotate-1);

    ASTNode top =  stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT,rotate,*$6,high, cut);
    ASTNode bottom =  stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT,width-rotate,*$6,cutMinusOne,zero);
    n =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVCONCAT,width,bottom,top));
    stp::GlobalParserInterface->deleteNode( $6);
  }
  $$ = n;
}
| LPAREN_TOK UNDERSCORE_TOK BVROTATE_RIGHT_TOK  NUMERAL_TOK  RPAREN_TOK an_term
{
  checkBitVectorTerm(*$6);
  ASTNode *n;
  unsigned width = $6->GetValueWidth();
  unsigned rotate = $4 % width;
  if (0 == rotate)
  {
      n = $6;
  }
  else
  {
    ASTNode high = stp::GlobalParserInterface->CreateBVConst(32,width-1);
    ASTNode zero = stp::GlobalParserInterface->CreateBVConst(32,0);
    ASTNode cut = stp::GlobalParserInterface->CreateBVConst(32,rotate);
    ASTNode cutMinusOne = stp::GlobalParserInterface->CreateBVConst(32,rotate-1);

    ASTNode bottom =  stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT,rotate,*$6,cutMinusOne, zero);
    ASTNode top =  stp::GlobalParserInterface->nf->CreateTerm(BVEXTRACT,width-rotate,*$6,high,cut);
    n =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVCONCAT,width,bottom,top));
    stp::GlobalParserInterface->deleteNode( $6);
  }
  $$ = n;
}
| LPAREN_TOK UNDERSCORE_TOK BVREPEAT_TOK  NUMERAL_TOK RPAREN_TOK an_term
{
  checkBitVectorTerm(*$6);
  unsigned count = $4;
  if (count < 1)
      fatal_yyerror("One or more repeats please");

  unsigned w = $6->GetValueWidth();
  ASTNode n =  *$6;

  for (unsigned i =1; i < count; i++)
  {
        n = stp::GlobalParserInterface->nf->CreateTerm(BVCONCAT,w*(i+1),n,*$6);
  }
  $$ = stp::GlobalParserInterface->newNode(n);
  stp::GlobalParserInterface->deleteNode( $6);
}
| UNDERSCORE_TOK BVCONST_DECIMAL_TOK NUMERAL_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateBVConst(*$2, 10, $3));
  $$->SetValueWidth($3);
  delete $2;
}
| LPAREN_TOK BITVECTOR_FUNCTIONID_TOK an_mixed RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->applyFunction(*$2,*$3));

  if ($$->GetType() != BITVECTOR_TYPE)
      yyerror("Must be bitvector type");

  delete $2;
  delete $3;
}
| LPAREN_TOK FLOATINGPOINT_FUNCTIONID_TOK an_mixed RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->applyFunction(*$2,*$3));

  if ($$->GetType() != FLOATINGPOINT_TYPE)
      yyerror("Must be floating-point type");

  delete $2;
  delete $3;
}
| FLOATINGPOINT_FUNCTIONID_TOK
{
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->applyFunction(*$1,empty));

  if ($$->GetType() != FLOATINGPOINT_TYPE)
    yyerror("Must be floating-point type");

  delete $1;
}
| BITVECTOR_FUNCTIONID_TOK
{
  ASTVec empty;
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->applyFunction(*$1,empty));

  if ($$->GetType() != BITVECTOR_TYPE)
    yyerror("Must be bitvector type");

  delete $1;
}
| LPAREN_TOK EXCLAIMATION_MARK_TOK an_term NAMED_ATTRIBUTE_TOK STRING_TOK RPAREN_TOK
{
  /* This implements (! <an_term> :named foo) */

  ASTNode s(stp::GlobalParserInterface->LookupOrCreateSymbol($5->c_str()));
  delete $5;

  s.SetIndexWidth($3->GetIndexWidth());
  s.SetValueWidth($3->GetValueWidth());

  stp::GlobalParserInterface->addSymbol(s);

  ASTNode n = stp::GlobalParserInterface->CreateNode(EQ,s, *$3);

  stp::GlobalParserInterface->AddAssert(n);

  $$ = $3;
}
| LPAREN_TOK LET_TOK lets an_term RPAREN_TOK
  {
    $$ = $4;
    stp::GlobalParserInterface->letMgr->pop();
  }
;

%%

namespace stp {
  int SMT2Parse() {
    GlobalParserInterface->letMgr->frameMode = true;
    // Each SMT2Parse is one script: the floating-point keywords start
    // disabled and turn on at an FP set-logic.
    SMT2SetFloatTokens(false);
    return smt2parse();
  }
}
