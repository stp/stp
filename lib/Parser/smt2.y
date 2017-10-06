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
  using stp::PARAMBOOL;    //!< Parameterized boolean expression
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
  using stp::PARAMBOOL;    //!< Parameterized boolean expression
  using stp::READ;         //!< Array read expression
  using stp::WRITE;        //!< Array write expression
  using stp::ARRAY;        //!< Array creation expression
  using stp::BITVECTOR;    //!< Bitvector creation expression
  using stp::BOOLEAN;      //!< Boolean creation expression

  using stp::NOT_DECLARED;
  using stp::TO_BE_SATISFIABLE;
  using stp::TO_BE_UNSATISFIABLE;
  using stp::TO_BE_UNKNOWN;

  using stp::BOOLEAN_TYPE;
  using stp::BITVECTOR_TYPE;
  using stp::ARRAY_TYPE;
  using stp::UNKNOWN_TYPE;

  using stp::SOLVER_INVALID;
  using stp::SOLVER_VALID;
  using stp::SOLVER_UNDECIDED;
  using stp::SOLVER_TIMEOUT;
  using stp::SOLVER_ERROR;
  using stp::SOLVER_UNSATISFIABLE;
  using stp::SOLVER_SATISFIABLE;

  // Suppress the bogus warning suppression in bison (it generates
  // compile error)
#undef __GNUC_MINOR__

  extern char* smt2text;
  extern int smt2lineno;
  extern int smt2lex(void);

  int yyerror(const char *s) {
    cout << "(error \"syntax error: line " << smt2lineno << " " << s << "  token: " << smt2text << "\")" << endl;
    return 1;
  }


#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 104857600
#define YYERROR_VERBOSE 1
#define YY_EXIT_FAILURE -1

  %}

%union {
  unsigned uintval;                  /* for numerals in types. */
  //ASTNode,ASTVec
  ASTNode *node;
  ASTVec *vec;
  std::string *str;
};

%start cmd

%type <node> status
%type <vec> an_formulas an_terms function_params an_mixed


%type <node> an_term  an_formula function_param

%token <uintval> NUMERAL_TOK
%token <str> BVCONST_DECIMAL_TOK
%token <str> BVCONST_BINARY_TOK
%token <str> BVCONST_HEXIDECIMAL_TOK

 /* We have this so we can parse :smt-lib-version 2.0 */
%token  DECIMAL_TOK

%token <node> FORMID_TOK TERMID_TOK
%token <str> STRING_TOK BITVECTOR_FUNCTIONID_TOK BOOLEAN_FUNCTIONID_TOK


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

 /* Types for QF_BV and QF_AUFBV. */
%token BITVEC_TOK
%token ARRAY_TOK
%token BOOL_TOK

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
%token DECLARE_FUN_REC_TOK
%token DECLARE_FUNS_REC_TOK
%token DEFINE_SORT_TOK
%token ECHO_TOK
%token EXIT_TOK
%token GET_ASSERTIONS_TOK
%token GET_ASSIGNMENT_TOK
%token GET_INFO_TOK
%token GET_MODEL_TOK
%token GET_OPTION_TOK
%token GET_PROOF_TOK
%token GET_UNSAT_ASSUMPTION_TOK
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
     CHECK_SAT_ASSUMING_TOK LPAREN_TOK an_term RPAREN_TOK
    {
      stp::GlobalParserInterface->unsupported();
    }
|
     DECLARE_CONST_TOK LPAREN_TOK an_term RPAREN_TOK
    {
      stp::GlobalParserInterface->unsupported();
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
       stp::GlobalParserInterface->success();
    }
|
     LOGIC_TOK STRING_TOK
    {
      if (!(0 == strcmp($2->c_str(),"QF_BV") ||
            0 == strcmp($2->c_str(),"QF_ABV") ||
            0 == strcmp($2->c_str(),"QF_AUFBV"))) {
        yyerror("Wrong input logic");
      }
      stp::GlobalParserInterface->success();
      delete $2;
    }
|
     NOTES_TOK attribute STRING_TOK
    {
      delete $3;
    }
|
     NOTES_TOK attribute DECIMAL_TOK
    {}
|
     NOTES_TOK attribute
    {}

;

function_param:
LPAREN_TOK STRING_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK RPAREN_TOK
{
  $$ = new ASTNode(stp::GlobalParserInterface->LookupOrCreateSymbol($2->c_str()));
  stp::GlobalParserInterface->addSymbol(*$$);
  $$->SetIndexWidth(0);
  $$->SetValueWidth($6);
  delete $2;
};

/* Returns a vector of parameters.*/
function_params:
function_param
{
  $$ = new ASTVec;
  $$->push_back(*$1);
  delete $1;
}
| function_params function_param
{
  $$ = $1;
  $$->push_back(*$2);
  delete $2;
};


function_def:
STRING_TOK LPAREN_TOK function_params RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK  an_term
{
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
  delete $10;
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
  delete $6;
}
|
STRING_TOK LPAREN_TOK RPAREN_TOK BOOL_TOK an_formula
{
  ASTVec empty;
  stp::GlobalParserInterface->storeFunction(*$1, empty, *$5);

  delete $1;
  delete $5;
}
|
STRING_TOK LPAREN_TOK RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK an_term
{
  if ($9->GetValueWidth() != $7)
  {
    char msg [100];
    sprintf(msg, "Different bit-widths specified: %d %d", $9->GetValueWidth(), $7);
    yyerror(msg);
  }

  ASTVec empty;
  stp::GlobalParserInterface->storeFunction(*$1,empty, *$9);

  delete $1;
  delete $9;
}
|
STRING_TOK LPAREN_TOK function_params RPAREN_TOK LPAREN_TOK ARRAY_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK RPAREN_TOK an_term
{
  stp::GlobalParserInterface->unsupported();
  delete $1;
  delete $18;
}
|
STRING_TOK LPAREN_TOK RPAREN_TOK LPAREN_TOK ARRAY_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK RPAREN_TOK an_term
{
  stp::GlobalParserInterface->unsupported();
  delete $1;
  delete $17;

#if 0
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  stp::GlobalParserInterface->addSymbol(s);
  unsigned int index_len = $9;
  unsigned int value_len = $14;
  if(index_len > 0) {
    s.SetIndexWidth($9);
  }
  else {
    FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
  }

  if(value_len > 0) {
    s.SetValueWidth($14);
  }
  else {
    FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
  }

  ASTVec empty;
  stp::GlobalParserInterface->storeFunction(*$1,empty, *$17);
#endif

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
| STRING_TOK LPAREN_TOK RPAREN_TOK BOOL_TOK
{
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  s.SetIndexWidth(0);
  s.SetValueWidth(0);
  stp::GlobalParserInterface->addSymbol(s);
  delete $1;
}
| STRING_TOK LPAREN_TOK RPAREN_TOK LPAREN_TOK ARRAY_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK RPAREN_TOK
{
  ASTNode s = stp::GlobalParserInterface->LookupOrCreateSymbol($1->c_str());
  stp::GlobalParserInterface->addSymbol(s);
  unsigned int index_len = $9;
  unsigned int value_len = $14;
  if(index_len > 0) {
    s.SetIndexWidth($9);
  }
  else {
    stp::FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
  }

  if(value_len > 0) {
    s.SetValueWidth($14);
  }
  else {
    stp::FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
  }
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
| FORMID_TOK
{
  $$ = stp::GlobalParserInterface->newNode(*$1);
  stp::GlobalParserInterface->deleteNode($1);
}
| LPAREN_TOK EQ_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = stp::GlobalParserInterface->newNode(EQ,*$3, *$4);
  $$ = n;
  stp::GlobalParserInterface->deleteNode($3);
  stp::GlobalParserInterface->deleteNode($4);
}
| LPAREN_TOK DISTINCT_TOK an_terms RPAREN_TOK
{
  using namespace stp;

  ASTVec terms = *$3;
  ASTVec forms;

  for(ASTVec::const_iterator it=terms.begin(),itend=terms.end();
      it!=itend; it++)
  {
    for(ASTVec::const_iterator it2=it+1; it2!=itend; it2++) {
      ASTNode n =
        stp::GlobalParserInterface->nf->CreateNode(NOT, stp::GlobalParserInterface->CreateNode(EQ, *it, *it2));

      forms.push_back(n);
    }
  }

  if(forms.size() == 0)
    FatalError("empty distinct");

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

  for(ASTVec::const_iterator it=terms.begin(),itend=terms.end();
      it!=itend; it++) {
    for(ASTVec::const_iterator it2=it+1; it2!=itend; it2++) {
      ASTNode n = (stp::GlobalParserInterface->nf->CreateNode(NOT, stp::GlobalParserInterface->CreateNode(IFF, *it, *it2)));
      forms.push_back(n);
    }
  }

  if(forms.size() == 0)
    FatalError("empty distinct");

  $$ = (forms.size() == 1) ?
    stp::GlobalParserInterface->newNode(forms[0]) :
    stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(AND, forms));

  delete $3;
}
| LPAREN_TOK BVSLT_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = stp::GlobalParserInterface->newNode(BVSLT, *$3, *$4);
  $$ = n;
  stp::GlobalParserInterface->deleteNode($3);
  stp::GlobalParserInterface->deleteNode($4);
}
| LPAREN_TOK BVSLE_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = stp::GlobalParserInterface->newNode(BVSLE, *$3, *$4);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK BVSGT_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = stp::GlobalParserInterface->newNode(BVSGT, *$3, *$4);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK BVSGE_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = stp::GlobalParserInterface->newNode(BVSGE, *$3, *$4);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK BVLT_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = stp::GlobalParserInterface->newNode(BVLT, *$3, *$4);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK BVLE_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = stp::GlobalParserInterface->newNode(BVLE, *$3, *$4);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK BVGT_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = stp::GlobalParserInterface->newNode(BVGT, *$3, *$4);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK BVGE_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = stp::GlobalParserInterface->newNode(BVGE, *$3, *$4);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
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
| LPAREN_TOK IMPLIES_TOK an_formula an_formula RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(IMPLIES, *$3, *$4);
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
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
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(AND, *$3));
  delete $3;
}
| LPAREN_TOK OR_TOK an_formulas RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->CreateNode(OR, *$3));
  delete $3;
}
| LPAREN_TOK XOR_TOK an_formula an_formula RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(XOR, *$3, *$4);
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK EQ_TOK an_formula an_formula RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(IFF, *$3, *$4);
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK LET_TOK LPAREN_TOK
  {
    stp::GlobalParserInterface->letMgr->push();  // TODO this isn't going to clear properly if it's an_term later.
  }
  lets RPAREN_TOK an_formula RPAREN_TOK
  {
    $$ = $7;
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

lets: let lets
| let
{};

let: LPAREN_TOK STRING_TOK an_formula RPAREN_TOK
{
  //populate the hashtable from LET-var -->
  //LET-exprs and then process them:
  //
  //1. ensure that LET variables do not clash
  //1. with declared variables.
  //
  //2. Ensure that LET variables are not
  //2. defined more than once
  stp::GlobalParserInterface->letMgr->LetExprMgr(*$2,*$3);
  delete $2;
  stp::GlobalParserInterface->deleteNode( $3);
}
| LPAREN_TOK STRING_TOK an_term RPAREN_TOK
{
  //populate the hashtable from LET-var -->
  //LET-exprs and then process them:
  //
  //1. ensure that LET variables do not clash
  //1. with declared variables.
  //
  //2. Ensure that LET variables are not
  //2. defined more than once
  stp::GlobalParserInterface->letMgr->LetExprMgr(*$2,*$3);
  delete $2;
  stp::GlobalParserInterface->deleteNode( $3);

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

an_term:
TERMID_TOK
{
  $$ = stp::GlobalParserInterface->newNode((*$1));
  stp::GlobalParserInterface->deleteNode( $1);
}
| LPAREN_TOK an_term RPAREN_TOK
{
  $$ = $2;
}
| SELECT_TOK an_term an_term
{
  //ARRAY READ
  // valuewidth is same as array, indexwidth is 0.
  ASTNode array = *$2;
  ASTNode index = *$3;
  unsigned int width = array.GetValueWidth();
  ASTNode * n =
    stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(READ, width, array, index));
  $$ = n;
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
  ASTNode * n = stp::GlobalParserInterface->newNode(write_term);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
| LPAREN_TOK UNDERSCORE_TOK BVEXTRACT_TOK  NUMERAL_TOK  NUMERAL_TOK RPAREN_TOK an_term
{
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
  unsigned w = $6->GetValueWidth() + $4;
  ASTNode width = stp::GlobalParserInterface->CreateBVConst(32,w);
  ASTNode *n =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVZX,w,*$6,width));
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $6);
}
|  LPAREN_TOK UNDERSCORE_TOK BVSX_TOK  NUMERAL_TOK  RPAREN_TOK an_term
{
  unsigned w = $6->GetValueWidth() + $4;
  ASTNode width = stp::GlobalParserInterface->CreateBVConst(32,w);
  ASTNode *n =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVSX,w,*$6,width));
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $6);
}

|  ITE_TOK an_formula an_term an_term
{
  const unsigned int width = $3->GetValueWidth();
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateArrayTerm(ITE,$4->GetIndexWidth(), width,*$2, *$3, *$4));
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
  stp::GlobalParserInterface->deleteNode( $4);
}
|  BVCONCAT_TOK an_term an_term
{
  const unsigned int width = $2->GetValueWidth() + $3->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVCONCAT, width, *$2, *$3));
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVNOT_TOK an_term
{
  //this is the BVNEG (term) in the CVCL language
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, *$2));
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
}
|  BVNEG_TOK an_term
{
  //this is the BVUMINUS term in CVCL langauge
  unsigned width = $2->GetValueWidth();
  ASTNode * n =  stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVUMINUS,width,*$2));
  $$ = n;
    stp::GlobalParserInterface->deleteNode( $2);
}
|  BVAND_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVAND, width, *$2, *$3);
  $$ = n;
    stp::GlobalParserInterface->deleteNode( $2);
    stp::GlobalParserInterface->deleteNode( $3);
}
|  BVOR_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVOR, width, *$2, *$3);
  $$ = n;
    stp::GlobalParserInterface->deleteNode( $2);
    stp::GlobalParserInterface->deleteNode( $3);
}
|  BVXOR_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVXOR, width, *$2, *$3);
  $$ = n;
    stp::GlobalParserInterface->deleteNode( $2);
    stp::GlobalParserInterface->deleteNode( $3);
}
| BVXNOR_TOK an_term an_term
{
//   (bvxnor s t) abbreviates (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(
  stp::GlobalParserInterface->nf->CreateTerm( BVOR, width,
    stp::GlobalParserInterface->nf->CreateTerm(BVAND, width, *$2, *$3),
      stp::GlobalParserInterface->nf->CreateTerm(BVAND, width,
        stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, *$2),
        stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, *$3)
      )
    )
  );

  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVCOMP_TOK an_term an_term
{
  ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(ITE, 1,
  stp::GlobalParserInterface->nf->CreateNode(EQ, *$2, *$3),
  stp::GlobalParserInterface->CreateOneConst(1),
  stp::GlobalParserInterface->CreateZeroConst(1)));

  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVSUB_TOK an_term an_term
{
  const unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVSUB, width, *$2, *$3);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVPLUS_TOK an_term an_term
{
  const unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVPLUS, width, *$2, *$3);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);

}
|  BVMULT_TOK an_term an_term
{
  const unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVMULT, width, *$2, *$3));
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|      BVDIV_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVDIV, width, *$2, *$3);
  $$ = n;

  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|      BVMOD_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVMOD, width, *$2, *$3);
  $$ = n;

  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|      SBVDIV_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(SBVDIV, width, *$2, *$3);
  $$ = n;

  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|      SBVREM_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(SBVREM, width, *$2, *$3);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|      SBVMOD_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(SBVMOD, width, *$2, *$3);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVNAND_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, stp::GlobalParserInterface->nf->CreateTerm(BVAND, width, *$2, *$3)));
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVNOR_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->nf->CreateTerm(BVNOT, width, stp::GlobalParserInterface->nf->CreateTerm(BVOR, width, *$2, *$3)));
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVLEFTSHIFT_1_TOK an_term an_term
{
  // shifting left by who know how much?
  unsigned int w = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVLEFTSHIFT,w,*$2,*$3);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
| BVRIGHTSHIFT_1_TOK an_term an_term
{
  // shifting right by who know how much?
  unsigned int w = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVRIGHTSHIFT,w,*$2,*$3);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
|  BVARITHRIGHTSHIFT_TOK an_term an_term
{
  // shifting arithmetic right by who know how much?
  unsigned int w = $2->GetValueWidth();
  ASTNode * n = stp::GlobalParserInterface->newNode(BVSRSHIFT,w,*$2,*$3);
  $$ = n;
  stp::GlobalParserInterface->deleteNode( $2);
  stp::GlobalParserInterface->deleteNode( $3);
}
| LPAREN_TOK UNDERSCORE_TOK BVROTATE_LEFT_TOK  NUMERAL_TOK  RPAREN_TOK an_term
{
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
  unsigned count = $4;
  if (count < 1)
      stp::FatalError("One or more repeats please");

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
| BVCONST_HEXIDECIMAL_TOK
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
| LPAREN_TOK BITVECTOR_FUNCTIONID_TOK an_mixed RPAREN_TOK
{
  $$ = stp::GlobalParserInterface->newNode(stp::GlobalParserInterface->applyFunction(*$2,*$3));

  if ($$->GetType() != BITVECTOR_TYPE)
      yyerror("Must be bitvector type");

  delete $2;
  delete $3;
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
| LPAREN_TOK LET_TOK LPAREN_TOK
  {
    stp::GlobalParserInterface->letMgr->push();
  }
  lets RPAREN_TOK an_term RPAREN_TOK
  {
    $$ = $7;
    stp::GlobalParserInterface->letMgr->pop();
  }

;

%%

namespace stp {
  int SMT2Parse() {
    return smt2parse();
  }
}
