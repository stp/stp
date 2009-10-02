%{
  /********************************************************************
   * AUTHORS: Vijay Ganesh
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
  // -*- c++ -*-

#include "parser.h"

  using namespace std; 
  using namespace BEEV;

  // Suppress the bogus warning suppression in bison (it generates
  // compile error)
#undef __GNUC_MINOR__
  
  extern char* smttext;
  extern int smtlineno;
  
  extern int smtlex(void);

  int yyerror(const char *s) {
    cout << "syntax error: line " << smtlineno << "\n" << s << endl;
    cout << "  token: " << smttext << endl;
    FatalError("");
    return 1;
  }

  ASTNode query;
#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 104857600
#define YYERROR_VERBOSE 1
#define YY_EXIT_FAILURE -1
#define YYPARSE_PARAM AssertsQuery
%}

%union {  
  // FIXME: Why is this not an UNSIGNED int?
  int uintval;			/* for numerals in types. */

  // for BV32 BVCONST 
  unsigned long long ullval;

  struct {
    //stores the indexwidth and valuewidth
    //indexwidth is 0 iff type is bitvector. positive iff type is
    //array, and stores the width of the indexing bitvector
    unsigned int indexwidth;
    //width of the bitvector type
    unsigned int valuewidth;
  } indexvaluewidth;

  //ASTNode,ASTVec
  BEEV::ASTNode *node;
  BEEV::ASTVec *vec;
  std::string *str;
};

%start cmd

%type <indexvaluewidth> sort_symb sort_symbs
%type <node> status
%type <vec> bench_attributes an_formulas an_terms

%type <node> benchmark bench_name bench_attribute
%type <node> an_term an_nonbvconst_term an_formula 

%type <node> var fvar logic_name
%type <str> user_value

%token <uintval> NUMERAL_TOK
%token <str> BVCONST_TOK
%token <node> BITCONST_TOK
%token <node> FORMID_TOK TERMID_TOK 
%token <str> STRING_TOK
%token <str> USER_VAL_TOK
%token SOURCE_TOK
%token CATEGORY_TOK
%token DIFFICULTY_TOK
%token BITVEC_TOK
%token ARRAY_TOK
%token SELECT_TOK
%token STORE_TOK
%token TRUE_TOK
%token FALSE_TOK
%token NOT_TOK
%token IMPLIES_TOK
%token ITE_TOK
%token AND_TOK
%token OR_TOK
%token XOR_TOK
%token IFF_TOK
%token EXISTS_TOK
%token FORALL_TOK
%token LET_TOK
%token FLET_TOK
%token NOTES_TOK
%token CVC_COMMAND_TOK
%token SORTS_TOK
%token FUNS_TOK
%token PREDS_TOK
%token EXTENSIONS_TOK
%token DEFINITION_TOK
%token AXIOMS_TOK
%token LOGIC_TOK
%token COLON_TOK
%token LBRACKET_TOK
%token RBRACKET_TOK
%token LPAREN_TOK
%token RPAREN_TOK
%token SAT_TOK
%token UNSAT_TOK
%token UNKNOWN_TOK
%token ASSUMPTION_TOK
%token FORMULA_TOK
%token STATUS_TOK
%token BENCHMARK_TOK
%token EXTRASORTS_TOK
%token EXTRAFUNS_TOK
%token EXTRAPREDS_TOK
%token LANGUAGE_TOK
%token DOLLAR_TOK
%token QUESTION_TOK
%token DISTINCT_TOK
%token SEMICOLON_TOK
%token EOF_TOK
%token EQ_TOK
/*BV SPECIFIC TOKENS*/
%token NAND_TOK
%token NOR_TOK
%token NEQ_TOK
%token ASSIGN_TOK
%token BV_TOK
%token BOOLEAN_TOK
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
%token BVZX_TOK
%token BVROTATE_RIGHT_TOK
%token BVROTATE_LEFT_TOK
%token BOOLEXTRACT_TOK
%token BOOL_TO_BV_TOK
%token BVEXTRACT_TOK

%left LBRACKET_TOK RBRACKET_TOK

%%

cmd:
    benchmark
    {
      ASTNode assumptions;
      if($1 == NULL) 
	{
	  assumptions = GlobalBeevMgr->CreateNode(TRUE);
	} 
      else 
	{
        assumptions = *$1;
	}
      
      if(query.IsNull()) 
	{
	  query = GlobalBeevMgr->CreateNode(FALSE);
	}

      ((ASTVec*)AssertsQuery)->push_back(assumptions);
      ((ASTVec*)AssertsQuery)->push_back(query);
      delete $1;
      YYACCEPT;
    }
;

benchmark:
    LPAREN_TOK BENCHMARK_TOK bench_name bench_attributes RPAREN_TOK
    {
      if($4 != NULL){
	if($4->size() > 1) 
	  $$ = new ASTNode(GlobalBeevMgr->CreateNode(AND,*$4));
	else
	  $$ = new ASTNode((*$4)[0]);	  
	delete $4;
      }
      else {
	$$ = NULL;
      }
    }
/*   | EOF_TOK */
/*     { */
/*     } */
;

bench_name:
    FORMID_TOK
    {
    }
;

bench_attributes:
    bench_attribute
    {
      $$ = new ASTVec;
      if ($1 != NULL) {
	$$->push_back(*$1);
	GlobalBeevMgr->AddAssert(*$1);
	delete $1;
      }
    }
  | bench_attributes bench_attribute
    {
      if ($1 != NULL && $2 != NULL) {
	$1->push_back(*$2);
	GlobalBeevMgr->AddAssert(*$2);
	$$ = $1;
	delete $2;
      }
    }
;

bench_attribute:
    COLON_TOK ASSUMPTION_TOK an_formula
    {
      //assumptions are like asserts
      $$ = $3;
    }
  | COLON_TOK FORMULA_TOK an_formula
    {
		// Previously this would call AddQuery() on the negation.
		// But if multiple formula were (eroneously) present
		// it discarded all but the last formula. Allowing multiple 
		// formula and taking the conjunction of them along with all
		// the assumptions is what the other solvers do.  

      //assumptions are like asserts
      $$ = $3;
    }
  | COLON_TOK STATUS_TOK status
    {
      $$ = NULL;
    }
  | COLON_TOK LOGIC_TOK logic_name
    {
      if (!(0 == strcmp($3->GetName(),"QF_UFBV")  ||
            0 == strcmp($3->GetName(),"QF_BV") ||
            //0 == strcmp($3->GetName(),"QF_UF") ||
            0 == strcmp($3->GetName(),"QF_AUFBV"))) {
	yyerror("Wrong input logic:");
      }
      $$ = NULL;
    }
  | COLON_TOK EXTRAFUNS_TOK LPAREN_TOK var_decls RPAREN_TOK
    {
      $$ = NULL;
    }
  | COLON_TOK EXTRAPREDS_TOK LPAREN_TOK var_decls RPAREN_TOK
    {
      $$ = NULL;
    }
  | annotation 
    {
      $$ = NULL;
    }
;

logic_name:
    FORMID_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK
    {
      $$ = $1;
    }
  | FORMID_TOK
    {
      $$ = $1;
    }
;

status:
    SAT_TOK { 
    	input_status = TO_BE_SATISFIABLE; 
    	$$ = NULL; 
 		}
  | UNSAT_TOK { 
      	input_status = TO_BE_UNSATISFIABLE; 
    	$$ = NULL; 
  }
  | UNKNOWN_TOK 
  { 
      	input_status = TO_BE_UNKNOWN; 
    	$$ = NULL; 
  }
 ;


/* annotations: */
/*     annotation */
/*     { */
/*     } */
/*   | annotations annotation */
/*     { */
/*     } */
/*   ; */
  
annotation:
    attribute 
    {
    }
  | attribute user_value 
    {
    }
;

user_value:
    USER_VAL_TOK
    {
      //cerr << "Printing user_value: " << *$1 << endl;
    }
;

attribute:
    COLON_TOK SOURCE_TOK
    {
    }
   | COLON_TOK CATEGORY_TOK
    {
    }
   | COLON_TOK DIFFICULTY_TOK 
;

sort_symbs:
    sort_symb 
    {
      //a single sort symbol here means either a BitVec or a Boolean
      $$.indexwidth = $1.indexwidth;
      $$.valuewidth = $1.valuewidth;
    }
  | sort_symb sort_symb
    {
      //two sort symbols mean f: type --> type
      $$.indexwidth = $1.valuewidth;
      $$.valuewidth = $2.valuewidth;
    }
;

var_decls:
    var_decl
    {
    }
//  | LPAREN_TOK var_decl RPAREN_TOK
  |
    var_decls var_decl
    {
    }
;

var_decl:
    LPAREN_TOK FORMID_TOK sort_symbs RPAREN_TOK
    {
      _parser_symbol_table.insert(*$2);
      //Sort_symbs has the indexwidth/valuewidth. Set those fields in
      //var
      $2->SetIndexWidth($3.indexwidth);
      $2->SetValueWidth($3.valuewidth);
      if(print_STPinput_back_flag)
      	GlobalBeevMgr->ListOfDeclaredVars.push_back(*$2);
    }
   | LPAREN_TOK FORMID_TOK RPAREN_TOK
    {
      _parser_symbol_table.insert(*$2);
      //Sort_symbs has the indexwidth/valuewidth. Set those fields in
      //var
      $2->SetIndexWidth(0);
      $2->SetValueWidth(0);
      if(print_STPinput_back_flag)
      	GlobalBeevMgr->ListOfDeclaredVars.push_back(*$2);
    }
;

an_formulas:
    an_formula
    {
      $$ = new ASTVec;
      if ($1 != NULL) {
	$$->push_back(*$1);
	delete $1;
      }
    }
  |
    an_formulas an_formula
    {
      if ($1 != NULL && $2 != NULL) {
	$1->push_back(*$2);
	$$ = $1;
	delete $2;
      }
    }
;

an_formula:   
    TRUE_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateNode(TRUE)); 
      $$->SetIndexWidth(0); 
      $$->SetValueWidth(0);
    }
  | FALSE_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateNode(FALSE)); 
      $$->SetIndexWidth(0); 
      $$->SetValueWidth(0);
    }
  | fvar
    {
      $$ = $1;
    }
  | LPAREN_TOK EQ_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK EQ_TOK an_term an_term annotations RPAREN_TOK
    {
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateSimplifiedEQ(*$3, *$4));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $3;
      delete $4;      
    }
  | LPAREN_TOK DISTINCT_TOK an_terms RPAREN_TOK
    {
      using namespace BEEV;

      ASTVec terms = *$3;
      ASTVec forms;

      for(ASTVec::const_iterator it=terms.begin(),itend=terms.end();
          it!=itend; it++) {
        for(ASTVec::const_iterator it2=it+1; it2!=itend; it2++) {
          ASTNode * n = new ASTNode(GlobalBeevMgr->CreateNode(NOT, GlobalBeevMgr->CreateNode(EQ, *it, *it2)));

          GlobalBeevMgr->BVTypeCheck(*n);
          
          forms.push_back(*n); 
        }
      }

      if(forms.size() == 0) 
        FatalError("empty distinct");
 
      $$ = (forms.size() == 1) ?
           new ASTNode(forms[0]) :
           new ASTNode(GlobalBeevMgr->CreateNode(AND, forms));

      delete $3;
    }

  | LPAREN_TOK BVSLT_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVSLT_TOK an_term an_term annotations RPAREN_TOK
    {
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateNode(BVSLT, *$3, *$4));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $3;
      delete $4;      
    }
  | LPAREN_TOK BVSLE_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVSLE_TOK an_term an_term annotations RPAREN_TOK
    {
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateNode(BVSLE, *$3, *$4));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $3;
      delete $4;      
    }
  | LPAREN_TOK BVSGT_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVSGT_TOK an_term an_term annotations RPAREN_TOK
    {
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateNode(BVSGT, *$3, *$4));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $3;
      delete $4;      
    }
  | LPAREN_TOK BVSGE_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVSGE_TOK an_term an_term annotations RPAREN_TOK
    {
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateNode(BVSGE, *$3, *$4));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $3;
      delete $4;      
    }
  | LPAREN_TOK BVLT_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVLT_TOK an_term an_term annotations RPAREN_TOK
    {
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateNode(BVLT, *$3, *$4));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $3;
      delete $4;      
    }
  | LPAREN_TOK BVLE_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVLE_TOK an_term an_term annotations RPAREN_TOK
    {
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateNode(BVLE, *$3, *$4));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $3;
      delete $4;      
    }
  | LPAREN_TOK BVGT_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVGT_TOK an_term an_term annotations RPAREN_TOK
    {
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateNode(BVGT, *$3, *$4));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $3;
      delete $4;      
    }
  | LPAREN_TOK BVGE_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVGE_TOK an_term an_term annotations RPAREN_TOK
    {
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateNode(BVGE, *$3, *$4));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $3;
      delete $4;      
    }
  | LPAREN_TOK an_formula RPAREN_TOK
    {
      $$ = $2;
    }
  | LPAREN_TOK NOT_TOK an_formula RPAREN_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateNode(NOT, *$3));
      delete $3;
    }
  | LPAREN_TOK IMPLIES_TOK an_formula an_formula RPAREN_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateNode(IMPLIES, *$3, *$4));
      delete $3;
      delete $4;
    }
  | LPAREN_TOK ITE_TOK an_formula an_formula an_formula RPAREN_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateSimplifiedFormulaITE(*$3, *$4, *$5));
      delete $3;
      delete $4;
      delete $5;
    }
  | LPAREN_TOK AND_TOK an_formulas RPAREN_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateNode(AND, *$3));
      delete $3;
    }
  | LPAREN_TOK OR_TOK an_formulas RPAREN_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateNode(OR, *$3));
      delete $3;
    }
  | LPAREN_TOK XOR_TOK an_formula an_formula RPAREN_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateNode(XOR, *$3, *$4));
      delete $3;
      delete $4;
    }
  | LPAREN_TOK IFF_TOK an_formula an_formula RPAREN_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateNode(IFF, *$3, *$4));
      delete $3;
      delete $4;
    }
  | letexpr_mgmt an_formula RPAREN_TOK
  //| letexpr_mgmt an_formula annotations RPAREN_TOK
    {
      $$ = $2;
      //Cleanup the LetIDToExprMap
      GlobalBeevMgr->CleanupLetIDMap();			 
    }
;

letexpr_mgmt: 
    LPAREN_TOK LET_TOK LPAREN_TOK QUESTION_TOK FORMID_TOK an_term RPAREN_TOK
    {
     //Expr must typecheck
      GlobalBeevMgr->BVTypeCheck(*$6);
      
      //set the valuewidth of the identifier
      $5->SetValueWidth($6->GetValueWidth());
      $5->SetIndexWidth($6->GetIndexWidth());
      
      //populate the hashtable from LET-var -->
      //LET-exprs and then process them:
      //
      //1. ensure that LET variables do not clash
      //1. with declared variables.
      //
      //2. Ensure that LET variables are not
      //2. defined more than once
      GlobalBeevMgr->LetExprMgr(*$5,*$6);
      delete $5;
      delete $6;      
   }
 | LPAREN_TOK FLET_TOK LPAREN_TOK DOLLAR_TOK FORMID_TOK an_formula RPAREN_TOK 
   {
     //Expr must typecheck
     GlobalBeevMgr->BVTypeCheck(*$6);
     
     //set the valuewidth of the identifier
     $5->SetValueWidth($6->GetValueWidth());
     $5->SetIndexWidth($6->GetIndexWidth());
     
     //Do LET-expr management
     GlobalBeevMgr->LetExprMgr(*$5,*$6);
     delete $5;
     delete $6;     
   }

an_terms: 
    an_term
    {
      $$ = new ASTVec;
      if ($1 != NULL) {
	$$->push_back(*$1);
	delete $1;
      }
    }
  |
    an_terms an_term
    {
      if ($1 != NULL && $2 != NULL) {
	$1->push_back(*$2);
	$$ = $1;
	delete $2;
      }
    }
;

an_term:
    BVCONST_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateBVConst($1, 10, 32));
    }
  | BVCONST_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->CreateBVConst($1,10,$3));
      delete $1;
    }
  | an_nonbvconst_term
  ;

an_nonbvconst_term: 
    BITCONST_TOK { $$ = $1; }
  | var
    {
      $$ = new ASTNode(GlobalBeevMgr->ResolveID(*$1));
      delete $1;
    }
  | LPAREN_TOK an_term RPAREN_TOK
  //| LPAREN_TOK an_term annotations RPAREN_TOK
    {
      $$ = $2;
      //$$ = new ASTNode(GlobalBeevMgr->SimplifyTerm(*$2));
      //delete $2;
    }
  | SELECT_TOK an_term an_term
    {
      //ARRAY READ
      // valuewidth is same as array, indexwidth is 0.
      ASTNode array = *$2;
      ASTNode index = *$3;
      unsigned int width = array.GetValueWidth();
      ASTNode * n = 
	new ASTNode(GlobalBeevMgr->CreateTerm(READ, width, array, index));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
      delete $3;
    }
  | STORE_TOK an_term an_term an_term
    {
      //ARRAY WRITE
      unsigned int width = $4->GetValueWidth();
      ASTNode array = *$2;
      ASTNode index = *$3;
      ASTNode writeval = *$4;
      ASTNode write_term = GlobalBeevMgr->CreateTerm(WRITE,width,array,index,writeval);
      write_term.SetIndexWidth($2->GetIndexWidth());
      GlobalBeevMgr->BVTypeCheck(write_term);
      ASTNode * n = new ASTNode(write_term);
      $$ = n;
      delete $2;
      delete $3;
      delete $4;
    }
  | BVEXTRACT_TOK LBRACKET_TOK NUMERAL_TOK COLON_TOK NUMERAL_TOK RBRACKET_TOK an_term
    {
      int width = $3 - $5 + 1;
      if (width < 0)
	yyerror("Negative width in extract");
      
      if((unsigned)$3 >= $7->GetValueWidth())
	yyerror("Parsing: Wrong width in BVEXTRACT\n");			 
      
      ASTNode hi  =  GlobalBeevMgr->CreateBVConst(32, $3);
      ASTNode low =  GlobalBeevMgr->CreateBVConst(32, $5);
      ASTNode output = GlobalBeevMgr->CreateTerm(BVEXTRACT, width, *$7,hi,low);
      ASTNode * n = new ASTNode(output);
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $7;
    }
  |  ITE_TOK an_formula an_term an_term 
    {
      unsigned int width = $3->GetValueWidth();
      if (width != $4->GetValueWidth()) {
	cerr << *$3;
	cerr << *$4;
	yyerror("Width mismatch in IF-THEN-ELSE");
      }			 
      if($3->GetIndexWidth() != $4->GetIndexWidth())
	yyerror("Width mismatch in IF-THEN-ELSE");
      
      GlobalBeevMgr->BVTypeCheck(*$2);
      GlobalBeevMgr->BVTypeCheck(*$3);
      GlobalBeevMgr->BVTypeCheck(*$4);
      $$ = new ASTNode(GlobalBeevMgr->CreateSimplifiedTermITE(*$2, *$3, *$4));
      //$$ = new ASTNode(GlobalBeevMgr->CreateTerm(ITE,width,*$2, *$3, *$4));
      $$->SetIndexWidth($4->GetIndexWidth());
      GlobalBeevMgr->BVTypeCheck(*$$);
      delete $2;
      delete $3;
      delete $4;
    }
  |  BVCONCAT_TOK an_term an_term 
    {
      unsigned int width = $2->GetValueWidth() + $3->GetValueWidth();
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVCONCAT, width, *$2, *$3));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      
      delete $2;
      delete $3;
    }
  |  BVNOT_TOK an_term
    {
      //this is the BVNEG (term) in the CVCL language
      unsigned int width = $2->GetValueWidth();
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVNEG, width, *$2));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
    }
  |  BVNEG_TOK an_term
    {
      //this is the BVUMINUS term in CVCL langauge
      unsigned width = $2->GetValueWidth();
      ASTNode * n =  new ASTNode(GlobalBeevMgr->CreateTerm(BVUMINUS,width,*$2));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
    }
  |  BVAND_TOK an_term an_term 
    {
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in AND");
      }
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVAND, width, *$2, *$3));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
      delete $3;
    }
  |  BVOR_TOK an_term an_term 
    {
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in OR");
      }
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVOR, width, *$2, *$3)); 
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
      delete $3;
    }
  |  BVXOR_TOK an_term an_term 
    {
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in XOR");
      }
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVXOR, width, *$2, *$3));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
      delete $3;
    }
  |  BVSUB_TOK an_term an_term 
    {
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in BVSUB");
      }
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVSUB, width, *$2, *$3));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
      delete $3;
    }
  |  BVPLUS_TOK an_term an_term 
    {
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in BVPLUS");
      }
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVPLUS, width, *$2, *$3));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
      delete $3;

    }
  |  BVMULT_TOK an_term an_term 
    {
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in BVMULT");
      }
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVMULT, width, *$2, *$3));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
      delete $3;
    }

|      BVDIV_TOK an_term an_term  
{
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in BVDIV");
      }
	ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVDIV, width, *$2, *$3));
	GlobalBeevMgr->BVTypeCheck(*n);
	$$ = n;

	delete $2;
	delete $3;
}
|      BVMOD_TOK an_term an_term
{
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in BVMOD");
      }
	ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVMOD, width, *$2, *$3));
	GlobalBeevMgr->BVTypeCheck(*n);
	$$ = n;

	delete $2;
	delete $3;
}
|      SBVDIV_TOK an_term an_term
{
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in SBVDIV");
      }
	ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(SBVDIV, width, *$2, *$3));
	GlobalBeevMgr->BVTypeCheck(*n);
	$$ = n;

	delete $2;
	delete $3;
}
|      SBVREM_TOK an_term an_term
{
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in SBVREM");
      }
	ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(SBVREM, width, *$2, *$3));
	GlobalBeevMgr->BVTypeCheck(*n);
	$$ = n;
	delete $2;
	delete $3;
}        
|      SBVMOD_TOK an_term an_term
{
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in SBVMOD");
      }
	ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(SBVMOD, width, *$2, *$3));
	GlobalBeevMgr->BVTypeCheck(*n);
	$$ = n;
	delete $2;
	delete $3;
}        





  |  BVNAND_TOK an_term an_term 
    {
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in BVNAND");
      }
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVNAND, width, *$2, *$3));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
      delete $3;
    }
  |  BVNOR_TOK an_term an_term 
    {
      unsigned int width = $2->GetValueWidth();
      if (width != $3->GetValueWidth()) {
	yyerror("Width mismatch in BVNOR");
      }
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVNOR, width, *$2, *$3)); 
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $2;
      delete $3;
    }
   |  BVLEFTSHIFT_1_TOK an_term an_term 
{
	// shifting left by who know how much?
      unsigned int w = $2->GetValueWidth();
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVLEFTSHIFT,w,*$2,*$3));
	  GlobalBeevMgr->BVTypeCheck(*n);
  	  $$ = n;
      delete $2;
    }
  | BVRIGHTSHIFT_1_TOK an_term an_term 
    {
    // shifting right by who know how much?
      unsigned int w = $2->GetValueWidth();
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVRIGHTSHIFT,w,*$2,*$3));
	  GlobalBeevMgr->BVTypeCheck(*n);
  	  $$ = n;
      delete $2;
    }
   |  BVARITHRIGHTSHIFT_TOK an_term an_term
    {
      // shifting arithmetic right by who know how much?
      unsigned int w = $2->GetValueWidth();
      ASTNode * n = new ASTNode(GlobalBeevMgr->CreateTerm(BVSRSHIFT,w,*$2,*$3));
	  GlobalBeevMgr->BVTypeCheck(*n);
  	  $$ = n;
      delete $2;
    }
  |  BVROTATE_LEFT_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK an_term 
    {
      GlobalBeevMgr->BVTypeCheck(*$5);
      
      ASTNode *n;
      unsigned width = $5->GetValueWidth();
      unsigned rotate = $3;
      if (0 == rotate)
      {
      	n = $5;
      }
      else if (rotate < width)
      {
      	ASTNode high = GlobalBeevMgr->CreateBVConst(32,width-1);
      	ASTNode zero = GlobalBeevMgr->CreateBVConst(32,0);
      	ASTNode cut = GlobalBeevMgr->CreateBVConst(32,width-rotate);
      	ASTNode cutMinusOne = GlobalBeevMgr->CreateBVConst(32,width-rotate-1);

      	ASTNode top =  GlobalBeevMgr->CreateTerm(BVEXTRACT,rotate,*$5,high, cut);
      	ASTNode bottom =  GlobalBeevMgr->CreateTerm(BVEXTRACT,width-rotate,*$5,cutMinusOne,zero);
      	n =  new ASTNode(GlobalBeevMgr->CreateTerm(BVCONCAT,width,bottom,top));
        delete $5;
      }
      else
      {
      	n = NULL; // remove gcc warning.
      	yyerror("Rotate must be strictly less than the width.");
      }
      
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      
    }
    |  BVROTATE_RIGHT_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK an_term 
    {
      GlobalBeevMgr->BVTypeCheck(*$5);
      
      ASTNode *n;
      unsigned width = $5->GetValueWidth();
      unsigned rotate = $3;
      if (0 == rotate)
      {
      	n = $5;
      }
      else if (rotate < width)
      {
      	ASTNode high = GlobalBeevMgr->CreateBVConst(32,width-1);
      	ASTNode zero = GlobalBeevMgr->CreateBVConst(32,0);
      	ASTNode cut = GlobalBeevMgr->CreateBVConst(32,rotate); 
      	ASTNode cutMinusOne = GlobalBeevMgr->CreateBVConst(32,rotate-1);

      	ASTNode bottom =  GlobalBeevMgr->CreateTerm(BVEXTRACT,rotate,*$5,cutMinusOne, zero);
      	ASTNode top =  GlobalBeevMgr->CreateTerm(BVEXTRACT,width-rotate,*$5,high,cut);
      	n =  new ASTNode(GlobalBeevMgr->CreateTerm(BVCONCAT,width,bottom,top));
        delete $5;
      }
      else
      {
		n = NULL; // remove gcc warning.
      	yyerror("Rotate must be strictly less than the width.");
      }
      
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      
    }
  |  BVSX_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK an_term 
    {
      GlobalBeevMgr->BVTypeCheck(*$5);
      unsigned w = $5->GetValueWidth() + $3;
      ASTNode width = GlobalBeevMgr->CreateBVConst(32,w);
      ASTNode *n =  new ASTNode(GlobalBeevMgr->CreateTerm(BVSX,w,*$5,width));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $5;
    }
| BVZX_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK an_term 
    {
      GlobalBeevMgr->BVTypeCheck(*$5);
      if (0 != $3)
      {
      unsigned w = $5->GetValueWidth() + $3;
	  ASTNode leading_zeroes = GlobalBeevMgr->CreateZeroConst($3);
      ASTNode *n =  new ASTNode(GlobalBeevMgr->CreateTerm(BVCONCAT,w,leading_zeroes,*$5));
      GlobalBeevMgr->BVTypeCheck(*n);
      $$ = n;
      delete $5;
    }
      else
      	$$ = $5;

    }
;
  
sort_symb:
    BITVEC_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK
    {
      // Just return BV width.  If sort is BOOL, width is 0.
      // Otherwise, BITVEC[w] returns w. 
      //
      //((indexwidth is 0) && (valuewidth>0)) iff type is BV
      $$.indexwidth = 0;
      unsigned int length = $3;
      if(length > 0) {
	$$.valuewidth = length;
      }
      else {
	FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
      }
    }
   | ARRAY_TOK LBRACKET_TOK NUMERAL_TOK COLON_TOK NUMERAL_TOK RBRACKET_TOK
    {
      unsigned int index_len = $3;
      unsigned int value_len = $5;
      if(index_len > 0) {
	$$.indexwidth = $3;
      }
      else {
	FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
      }

      if(value_len > 0) {
	$$.valuewidth = $5;
      }
      else {
	FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
      }
    }
;

var:
    FORMID_TOK 
    {
      $$ = new ASTNode(GlobalBeevMgr->ResolveID(*$1)); 
      delete $1;      
    }
   | TERMID_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->ResolveID(*$1));
      delete $1;
    }
   | QUESTION_TOK TERMID_TOK
    {
      $$ = $2;
    }
;

fvar:
    DOLLAR_TOK FORMID_TOK
    {
      $$ = $2; 
    }
  | FORMID_TOK
    {
      $$ = new ASTNode(GlobalBeevMgr->ResolveID(*$1)); 
      delete $1;      
    }   
;
%%
