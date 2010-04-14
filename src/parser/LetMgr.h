// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef LETMGR_H
#define LETMGR_H

#include "../AST/AST.h"
namespace BEEV
{
  //LET Management
  class LETMgr 
  {
  private:

    const ASTNode ASTUndefined;

	// MAP: This map is from bound IDs that occur in LETs to
    // expression. The map is useful in checking replacing the IDs
    // with the corresponding expressions. As soon as the brackets
	// that close a let expression is reached, it is emptied by
    // a call to CleanupLetIDMap().
    ASTNodeMap *_letid_expr_map;

    //Allocate LetID map
    void InitializeLetIDMap(void);

  public:
      
    ASTNodeSet _parser_symbol_table;

    LETMgr(ASTNode undefined)
    : ASTUndefined(undefined)
    {
    	assert(!undefined.IsNull());
    	InitializeLetIDMap();
    }

    ~LETMgr()
    {
      delete _letid_expr_map;
    }

    ASTNode ResolveID(const ASTNode& var);
      
    //Functions that are used to manage LET expressions
    void LetExprMgr(const ASTNode& var, const ASTNode& letExpr);
      
    //Delete Letid Map. Called when we move onto the expression after (let ... )
    void CleanupLetIDMap(void);

    //Substitute Let-vars with LetExprs
    //ASTNode SubstituteLetExpr(ASTNode inExpr);
  };// End of class LETMgr
}; //end of namespace

#endif
