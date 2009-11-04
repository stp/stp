// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef LET_H
#define LET_H

#include "../AST/AST.h"
namespace BEEV
{
  //LET Management
  class LETMgr 
  {
  private:

    // MAP: This map is from bound IDs that occur in LETs to
    // expression. The map is useful in checking replacing the IDs
    // with the corresponding expressions.
    ASTNodeMap *_letid_expr_map;
    ASTNode ASTUndefined;
      
  public:
      
    LETMgr(ASTNode undefined)
    {
      _letid_expr_map = new ASTNodeMap();
      ASTUndefined = undefined;
    }

    ~LETMgr()
       {
         delete _letid_expr_map;
       }

    ASTNode ResolveID(const ASTNode& var);
      
    //Functions that are used to manage LET expressions
    void LetExprMgr(const ASTNode& var, const ASTNode& letExpr);
      
    //Delete Letid Map
    void CleanupLetIDMap(void);
      
    //Allocate LetID map
    void InitializeLetIDMap(void);
      
    //Substitute Let-vars with LetExprs
    ASTNode SubstituteLetExpr(ASTNode inExpr);
  };// End of class LETMgr
}; //end of namespace

#endif
