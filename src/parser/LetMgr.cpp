// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <stdlib.h>
#include "LetMgr.h"

namespace BEEV {
  // FUNC: This function maintains a map between LET-var names and
  // LET-expressions
  //
  //1. if the Let-var is already defined in the LET scope, then the
  //1. function returns an error.
  //
  //2. if the Let-var is already declared variable in the input, then
  //2. the function returns an error
  //
  //3. otherwise add the <var,letExpr> pair to the _letid_expr table.
  void LETMgr::LetExprMgr(const ASTNode& var, const ASTNode& letExpr) 
  {
	  ASTNodeMap::iterator it;
    if(((it = _letid_expr_map->find(var)) != _letid_expr_map->end()) && 
       it->second != ASTUndefined) {      
      FatalError("LetExprMgr:The LET-var v has already been defined"\
                 "in this LET scope: v =", var);
    }

    if(_parser_symbol_table.find(var) != _parser_symbol_table.end()) {
      FatalError("LetExprMgr:This var is already declared. "\
                 "cannot redeclare as a letvar: v =", var);
    }

    (*_letid_expr_map)[var] = letExpr;
  }//end of LetExprMgr()

  //this function looksup the "var to letexpr map" and returns the
  //corresponding letexpr. if there is no letexpr, then it simply
  //returns the var.
  ASTNode LETMgr::ResolveID(const ASTNode& v) 
  {
	if (v.GetKind() != SYMBOL) {
      return v;
    }

    if(_parser_symbol_table.find(v) != _parser_symbol_table.end()) {
      return v;
    }

    ASTNodeMap::iterator it;
    if((it =_letid_expr_map->find(v)) != _letid_expr_map->end()) {
      if(it->second == ASTUndefined) 
        FatalError("ResolveID :: Unresolved Identifier: ",v);
      else
        return it->second;
    }

    //this is to mark the let-var as undefined. the let var is defined
    //only after the LetExprMgr has completed its work, and until then
    //'v' is undefined. 
    //
    //declared variables also get stored in this map, but there value
    //is ASTUndefined. This is really a hack. I don't know how to get
    //rid of this hack.
    (*_letid_expr_map)[v] = ASTUndefined;
    return v;    
  }//End of ResolveID()
  
  // This function simply cleans up the LetID -> LetExpr Map.   
  void LETMgr::CleanupLetIDMap(void) 
  { 
    // ext/hash_map::clear() is very expensive on big empty maps. shortcut.
    if (_letid_expr_map->size()  ==0)
      return;


    // I don't know what this does. Commenting it out and all the regression
    // tests still pass.
#if 0
    ASTNodeMap::iterator it = _letid_expr_map->begin();
    ASTNodeMap::iterator itend = _letid_expr_map->end();
    for(;it!=itend;it++) {
      if(it->second != ASTUndefined) {
        it->first.SetValueWidth(0);
        it->first.SetIndexWidth(0);
      }
    }
#endif

    // May contain lots of buckets, so reset.
    delete _letid_expr_map;
    InitializeLetIDMap();
  }//end of CleanupLetIDMap()

  void LETMgr::InitializeLetIDMap(void)
  {
    _letid_expr_map = new ASTNodeMap();
  } //end of InitializeLetIDMap()
};
