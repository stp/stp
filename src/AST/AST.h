// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef AST_H
#define AST_H
#include "TopLevel.h"
#include "ASTNode.h"
#include "ASTInternal.h"
#include "ASTInterior.h"
#include "ASTSymbol.h"
#include "ASTBVConst.h"

namespace BEEV
{
  void FatalError(const char * str, const ASTNode& a, int w = 0);
  void FatalError(const char * str);
  void SortByExprNum(ASTVec& c);
  void SortByArith(ASTVec& c);
  bool exprless(const ASTNode n1, const ASTNode n2);
  bool arithless(const ASTNode n1, const ASTNode n2);
  bool isAtomic(Kind k);

  // If (a > b) in the termorder, then return 1 elseif (a < b) in the
  // termorder, then return -1 else return 0
  int TermOrder(const ASTNode& a, const ASTNode& b);
    
  
  //FUNCTION TypeCheck: Assumes that the immediate Children of the
  //input ASTNode have been typechecked. This function is suitable
  //in scenarios like where you are building the ASTNode Tree, and
  //you typecheck as you go along. It is not suitable as a general
  //typechecker
  
  // NB: The boolean value is always true!
  bool BVTypeCheck(const ASTNode& n);
  
  // Checks recursively all the way down.
  bool BVTypeCheckRecursive(const ASTNode& n);

  //Takes a BVCONST and returns its constant value
  unsigned int GetUnsignedConst(const ASTNode n);

  typedef hash_map<
    ASTNode, 
    ASTNode, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeMap;

  typedef hash_map<
    ASTNode, 
    int32_t, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeCountMap;

  typedef hash_set<
    ASTNode, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeSet;

  typedef hash_multiset<
    ASTNode, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeMultiSet;

  typedef hash_map<
    ASTNode, 
    ASTVec, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeToVecMap;

  // Datatype for clauses
  typedef vector<const ASTNode*>* ClausePtr;
  
  // Datatype for Clauselists
  typedef vector<ClausePtr> ClauseList;
  
  // Function to dump contents of ASTNodeMap
  ostream &operator<<(ostream &os, const ASTNodeMap &nmap);
}; // end namespace BEEV
#endif
