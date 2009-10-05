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
#include "ASTInternal.h"
#include "ASTInterior.h"
#include "ASTNode.h"
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
  
  // Function to dump contents of ASTNodeMap
  ostream &operator<<(ostream &os, const ASTNodeMap &nmap);
}; // end namespace BEEV
#endif
