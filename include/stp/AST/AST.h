/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
 *
 * BEGIN DATE: November, 2005
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#ifndef AST_H
#define AST_H

#include "UsefulDefs.h"
#include "ASTNode.h"


namespace stp
{
void FatalError(const char* str, const ASTNode& a, int w = 0)
                __attribute__((noreturn));
void FatalError(const char* str) __attribute__((noreturn));
void SortByExprNum(ASTVec& c);
void SortByArith(ASTVec& c);
bool exprless(const ASTNode n1, const ASTNode n2);
bool arithless(const ASTNode n1, const ASTNode n2);
bool isAtomic(Kind k);
bool isCommutative(const Kind k);
bool containsArrayOps(const ASTNode& n, STPMgr *stp);
bool numberOfReadsLessThan(const ASTNode& n, int v);

// If (a > b) in the termorder, then return 1 elseif (a < b) in the
// termorder, then return -1 else return 0
int TermOrder(const ASTNode& a, const ASTNode& b);

// FUNCTION TypeCheck: Assumes that the immediate Children of the
// input ASTNode have been typechecked. This function is suitable
// in scenarios like where you are building the ASTNode Tree, and
// you typecheck as you go along. It is not suitable as a general
// typechecker

// NB: The boolean value is always true!
bool BVTypeCheck(const ASTNode& n);

long getCurrentTime();

ASTVec FlattenKind(Kind k, const ASTVec& children);

// Checks recursively all the way down.
bool BVTypeCheckRecursive(const ASTNode& n);

// Takes a BVCONST and returns its constant value
unsigned int GetUnsignedConst(const ASTNode n);

typedef hash_map<ASTNode, ASTNode, ASTNode::ASTNodeHasher,
                 ASTNode::ASTNodeEqual> ASTNodeMap;

typedef hash_map<ASTNode, int32_t, ASTNode::ASTNodeHasher,
                 ASTNode::ASTNodeEqual> ASTNodeCountMap;

typedef hash_set<ASTNode, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
    ASTNodeSet;

typedef hash_multiset<ASTNode, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
    ASTNodeMultiSet;

typedef hash_map<ASTNode, ASTVec, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual>
    ASTNodeToVecMap;

void FlattenKindNoDuplicates(const Kind k, const ASTVec& children,
                             ASTVec& flat_children,
                             ASTNodeSet& alreadyFlattened);

// Needed for defining the MAP below
struct ltint
{
  bool operator()(int s1, int s2) const { return s1 < s2; }
};

class ClauseList;

// Datatype for ClauseLists
typedef std::map<int, ClauseList*, ltint> ClauseBuckets;

typedef std::map<int, ASTVec*, ltint> IntToASTVecMap;

// Function to dump contents of ASTNodeMap
ostream& operator<<(ostream& os, const ASTNodeMap& nmap);

void buildListOfSymbols(const ASTNode& n, ASTNodeSet& visited,
                        ASTNodeSet& symbols);
} // end namespace stp

#endif
