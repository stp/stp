#ifndef BBNODE_H_
#define BBNODE_H_

#include "../AST/AST.h"

namespace BEEV {
typedef ASTNode BBNode;

typedef vector<BBNode> BBNodeVec;
typedef vector<vector<BBNode> > BBNodeVecVec;
typedef map<ASTNode, BBNode> BBNodeMap;
typedef map<ASTNode, BBNodeVec> BBNodeVecMap;
typedef set<BBNode> BBNodeSet;
}
;

#endif
