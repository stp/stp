#ifndef MISC_H
#define MISC_H

extern const int bits;
extern const int widen_to;

extern Simplifier *simp;

ASTNode
widen(const ASTNode& w, int width);

ASTNode
create(Kind k, const ASTNode& n0, const ASTNode& n1);

int
getDifficulty(const ASTNode& n_);

bool
isConstant(const ASTNode& n, VariableAssignment& different, const int bits);

vector<ASTNode>
getVariables(const ASTNode& n);

ASTNode
rewriteThroughWithAIGS(const ASTNode &n_);

#endif
