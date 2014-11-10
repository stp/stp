/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Mar, 2012
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

#ifndef MISC_H
#define MISC_H

extern const int bits;
extern const int widen_to;

extern Simplifier* simp;

ASTNode widen(const ASTNode& w, int width);

ASTNode create(Kind k, const ASTNode& n0, const ASTNode& n1);

int getDifficulty(const ASTNode& n_);

bool isConstant(const ASTNode& n, VariableAssignment& different,
                const int bits);

vector<ASTNode> getVariables(const ASTNode& n);

ASTNode rewriteThroughWithAIGS(const ASTNode& n_);

#endif
