/***************************
 * Authors: Michael Katelman, Tervor Hansen, Vijay Ganesh
 *
 * Start date: Oct, 2008
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

#include "../AST.h"

using namespace BEEV;

int main()
{
  const int size = 1;

  BeevMgr *bm = new BeevMgr();
  ASTNode s1 = bm->CreateSymbol("x");
  s1.SetValueWidth(size);

  cout << "s1" << s1 << endl;
  ASTNode s2 = bm->CreateSymbol("y");
  s2.SetValueWidth(size);

  cout << "s2" << s2 << endl;
  ASTNode s3 = bm->CreateSymbol("z");
  s3.SetValueWidth(size);

  cout << "s3" << s3 << endl;

  ASTNode bbs1 = bm->BBForm(s1);
  cout << "bitblasted s1" << endl << bbs1 << endl;
  bm->PrintClauseList(cout, bm->ToCNF(bbs1));

  ASTNode a2 = bm->CreateNode(AND, s1, s2);
  ASTNode bba2 = bm->BBForm(a2);
  cout << "bitblasted a2" << endl << bba2 << endl;
  bm->PrintClauseList(cout, bm->ToCNF(bba2));

  ASTNode a3 = bm->CreateNode(OR, s1, s2);
  ASTNode bba3 = bm->BBForm(a3);
  cout << "bitblasted a3" << endl << bba3 << endl;
  bm->PrintClauseList(cout, bm->ToCNF(bba3));

  ASTNode a4 = bm->CreateNode(EQ, s1, s2);
  ASTNode bba4 = bm->BBForm(a4);
  cout << "bitblasted a4 " << endl << bba4 << endl;

  bm->PrintClauseList(cout, bm->ToCNF(bba4));

}
