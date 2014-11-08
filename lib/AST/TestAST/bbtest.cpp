/********************************************************************
 * AUTHORS: Unknown
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

#include "../AST.h"

using namespace BEEV;

int main()
{
  const int size = 32;

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

  ASTNode c1 = bm->CreateBVConst(size, 0);
  cout << "c1" << c1 << endl;
  ASTVec bbc1 = bm->BBTerm(c1);
  cout << "bitblasted c1 " << endl;
  LispPrintVec(cout, bbc1, 0);
  cout << endl;

  ASTNode c2 = bm->CreateBVConst(size, 1);
  c2.SetValueWidth(size);
  cout << "c2" << c2 << endl;
  ASTVec bbc2 = bm->BBTerm(c2);
  cout << "bitblasted c2 " << endl;
  LispPrintVec(cout, bbc2, 0);
  cout << endl;

  ASTNode c3 = bm->CreateBVConst(size, 0xFFFFFFFF);
  c3.SetValueWidth(size);
  cout << "c3" << c3 << endl;
  ASTVec bbc3 = bm->BBTerm(c3);
  cout << "bitblasted c3 " << endl;
  LispPrintVec(cout, bbc3, 0);
  cout << endl;

  ASTNode c4 = bm->CreateBVConst(size, 0xAAAAAAAA);
  c4.SetValueWidth(size);
  cout << "c4" << c4 << endl;
  ASTVec bbc4 = bm->BBTerm(c4);
  cout << "bitblasted c4 " << endl;
  LispPrintVec(cout, bbc4, 0);
  cout << endl;

  //   ASTNode b1 = bm->CreateBVConst(12);
  //   ASTNode b2 = bm->CreateBVConst(36);
  //   cout << "b1: " <<  b1 << endl;
  //   cout << "b2: " <<  b2 << endl;

  ASTNode a1 = bm->CreateNode(BVPLUS, s1, s2);
  a1.SetValueWidth(size);

  ASTVec& bba1 = bm->BBTerm(a1);
  cout << "bitblasted a1 " << endl;
  LispPrintVec(cout, bba1, 0);
  cout << endl;

  ASTNode a2 = bm->CreateNode(BVPLUS, s1, s2, s3);
  a1.SetValueWidth(2);

  ASTVec& bba2 = bm->BBTerm(a2);
  cout << "bitblasted a2 " << endl;
  LispPrintVec(cout, bba2, 0);
  cout << endl;

  ASTNode a3 = bm->CreateNode(BVXOR, s1, s2);
  a3.SetValueWidth(2);

  ASTVec& bba3 = bm->BBTerm(a3);
  cout << "bitblasted a3 " << endl;
  LispPrintVec(cout, bba3, 0);
  cout << endl;

  ASTNode a4 = bm->CreateNode(EQ, s1, s2);
  ASTNode bba4 = bm->BBForm(a4);
  cout << "bitblasted a4 " << endl << bba4 << endl;

  ASTNode a5 = bm->CreateNode(BVLE, s1, s2);
  ASTNode bba5 = bm->BBForm(a5);
  cout << "bitblasted a5 " << endl << bba5 << endl;

  return 0;
}
