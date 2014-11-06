// -*- c++ -*-
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

  BeevMgr * bm = new BeevMgr();
  ASTNode s1 = bm->CreateSymbol("foo");
  s1 = bm->CreateSymbol("foo1");
  s1 = bm->CreateSymbol("foo2");
  ASTNode s2 = bm->CreateSymbol("bar");
  cout << "s1" << s1 << endl;
  cout << "s2" << s2 << endl;

  ASTNode b1 = bm->CreateBVConst(5, 12);
  ASTNode b2 = bm->CreateBVConst(6, 36);
  cout << "b1: " << b1 << endl;
  cout << "b2: " << b2 << endl;

  ASTNode a1 = bm->CreateNode(EQ, s1, s2);
  ASTNode a2 = bm->CreateNode(AND, s1, s2);
  a1 = bm->CreateNode(OR, s1, s2);
  ASTNode a3 = bm->CreateNode(IMPLIES, a1, a2);
  ASTNode a4 = bm->CreateNode(IMPLIES, s1, a2);
  cout << "a3" << a3 << endl;
  cout << "a4" << a4 << endl;
  return 0;
}
