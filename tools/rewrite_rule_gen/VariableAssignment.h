/********************************************************************
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

#ifndef VARIABLEASSIGNMENT_H_
#define VARIABLEASSIGNMENT_H_

// A pair of constants of the same bit-width assigned to v and w..

struct VariableAssignment
{
private:
  ASTNode v;
  ASTNode w;
  bool empty;

public:
  ASTNode getV() const
  {
    assert(!empty);
    return v;
  }

  ASTNode getW() const
  {
    assert(!empty);
    return w;
  }

  void setValues(const ASTNode& nv, const ASTNode& nw)
  {
    assert(nv.isConstant());
    assert(nw.isConstant());
    assert(nw.GetValueWidth() == nv.GetValueWidth());
    w = nw;
    v = nv;
    empty = false;
  }

  VariableAssignment() { empty = true; }
};

#endif
