// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Mar 24, 2011
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

#ifndef ASTINTERNALWithChildren_H
#define ASTINTERNALWithChildren_H

/*
 * Leaf objects like Symbols and BVConsts don't need a vector of
 * children. On a 64-bit machine, a vector object is 24 bytes. So
 * splitting the two objects apart saves 24 bytes for those objects.
 */

namespace BEEV
{
class ASTInternalWithChildren : public ASTInternal
{

protected:
  // The vector of children
  ASTVec _children;

  /// todo. This should be a bitfield in a superclass if it can fit without
  /// increasing the sizeof..
  mutable bool is_simplified;

public:
  virtual ASTVec const& GetChildren() const { return _children; }

  bool isSimplified() const { return is_simplified; }

  void hasBeenSimplified() const { is_simplified = true; }

  // Constructor (kind and children).
  ASTInternalWithChildren(Kind kind, const ASTVec& children, int nodenum = 0)
      : ASTInternal(kind, nodenum), _children(children)
  {
    is_simplified = false;
  }

  // Constructor (kind only, empty children, int nodenum)
  ASTInternalWithChildren(Kind kind, int nodenum = 0)
      : ASTInternal(kind, nodenum)
  {
    is_simplified = false;
  }
}; // End of Class ASTInternalBase
} // end of namespace
#endif
