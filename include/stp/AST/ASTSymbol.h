// -*- c++ -*-
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

#ifndef ASTSYMBOL_H
#define ASTSYMBOL_H

#include "stp/Util/StringHash.h"
#include "stp/AST/ASTInternal.h"

namespace stp
{
/******************************************************************
 *  Class to represent internals of Symbol node.                  *
 ******************************************************************/
class ASTSymbol : public ASTInternal
{
  friend class STPMgr;
  friend class ASTNode;
  friend class ASTNodeHasher;
  friend class ASTNodeEqual;

  const static ASTVec empty_children;

private:
  // The name of the symbol
  const char* const _name;

  /****************************************************************
   * Hasher for ASTSymbol nodes                                   *
   ****************************************************************/
  class ASTSymbolHasher
  {
  public:
    size_t operator()(const ASTSymbol* sym_ptr) const
    {
      return CStringHash()(sym_ptr->_name);
    };
  }; 

  /****************************************************************
   * Equality for ASTSymbol nodes                                 *
   ****************************************************************/
  class ASTSymbolEqual
  {
  public:
    bool operator()(const ASTSymbol* sym_ptr1, const ASTSymbol* sym_ptr2) const
    {
      return (*sym_ptr1 == *sym_ptr2);
    }
  };

  friend bool operator==(const ASTSymbol& sym1, const ASTSymbol& sym2)
  {
    return (strcmp(sym1._name, sym2._name) == 0);
  }

  // Get the name of the symbol
  const char* GetName() const;

  // Print function for symbol -- return name. (c_friendly is for
  // printing hex. numbers that C compilers will accept)
  virtual void nodeprint(ostream& os, bool c_friendly = false);

  // Call this when deleting a node that has been stored in the the
  // unique table
  virtual void CleanUp();

public:
  virtual ASTVec const& GetChildren() const { return empty_children; }

  // Constructor.  This does NOT copy its argument.
  ASTSymbol(STPMgr *mgr, const char* const name) : ASTInternal(mgr, SYMBOL), _name(name) {}

  virtual ~ASTSymbol() {}

  // Copy constructor
  ASTSymbol(const ASTSymbol& sym) : ASTInternal(sym.nodeManager, sym._kind), _name(sym._name)
  {
    // printf("inside ASTSymbol constructor %s\n", _name);
  }
};
} // end of namespace
#endif
