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

#include "stp/config.h"
#include "stp/AST/ASTInternal.h"
#include "stp/Util/StringHash.h"

namespace stp
{
/******************************************************************
 *  Class to represent internals of Symbol node.                  *
 ******************************************************************/
class ASTSymbol : public ASTInternal
{
  friend class STPMgr;
  friend class ASTNode;

  const static ASTVec empty_children;

private:
  // The name of the symbol
  const char* const _name;
  // Manager-minted symbols occupy a separate identity domain even when a
  // low-level API caller deliberately chooses the same spelling and sort.
  // `false` contributes no hash bits, preserving every historical user
  // symbol hash and equality result.
  const bool _internal_identity;

  /****************************************************************
   * Hasher for ASTSymbol nodes                                   *
   ****************************************************************/
  class ASTSymbolHasher
  {
  public:
    size_t operator()(const ASTSymbol* sym_ptr) const
    {
      return CStringHash()(sym_ptr->_name) ^
             static_cast<size_t>(sym_ptr->_source_sort.hash() *
                                 0x9e3779b97f4a7c15ULL)
             ^
             (sym_ptr->_internal_identity
                  ? static_cast<size_t>(0xd6e8feb86659fd93ULL)
                  : static_cast<size_t>(0))
          ;
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
    return strcmp(sym1._name, sym2._name) == 0 &&
           sym1._source_sort == sym2._source_sort
           && sym1._internal_identity == sym2._internal_identity
        ;
  }

  // Get the name of the symbol
  const char* GetName() const;

  // Print function for symbol -- return name. (c_friendly is for
  // printing hex. numbers that C compilers will accept)
  void nodeprint(ostream& os, bool c_friendly = false) override;

  // Call this when deleting a node that has been stored in the the
  // unique table
  void CleanUp() override;

  uint32_t _value_width;
  uint32_t _index_width;

  uint32_t _sig_width;
  uint32_t _exp_width;

  // Fixed at construction for typed source symbols. Legacy internal symbols
  // retain Unknown and may use the historical width setters.
  const SourceSort _source_sort;

  void setIndexWidth(uint32_t i) override
  {
    if (_source_sort.isKnown())
    {
      assert(i == _index_width);
      return;
    }
    _index_width = i;
  }
  uint32_t getIndexWidth() const override { return _index_width; }

  void setValueWidth(uint32_t v) override
  {
    if (_source_sort.isKnown())
    {
      assert(v == _value_width);
      return;
    }
    _value_width = v;
  }
  uint32_t getValueWidth() const override { return _value_width; }

  void setSigWidth(uint32_t sw) override
  {
    if (_source_sort.isKnown())
    {
      assert(sw == _sig_width);
      return;
    }
    _sig_width = sw;
  }
  uint32_t getSigWidth() const override { return _sig_width; }

  void setExpWidth(uint32_t ew) override
  {
    if (_source_sort.isKnown())
    {
      assert(ew == _exp_width);
      return;
    }
    _exp_width = ew;
  }
  uint32_t getExpWidth() const override { return _exp_width; }

  SourceSort getDeclaredSourceSort() const override { return _source_sort; }

public:
  ASTChildren GetChildren() const override { return empty_children; }

  // Constructor.  This does NOT copy its argument.
  ASTSymbol(STPMgr* mgr, const char* const name)
      : ASTInternal(mgr, SYMBOL), _name(name),
        _internal_identity(false),
        _value_width(0), _index_width(0), _sig_width(0), _exp_width(0),
        _source_sort(SourceSort::unknown())
  {
  }

  ASTSymbol(STPMgr* mgr, const char* const name, const SourceSort& source_sort)
      : ASTSymbol(mgr, name, source_sort, false)
  {
  }

private:
  ASTSymbol(STPMgr* mgr, const char* const name,
            const SourceSort& source_sort, bool internal_identity)
      : ASTInternal(mgr, SYMBOL), _name(name),
        _internal_identity(internal_identity), _value_width(0),
        _index_width(0), _sig_width(0), _exp_width(0),
        _source_sort(source_sort)
  {
    switch (_source_sort.kind())
    {
      case SourceSort::Kind::Bool:
        break;
      case SourceSort::Kind::BitVector:
        _value_width = _source_sort.bitVectorWidth();
        break;
      case SourceSort::Kind::FloatingPoint:
        _exp_width = _source_sort.exponentWidth();
        _sig_width = _source_sort.significandWidth();
        _value_width = _source_sort.packedWidth();
        break;
      case SourceSort::Kind::RoundingMode:
        _value_width = _source_sort.packedWidth();
        break;
      case SourceSort::Kind::Uninterpreted:
        // The declared sort retains its identity at the source boundary while
        // its finite carrier uses the exact upstream packed width below it.
        _value_width = _source_sort.packedWidth();
        break;
      case SourceSort::Kind::Real:
        // Mathematical Real has no packed carrier width.  Its source sort is
        // immutable identity and ASTNode::GetType classifies it before the
        // legacy width-based path.
        break;
      case SourceSort::Kind::Array:
        _index_width = _source_sort.index().packedWidth();
        _value_width = _source_sort.element().packedWidth();
        if (_source_sort.element().kind() ==
            SourceSort::Kind::FloatingPoint)
        {
          _exp_width = _source_sort.element().exponentWidth();
          _sig_width = _source_sort.element().significandWidth();
        }
        break;
      case SourceSort::Kind::Unknown:
        break;
    }
  }

public:
  virtual ~ASTSymbol() {}

  // Copy constructor
  ASTSymbol(const ASTSymbol& sym)
      : ASTInternal(sym.nodeManager, sym._kind), _name(sym._name),
        _internal_identity(sym._internal_identity),
        _value_width(sym._value_width), _index_width(sym._index_width),
        _sig_width(sym._sig_width), _exp_width(sym._exp_width),
        _source_sort(sym._source_sort)
  {
    // printf("inside ASTSymbol constructor %s\n", _name);
  }
};
} // end of namespace
#endif
