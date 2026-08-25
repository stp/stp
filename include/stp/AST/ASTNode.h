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
#ifndef ASTNODE_H
#define ASTNODE_H

#include <cstdint>

#include "stp/NodeFactory/HashingNodeFactory.h"
#include "stp/Util/Attributes.h"
#include "ASTInternal.h"
#include "stp/Globals/Globals.h"

namespace stp
{
using std::ostream;
class ASTInternal;
class UFContext;

/******************************************************************
 *  A Kind of Smart pointer to actual ASTInternal datastructure.  *
 *  This class defines the node datastructure for the DAG that    *
 *  captures input formulas to STP.                               *
 ******************************************************************/
class ASTNode
{
  friend class STPMgr;
  friend class ASTInterior;
  friend class UFContext;
  friend class vector<ASTNode>;
  friend ASTNode HashingNodeFactory::CreateNode(
      stp::Kind kind, stp::ASTChildren back_children);
  friend bool arithless(const ASTNode& n1, const ASTNode& n2);

  // Ptr to the read data
  ASTInternal* _int_node_ptr;

  // Creates a new pointer, increments refcount of pointed-to object.
  DLL_PUBLIC explicit ASTNode(ASTInternal* in) : _int_node_ptr(in)
  {
    if (in)
    {
      in->IncRef();
    }
  }

  // Equal iff ASTIntNode pointers are the same.
  friend bool operator==(const ASTNode& node1, const ASTNode& node2)
  {
    // Nodes are hash-consed, so the pointer and the node number are in
    // bijection; comparing pointers avoids dereferencing both nodes.
    return (node1._int_node_ptr == node2._int_node_ptr);
  }

  friend bool operator!=(const ASTNode& node1, const ASTNode& node2)
  {
    return !(node1 == node2);
  }

  friend bool operator<(const ASTNode& node1, const ASTNode& node2)
  {
    return (node1.Hash() < node2.Hash());
  }

  STPMgr* GetSTPMgr() const;

public:
  uint8_t getIteration() const;
  void setIteration(uint8_t v) const;

  // Inlined for the same reason as the accessors below: these are among the
  // hottest calls in STP, and the refcount arithmetic is smaller than the
  // call sequence needed to reach it.
  DLL_PUBLIC ASTNode() : _int_node_ptr(NULL){};

  DLL_PUBLIC ASTNode(const ASTNode& n) : _int_node_ptr(n._int_node_ptr)
  {
    if (n._int_node_ptr)
    {
      n._int_node_ptr->IncRef();
    }
  }

  DLL_PUBLIC ~ASTNode()
  {
    if (_int_node_ptr)
    {
      _int_node_ptr->DecRef();
    }
  }

  DLL_PUBLIC ASTNode(ASTNode&& other) noexcept
      : _int_node_ptr(other._int_node_ptr)
  {
    other._int_node_ptr = 0;
  }

  // Print the arguments in lisp format
  friend ostream& LispPrintVec(ostream& os, const ASTVec& v, int indentation);

  // Check if it points to a null node
  inline bool IsNull() const { return _int_node_ptr == NULL; }

  // Public construction APIs use this to reject cross-context operands before
  // asking a node factory to build anything. Node ownership is immutable.
  bool IsOwnedBy(const STPMgr* manager) const
  {
    return !IsNull() && GetSTPMgr() == manager;
  }

  // The owning manager is immutable. Public printers for context-owned
  // durable nodes need to recover their declaration registry without relying
  // on a process-global parser manager.
  STPMgr* GetNodeManager() const
  {
    return IsNull() ? NULL : GetSTPMgr();
  }

  bool isSimplfied() const;
  void hasBeenSimplfied() const;

  bool isConstant() const
  {
    const Kind k = GetKind();
    return k == BVCONST || k == TRUE || k == FALSE;
  }

  bool isAtom() const
  {
    const Kind k = GetKind();
    return k == SYMBOL || isConstant();
  }

  bool isPred() const
  {
    const Kind k = GetKind();
    return k == BVLT || k == BVLE || k == BVGT || k == BVGE || k == BVSLT ||
           k == BVSLE || k == BVSGT || k == BVSGE || k == BVUADDO ||
           k == BVSADDO || k == BVUMULO || k == BVSMULO || k == BVUSUBO ||
           k == BVSSUBO || k == EQ || k == ARRAY_EQ || k == DISTINCT;
  }

  // delegates to the ASTInternal node.
  void nodeprint(ostream& os, bool c_friendly = false) const;

  // Assignment (for ref counting). The IncRef happens before the DecRef so
  // that self-assignment is safe.
  DLL_PUBLIC ASTNode& operator=(const ASTNode& n)
  {
    if (n._int_node_ptr)
      n._int_node_ptr->IncRef();

    if (_int_node_ptr)
      _int_node_ptr->DecRef();

    _int_node_ptr = n._int_node_ptr;
    return *this;
  }

  DLL_PUBLIC ASTNode& operator=(ASTNode&& n)
  {
    if (_int_node_ptr)
      _int_node_ptr->DecRef();

    _int_node_ptr = n._int_node_ptr;

    n._int_node_ptr = 0;
    return *this;
  }

  // Access node number. Inlined: ASTInternal is complete here (its header no
  // longer includes this one), so these fold to direct field reads at the
  // call sites. They are among the hottest calls in STP.
  uint64_t GetNodeNum() const { return _int_node_ptr->GetNodeNum(); }

  // Access kind.
  Kind GetKind() const { return _int_node_ptr->GetKind(); }

  // Access Children of this Node
  ASTChildren GetChildren() const { return _int_node_ptr->GetChildren(); }

  // Return the number of child nodes
  size_t Degree() const { return GetChildren().size(); };

  // Get indexth childNode.
  const ASTNode& operator[](size_t index) const
  {
    return GetChildren()[index];
  };

  // Get begin() iterator for child nodes
  const ASTNode* begin() const { return GetChildren().begin(); };

  // Get end() iterator for child nodes
  const ASTNode* end() const { return GetChildren().end(); };

  // Get back() element for child nodes
  const ASTNode back() const { return GetChildren().back(); };

  // Get the name from a symbol (char *).  It's an error if kind != SYMBOL.
  const char* GetName() const;

  // Get the BVCONST value.
  CBV GetBVConst() const;

  unsigned int GetUnsignedConst() const;

  /*******************************************************************
   * ASTNode is of type BV      <==> ((indexwidth=0)&&(valuewidth>0))*
   * ASTNode is of type ARRAY   <==> ((indexwidth>0)&&(valuewidth>0))*
   * ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))*
   *                                                                 *
   * Both indexwidth and valuewidth should never be less than 0      *
   *******************************************************************/
  // Inlined for the same reason as the ref-counting members: ASTInternal is
  // complete here, so these fold to a single virtual dispatch at the call site
  // instead of a call into the library that then dispatches.
  unsigned int GetIndexWidth() const { return _int_node_ptr->getIndexWidth(); }
  DLL_PUBLIC unsigned int GetValueWidth() const
  {
    // Invariant: a float-formatted node stores its packed width as the value
    // width like any other term (the declaration rules and node builders all
    // maintain this). The format is never the width's only source -- this
    // accessor used to derive sig + exp on every call, solver-wide, to paper
    // over declaration sites that left the value width zero.
    assert(_int_node_ptr->getSigWidth() == 0 ||
           _int_node_ptr->getValueWidth() ==
               _int_node_ptr->getExpWidth() + _int_node_ptr->getSigWidth());
    return _int_node_ptr->getValueWidth();
  }
  void SetIndexWidth(unsigned int iw) const;
  void SetValueWidth(unsigned int vw) const;

  // Reads each width once. The previous form re-read them per branch, which
  // cost up to six dispatches for what is two pieces of information.
  types GetType(void) const
  {
    const unsigned int iw = GetIndexWidth();
    const unsigned int vw = GetValueWidth();

    // Arrays first. An array of floats carries its *element's* format in the
    // exponent and significand widths, so testing those first would call the
    // array itself a float.
    if (iw > 0)
      return (vw > 0) ? ARRAY_TYPE : UNKNOWN_TYPE;

    if (GetSigWidth() != 0 && GetExpWidth() != 0)
      return FLOATINGPOINT_TYPE;

    return (0 == vw) ? BOOLEAN_TYPE : BITVECTOR_TYPE;
  }

  // The immutable source-language sort. This is deliberately separate from
  // GetType(), which remains the packed carrier classification consumed by
  // STP's bit-vector pipeline.
  //
  // Memoised on the node; deriveSourceSort below is the derivation itself and
  // runs at most once per node (see ASTInternal::cachedSourceSort).
  SourceSort GetSourceSort() const;

private:
  // The derivation behind GetSourceSort, without the memo. Private so that
  // nothing reintroduces the recomputation by calling it directly.
  SourceSort deriveSourceSort() const;

public:
  unsigned int GetSigWidth() const;
  unsigned int GetExpWidth() const;

  // Work the floating-point format out from this node's kind and children and
  // remember it. Called on demand by GetExpWidth/GetSigWidth; the format of an
  // interior node is derived rather than assigned, so that rebuilding a node
  // cannot lose it.
  void cacheFPFormat() const;
  void SetSigWidth(unsigned int sw) const;
  void SetExpWidth(unsigned int ew) const;

  // Whether a floating-point format may be *stored* on this node, rather than
  // derived from its kind and children or not carried at all. SetExpWidth
  // asserts on it and FloatBlaster::withFormat -- the funnel that decides
  // where a format goes -- consults it; the rule, and what stamping a node
  // that fails it would do, are with the definition.
  bool canStoreFPFormat() const;

  // Hash is the node's unique id. Inlined: used by every ==/</hash lookup.
  size_t Hash() const { return _int_node_ptr ? _int_node_ptr->node_uid : 0; }

  // Lisp-form printer
  ostream& LispPrint(ostream& os, int indentation = 0) const;
  ostream& LispPrint_indent(ostream& os, int indentation) const;

  // Presentation Language Printer
  ostream& PL_Print(ostream& os, STPMgr* mgr, int indentation = 0) const;
  ostream& PL_Print(ostream& os, int /*indentation = 0*/) const
  {
    return PL_Print(os, GetSTPMgr(), 0);
  }

  // Attempt to define something that will work in the gdb
  friend void lpvec(const ASTVec& vec);

  // Printing to stream
  friend ostream& operator<<(ostream& os, const ASTNode& node)
  {
    node.LispPrint(os, 0);
    return os;
  };

  // Check if NODE really has a good ptr
  bool IsDefined() const { return _int_node_ptr != NULL; }

  /*****************************************************************
   * Hasher class for STL std::unordered_map-s and std::unordered_set-s that use ASTNodes*
   * as keys.  Needs to be public so people can define hash tables *
   * (and use ASTNodeMap class)                                    *
   *****************************************************************/
  class ASTNodeHasher
  {
  public:
    size_t operator()(const ASTNode& n) const
    {
      return n.Hash();
      // return (size_t)n.GetNodeNum();
    };
  };

  /*****************************************************************
   * Equality for ASTNode std::unordered_set and std::unordered_map. Returns true iff  *
   * internal pointers are the same.  Needs to be public so people *
   * can define hash tables (and use ASTNodeSet class)             *
   *****************************************************************/
  class ASTNodeEqual
  {
  public:
    bool operator()(const ASTNode& n1, const ASTNode& n2) const
    {
      return (n1._int_node_ptr == n2._int_node_ptr);
    }
  };
};

} // end of namespace
#endif
