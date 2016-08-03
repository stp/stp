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

#include "stp/AST/ASTInternal.h"
#include "stp/AST/NodeFactory/HashingNodeFactory.h"

namespace stp
{
using std::ostream;

/******************************************************************
 *  A Kind of Smart pointer to actual ASTInternal datastructure.  *
 *  This class defines the node datastructure for the DAG that    *
 *  captures input formulas to STP.                               *
 ******************************************************************/
class ASTNode
{
  friend class STPMgr;
  friend class ASTtoCNF;
  friend class ASTInterior;
  friend class vector<ASTNode>;
  friend ASTNode HashingNodeFactory::CreateNode(const stp::Kind kind,
                                             const ASTVec& back_children);
  friend bool exprless(const ASTNode n1, const ASTNode n2);
  friend bool arithless(const ASTNode n1, const ASTNode n2);

  // Ptr to the read data
  ASTInternal* _int_node_ptr;

  explicit ASTNode(ASTInternal* in);

  // Equal iff ASTIntNode pointers are the same.
  friend bool operator==(const ASTNode& node1, const ASTNode& node2)
  {
    return ((size_t)node1._int_node_ptr) == ((size_t)node2._int_node_ptr);
  }

  friend bool operator!=(const ASTNode& node1, const ASTNode& node2)
  {
    return !(node1 == node2);
  }

  friend bool operator<(const ASTNode& node1, const ASTNode& node2)
  {
    return ((size_t)node1._int_node_ptr) < ((size_t)node2._int_node_ptr);
  }

public:
  /****************************************************************
   * Public Member Functions                                      *
   ****************************************************************/

  uint8_t getIteration() const;
  void setIteration(uint8_t v) const;

  // Default constructor.
  ASTNode() : _int_node_ptr(NULL){};

  // Copy constructor
  ASTNode(const ASTNode& n);

  ~ASTNode();

  // Print the arguments in lisp format
  friend ostream& LispPrintVec(ostream& os, const ASTVec& v, int indentation);

  // Check if it points to a null node
  inline bool IsNull() const { return _int_node_ptr == NULL; }

  bool isSimplfied() const;
  void hasBeenSimplfied() const;

  bool isConstant() const
  {
    const Kind k = GetKind();
    return k == BVCONST || k == TRUE || k == FALSE;
  }

  bool isITE() const
  {
    Kind k = GetKind();
    return k== ITE;
  }

  bool isAtom() const
  {
    const Kind k = GetKind();
    return k == SYMBOL || isConstant();
  }

  bool isPred() const
  {
    const Kind k = GetKind();
    return k == BVLT || k == BVLE || k == BVGT || k == BVGE ||
            k == BVSLT || k == BVSLE || k == BVSGT || k == BVSGE || k == EQ;
  }

  // delegates to the ASTInternal node.
  void nodeprint(ostream& os, bool c_friendly = false) const;

  // Assignment (for ref counting)
  ASTNode& operator=(const ASTNode& n);

  // Access node number
  unsigned GetNodeNum() const;

  // Access kind.
  Kind GetKind() const;

  // Access Children of this Node
  const ASTVec& GetChildren() const;

  // Return the number of child nodes
  size_t Degree() const { return GetChildren().size(); };

  // Get indexth childNode.
  const ASTNode& operator[](size_t index) const
  {
    return GetChildren()[index];
  };

  // Get begin() iterator for child nodes
  ASTVec::const_iterator begin() const { return GetChildren().begin(); };

  // Get end() iterator for child nodes
  ASTVec::const_iterator end() const { return GetChildren().end(); };

  // Get back() element for child nodes
  const ASTNode back() const { return GetChildren().back(); };

  // Get the name from a symbol (char *).  It's an error if kind !=
  // SYMBOL.
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
  unsigned int GetIndexWidth() const;
  unsigned int GetValueWidth() const;
  void SetIndexWidth(unsigned int iw) const;
  void SetValueWidth(unsigned int vw) const;
  types GetType(void) const;

  // Hash using pointer value of _int_node_ptr.
  size_t Hash() const { return (size_t)_int_node_ptr; }

  void NFASTPrint(int l, int max, int prefix) const;

  // Lisp-form printer
  ostream& LispPrint(ostream& os, int indentation = 0) const;
  ostream& LispPrint_indent(ostream& os, int indentation) const;

  // Presentation Language Printer
  ostream& PL_Print(ostream& os , STPMgr *mgr, int indentation = 0) const;

  // Construct let variables for shared subterms
  void LetizeNode(STPMgr* bm) const;

  // Attempt to define something that will work in the gdb
  friend void lp(ASTNode& node);
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
      return (size_t)n._int_node_ptr;
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
