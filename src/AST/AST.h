// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef AST_H
#define AST_H

#include <vector>
#ifdef EXT_HASH_MAP
#include <ext/hash_set>
#include <ext/hash_map>
#elif defined(TR1_UNORDERED_MAP)
#include <tr1/unordered_map>
#include <tr1/unordered_set>
#define hash_map tr1::unordered_map
#define hash_set tr1::unordered_set
#define hash_multiset tr1::unordered_multiset
#else
#include <hash_set>
#include <hash_map>
#endif
#include <iostream>
#include <sstream>
#include <string>
#include <map>
#include <set>
#include <algorithm>
#include "../main/Globals.h"
#include "ASTUtil.h"
#include "ASTKind.h"
#include <stdint.h>
#include <stdlib.h>
#include "../extlib-constbv/constantbv.h"
#include "RunTimes.h"

/*****************************************************************************
 * LIST OF CLASSES DECLARED IN THIS FILE:
 *
 * class BeevMgr;
 * class ASTNode;
 * class ASTInternal;
 * class ASTInterior;
 * class ASTSymbol;
 * class ASTBVConst;
 *****************************************************************************/
namespace BEEV
{
  using namespace std;
  using namespace MINISAT;
#ifdef EXT_HASH_MAP
  using namespace __gnu_cxx;
#endif

  class BeevMgr;
  class ASTNode;
  class ASTInternal;
  class ASTInterior;
  class ASTSymbol;
  class ASTBVConst;
  class BVSolver;


  template <class E, class T>
  struct enumeration
  {
    typedef T type;
    typedef E enum_type;

    enumeration()
      : e_(E())
    {}
    
    enumeration(E e)
      : e_(static_cast<T>(e))
    {}
    
    operator E() const
    { return static_cast<E>(e_); }
    
  private:
    T e_;
  };

  //Useful typedefs: Vector of ASTNodes, used for child nodes among
  //other things.
  typedef vector<ASTNode> ASTVec;
  typedef unsigned int * CBV;
  extern ASTVec _empty_ASTVec;
  /***************************************************************************/
  /*  Class ASTNode: Smart pointer to actual ASTNode internal datastructure. */
  /***************************************************************************/
  class ASTNode
  {
    friend class BeevMgr;
    friend class CNFMgr;
    friend class ASTInterior;
    friend class vector<ASTNode>;
    //Print the arguments in lisp format.
    friend ostream &LispPrintVec(ostream &os, 
                                 const ASTVec &v, 
                                 int indentation = 0);
    friend ostream &LispPrintVecSpecial(ostream &os, 
                                        const vector<const ASTNode*> &v, 
                                        int indentation = 0);

  private:
    ASTInternal * _int_node_ptr; // The real data.

    // Usual constructor.
    ASTNode(ASTInternal *in);

    //Integer that helps sort the ASTNodes. This sorting is different
    //from the sorting based on NodeNum. This is used as a way of
    //achieving abstraction-refinement.
    //unsigned int _sort_for_absrefine;

    //Equal iff ASTIntNode pointers are the same.
    friend bool operator==(const ASTNode node1, const ASTNode node2)
    {
      return ((size_t) node1._int_node_ptr) == ((size_t) node2._int_node_ptr);
    }

    //MKK: This shouldn't be necessary, but for some inexplicable reason I
    //cannot get ToSAT.cpp to compile. The differences between the old files
    //(AST.h, ToSAT.cpp) and the new files are very minor, mostly Solver ->
    //Solver, and so the compiler errors are difficult to understand.
    friend bool operator!=(const ASTNode node1, const ASTNode node2)
    {
      return !(node1 == node2);
      //return ((size_t) node1._int_node_ptr) == ((size_t) node2._int_node_ptr);
    }

    /* FIXME:  Nondeterministic code *** */
    /** questionable pointer comparison function */
    friend bool operator<(const ASTNode node1, const ASTNode node2)
    {
      return ((size_t) node1._int_node_ptr) < ((size_t) node2._int_node_ptr);
    }

  public:
    //     //Set the sorting integer for abstraction refinement
    //     void SetAbsRefineInt(unsigned int a) {_sort_for_absrefine = a;}
    
    //     //Get the sorting integer for abstraction refinement
    //     unsigned int GetAbsRefineInt(void) {return _sort_for_absrefine;}
    
    //     //Compare two ASTNodes based on their abstraction refinement
    //     //number
    //     bool CmpAbsRefine(const ASTNode node1, const ASTNode node2) {
    //       return (node1._sort_for_absrefine < node2._sort_for_absrefine);
    //     }
    
    //Check if it points to a null node
    bool IsNull() const
    {
      return _int_node_ptr == NULL;
    }

    // This is for sorting by expression number (used in Boolean
    //optimization).
    // With any ordering operation, the properties of the order
    // need to be carefully specified.  In this case, we just
    // need identical exprs to be consecutive, and (NOT x) to
    // follow "x" immediately.  For some time, this function was
    // "arithless" (below), which separates x and (NOT x) in some
    // cases.
    // DO NOT MODIFY WITHOUT CHECKING WITH DAVID DILL FIRST!
    friend bool exprless(const ASTNode n1, const ASTNode n2)
    {
      return (n1.GetNodeNum() < n2.GetNodeNum());
    } // end of exprless

    // This is for sorting by arithmetic expressions (for
    // combining like terms, etc.)
    friend bool arithless(const ASTNode n1, const ASTNode n2)
    {
      Kind k1 = n1.GetKind();
      Kind k2 = n2.GetKind();

      if (n1 == n2)
        {
          // necessary for "strict weak ordering"
          return false;
        }
      else if (BVCONST == k1 && BVCONST != k2)
        {
          // put consts first
          return true;
        }
      else if (BVCONST != k1 && BVCONST == k2)
        {
          // put consts first
          return false;
        }
      else if (SYMBOL == k1 && SYMBOL != k2)
        {
          // put symbols next
          return true;
        }
      else if (SYMBOL != k1 && SYMBOL == k2)
        {
          // put symbols next
          return false;
        }
      else
        {
          // otherwise, sort by exprnum (descendents will appear
          // before ancestors).
          return (n1.GetNodeNum() < n2.GetNodeNum());
        }
    } //end of arithless

    // For lisp DAG printing.  Has it been printed already, so we can
    // just print the node number?
    bool IsAlreadyPrinted() const;
    void MarkAlreadyPrinted() const;

    // delegates to the ASTInternal node.
    void nodeprint(ostream& os, bool c_friendly = false) const;

  public:
    // Default constructor.  This gets used when declaring an ASTVec
    // of a given size, in the hash table, etc.  For faster
    // refcounting, create a symbol node for NULL.  Give it a big
    // initial refcount.  Never free it.  also check, for ref-count
    // overflow?
    ASTNode() :
      _int_node_ptr(NULL)
    {
      //_sort_for_absrefine=0;
    }
    ;

    // Copy constructor
    ASTNode(const ASTNode &n);

    // Destructor
    ~ASTNode();

    // Assignment (for ref counting)
    ASTNode& operator=(const ASTNode& n);

    BeevMgr &GetBeevMgr() const;

    // Access node number
    int GetNodeNum() const;

    // Access kind.  Inlined later because of declaration ordering problems.
    Kind GetKind() const;

    // access Children
    const ASTVec &GetChildren() const;

    // Return the number of child nodes
    size_t Degree() const
    {
      return GetChildren().size();
    }
    ;

    // Get indexth childNode.
    const ASTNode operator[](size_t index) const
    {
      return GetChildren()[index];
    }
    ;

    // Get begin() iterator for child nodes
    ASTVec::const_iterator begin() const
    {
      return GetChildren().begin();
    }
    ;

    // Get end() iterator for child nodes
    ASTVec::const_iterator end() const
    {
      return GetChildren().end();
    }
    ;

    //Get back() element for child nodes
    const ASTNode back() const
    {
      return GetChildren().back();
    }
    ;

    // Get the name from a symbol (char *).  It's an error if kind != SYMBOL
    // The result should be treated as const.
    const char * /**const**/ GetName() const;

    //Get the BVCONST value
    // The result should be treated as const.
    /*const*/ CBV GetBVConst() const;

    /*ASTNode is of type BV <==> ((indexwidth=0)&&(valuewidth>0))
     *
     *ASTNode is of type ARRAY <==> ((indexwidth>0)&&(valuewidth>0))
     *
     *ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))
     *
     *both indexwidth and valuewidth should never be less than 0
     */
    unsigned int GetIndexWidth() const;
    void SetIndexWidth(unsigned int iw) const;

    unsigned int GetValueWidth() const;
    void SetValueWidth(unsigned int vw) const;

    //return the type of the ASTNode
    //0 iff BOOLEAN
    //1 iff BITVECTOR
    //2 iff ARRAY

    /*ASTNode is of type BV <==> ((indexwidth=0)&&(valuewidth>0))
     *
     *ASTNode is of type ARRAY <==> ((indexwidth>0)&&(valuewidth>0))
     *
     *ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))
     *
     *both indexwidth and valuewidth should never be less than 0
     */
    types GetType(void) const;

    // Hash is pointer value of _int_node_ptr.
    /* const */ size_t Hash() const
    {
      return (size_t) _int_node_ptr;
      //return GetNodeNum();
    }

    void NFASTPrint(int l, int max, int prefix) const;

    // lisp-form printer
    ostream& LispPrint(ostream &os, int indentation = 0) const;
    ostream &LispPrint_indent(ostream &os, int indentation) const;

    //Presentation Language Printer
    ostream& PL_Print(ostream &os, int indentation = 0) const;

    //Construct let variables for shared subterms
    void LetizeNode(void) const;

    // Attempt to define something that will work in the gdb
    friend void lp(ASTNode &node);
    friend void lpvec(const ASTVec &vec);

    friend ostream &operator<<(ostream &os, const ASTNode &node)
    {
      node.LispPrint(os, 0);
      return os;
    }
    ;

    // Check whether the ASTNode points to anything.  Undefined nodes
    // are created by the default constructor.  In binding table (for
    // lambda args, etc.), undefined nodes are used to represent
    // deleted entries.
    bool IsDefined() const
    {
      return _int_node_ptr != NULL;
    }

    /* Hasher class for STL hash_maps and hash_sets that use ASTNodes
     * as keys.  Needs to be public so people can define hash tables
     * (and use ASTNodeMap class)*/
    class ASTNodeHasher
    {
    public:
      size_t operator()(const ASTNode& n) const
      {
        return (size_t) n._int_node_ptr;
        //return (size_t)n.GetNodeNum();
      }
      ;
    }; //End of ASTNodeHasher

    /* Equality for ASTNode hash_set and hash_map. Returns true iff
     * internal pointers are the same.  Needs to be public so people
     * can define hash tables (and use ASTNodeSet class)*/
    class ASTNodeEqual
    {
    public:
      bool operator()(const ASTNode& n1, const ASTNode& n2) const
      {
        return (n1._int_node_ptr == n2._int_node_ptr);
      }
    }; //End of ASTNodeEqual
  }; //End of Class ASTNode

  void FatalError(const char * str, const ASTNode& a, int w = 0);
  void FatalError(const char * str);
  void SortByExprNum(ASTVec& c);
  void SortByArith(ASTVec& c);
  bool exprless(const ASTNode n1, const ASTNode n2);
  bool arithless(const ASTNode n1, const ASTNode n2);
  bool isAtomic(Kind k);

  /***************************************************************************/
  /*  Class ASTInternal:Abstract base class for internal node representation.*/
  /*                    Requires Kind and ChildNodes so same traversal works */
  /*                    on all nodes.                                        */
  /***************************************************************************/
  class ASTInternal
  {

    friend class ASTNode;
    friend class CNFMgr;

  protected:

    // reference count.
    int _ref_count;

    // Kind.  It's a type tag and the operator.
    //Kind _kind;
    enumeration<Kind,unsigned char> _kind;

    // The vector of children (*** should this be in ASTInterior? ***)
    ASTVec _children;

    // Manager object.  Having this backpointer means it's easy to
    // find the manager when we need it.
    BeevMgr &_bm;

    //Nodenum is a unique positive integer for the node.  The nodenum
    //of a node should always be greater than its descendents (which
    //is easily achieved by incrementing the number each time a new
    //node is created).
    int _node_num;

    // Length of bitvector type for array index.  The term is an
    // array iff this is positive.  Otherwise, the term is a bitvector
    // or a bit.
    unsigned short _index_width;

    // Length of bitvector type for scalar value or array element.
    // If this is one, the term represents a single bit (same as a bitvector
    // of length 1).  It must be 1 or greater.
    unsigned short _value_width;

    // Increment refcount.
    void IncRef()
    {
      ++_ref_count;
    }

    // DecRef is a potentially expensive, because it has to delete
    // the node from the unique table, in addition to freeing it.
    // FIXME:  Consider putting in a backpointer (iterator) to the hash
    // table entry so it can be deleted without looking it up again.
    void DecRef();

    // Treat the result as const pleases
    virtual /**const**/ Kind GetKind() const
    {
      return _kind;
    }

    virtual ASTVec const &GetChildren() const
    {
      return _children;
    }

    int GetNodeNum() const
    {
      return _node_num;
    }

    void SetNodeNum(int nn)
    {
      _node_num = nn;
    }
    ;

    // Constructor (bm only)
    ASTInternal(BeevMgr &bm, int nodenum = 0) :
      _ref_count(0), _kind(UNDEFINED), _bm(bm), 
      _node_num(nodenum), _index_width(0), _value_width(0)
    {
    }

    // Constructor (kind only, empty children, int nodenum)
    ASTInternal(Kind kind, BeevMgr &bm, int nodenum = 0) :
      _ref_count(0), _kind(kind), _bm(bm), 
      _node_num(nodenum), _index_width(0), _value_width(0)
    {
    }

    // Constructor (kind and children).  This copies the contents of
    // the child nodes.
    // FIXME: is there a way to avoid repeating these?
    ASTInternal(Kind kind, const ASTVec &children, BeevMgr &bm, int nodenum = 0) :
      _ref_count(0), _kind(kind), _children(children), 
      _bm(bm), _node_num(nodenum), _index_width(0), _value_width(0)
    {
    }

    // Copy constructor.  This copies the contents of the child nodes
    // array, along with everything else.  Assigning the smart pointer,
    // ASTNode, does NOT invoke this; This should only be used for
    // temporary hash keys before uniquefication.
    // FIXME:  I don't think children need to be copied.
    ASTInternal(const ASTInternal &int_node, int nodenum = 0) :
      _ref_count(0), _kind(int_node._kind), 
      _children(int_node._children), _bm(int_node._bm), 
      _node_num(int_node._node_num), _index_width(int_node._index_width), 
      _value_width(int_node._value_width)
    {
    }

    // Copying assign operator.  Also copies contents of children.
    ASTInternal& operator=(const ASTInternal &int_node);

    // Cleanup function for removing from hash table
    virtual void CleanUp() = 0;

    // Destructor (does nothing, but is declared virtual here.
    virtual ~ASTInternal();

    // Abstract virtual print function for internal node.
    // (c_friendly is for printing hex. numbers that C compilers will accept)
    virtual void nodeprint(ostream& os, bool c_friendly = false)
    {
      os << "*";
    }
    ;
  }; //End of Class ASTInternal

  // FIXME: Should children be only in interior node type?
  /***************************************************************************
 Class ASTInterior: Internal representation of an interior
 ASTNode.  Generally, these nodes should have at least one
 child
  ***************************************************************************/
  class ASTInterior: public ASTInternal
  {

    friend class BeevMgr;
    friend class ASTNodeHasher;
    friend class ASTNodeEqual;

  private:

    // Hasher for ASTInterior pointer nodes
    class ASTInteriorHasher
    {
    public:
      size_t operator()(const ASTInterior *int_node_ptr) const;
    };

    // Equality for ASTInterior nodes
    class ASTInteriorEqual
    {
    public:
      bool operator()(const ASTInterior *int_node_ptr1, 
		      const ASTInterior *int_node_ptr2) const
      {
        return (*int_node_ptr1 == *int_node_ptr2);
      }
    };

    // Used in Equality class for hash tables
    friend bool operator==(const ASTInterior &int_node1, 
			   const ASTInterior &int_node2)
    {
      return (int_node1._kind == int_node2._kind) && 
	(int_node1._children == int_node2._children);
    }

    // Call this when deleting a node that has been stored in the
    // the unique table
    virtual void CleanUp();

    // Returns kinds.  "lispprinter" handles printing of parenthesis
    // and childnodes. (c_friendly is for printing hex. numbers that C
    // compilers will accept)
    virtual void nodeprint(ostream& os, bool c_friendly = false)
    {
      os << _kind_names[_kind];
    }
  public:

    // FIXME: This should not be public, but has to be because the
    // ASTInterior hash table insists on it.  I can't seem to make the
    // private destructor visible to hash_set.  It does not even work
    // to put "friend class hash_set<ASTInterior, ...>" in here.

    // Basic constructors
    ASTInterior(Kind kind, BeevMgr &bm) :
      ASTInternal(kind, bm)
    {
    }

    ASTInterior(Kind kind, ASTVec &children, BeevMgr &bm) :
      ASTInternal(kind, children, bm)
    {
    }

    //Copy constructor.  This copies the contents of the child nodes
    //array, along with everything else. Assigning the smart pointer,
    //ASTNode, does NOT invoke this.
    ASTInterior(const ASTInterior &int_node) :
      ASTInternal(int_node)
    {
    }

    // Destructor (does nothing, but is declared virtual here.
    virtual ~ASTInterior();

  }; //End of ASTNodeInterior


  /***************************************************************************/
  /*  Class ASTSymbol:  Class to represent internals of Symbol node.         */
  /***************************************************************************/
  class ASTSymbol: public ASTInternal
  {
    friend class BeevMgr;
    friend class ASTNode;
    friend class ASTNodeHasher;
    friend class ASTNodeEqual;

  private:
    // The name of the symbol
    const char * const _name;

    class ASTSymbolHasher
    {
    public:
      size_t operator()(const ASTSymbol *sym_ptr) const
      {
#ifdef TR1_UNORDERED_MAP
        tr1::hash<string> h;
#else
        hash<char*> h;
#endif
        return h(sym_ptr->_name);
      }
      ;
    };

    // Equality for ASTInternal nodes
    class ASTSymbolEqual
    {
    public:
      bool operator()(const ASTSymbol *sym_ptr1, const ASTSymbol *sym_ptr2) const
      {
        return (*sym_ptr1 == *sym_ptr2);
      }
    };

    friend bool operator==(const ASTSymbol &sym1, const ASTSymbol &sym2)
    {
      return (strcmp(sym1._name, sym2._name) == 0);
    }

    const char * /**const**/ GetName() const
    {
      return _name;
    }

    // Print function for symbol -- return name */
    // (c_friendly is for printing hex. numbers that C compilers will accept)
    virtual void nodeprint(ostream& os, bool c_friendly = false)
    {
      os << _name;
    }

    // Call this when deleting a node that has been stored in the
    // the unique table
    virtual void CleanUp();

  public:

    // Default constructor
    ASTSymbol(BeevMgr &bm) :
      ASTInternal(bm), _name(NULL)
    {
    }

    // Constructor.  This does NOT copy its argument.
    ASTSymbol(const char * const name, BeevMgr &bm) :
      ASTInternal(SYMBOL, bm), _name(name)
    {
    }

    // Destructor (does nothing, but is declared virtual here.
    virtual ~ASTSymbol();

    // Copy constructor
    // FIXME: seems to be calling default constructor for astinternal
    ASTSymbol(const ASTSymbol &sym) :
      ASTInternal(sym._kind, sym._children, sym._bm), _name(sym._name)
    {
    }
  }; //End of ASTSymbol


  /***************************************************************************/
  /*  Class ASTBVConst:  Class to represent internals of a bitvectorconst    */
  /***************************************************************************/
  class ASTBVConst: public ASTInternal
  {
    friend class BeevMgr;
    friend class ASTNode;
    friend class ASTNodeHasher;
    friend class ASTNodeEqual;

  private:
    //This is the private copy of a bvconst currently
    //This should not be changed at any point
    CBV _bvconst;

    class ASTBVConstHasher
    {
    public:
      size_t operator()(const ASTBVConst * bvc) const
      {
        return CONSTANTBV::BitVector_Hash(bvc->_bvconst);
      }
      ;
    };

    class ASTBVConstEqual
    {
    public:
      bool operator()(const ASTBVConst * bvc1, const ASTBVConst * bvc2) const
      {
        if (bvc1->_value_width != bvc2->_value_width)
          {
            return false;
          }
        return (0 == CONSTANTBV::BitVector_Compare(bvc1->_bvconst, bvc2->_bvconst));
      }
    };

    //FIXME Keep an eye on this function
    ASTBVConst(CBV bv, unsigned int width, BeevMgr &bm) :
      ASTInternal(BVCONST, bm)
    {
      _bvconst = CONSTANTBV::BitVector_Clone(bv);
      _value_width = width;
    }

    friend bool operator==(const ASTBVConst &bvc1, const ASTBVConst &bvc2)
    {
      if (bvc1._value_width != bvc2._value_width)
        return false;
      return (0 == CONSTANTBV::BitVector_Compare(bvc1._bvconst, bvc2._bvconst));
    }
    // Call this when deleting a node that has been stored in the
    // the unique table
    virtual void CleanUp();

    // Print function for bvconst -- return _bvconst value in bin format
    // (c_friendly is for printing hex. numbers that C compilers will accept)
    virtual void nodeprint(ostream& os, bool c_friendly = false)
    {
      unsigned char *res;
      const char *prefix;

      if(print_binary_flag) {
        res = CONSTANTBV::BitVector_to_Bin(_bvconst);
        if (c_friendly)
          {
            prefix = "0b";
          }
        else
          {
            prefix = "0bin";
          }
      }
      else if (_value_width % 4 == 0)
        {
          res = CONSTANTBV::BitVector_to_Hex(_bvconst);
          if (c_friendly)
            {
              prefix = "0x";
            }
          else
            {
              prefix = "0hex";
            }
        }
      else
        {
          res = CONSTANTBV::BitVector_to_Bin(_bvconst);
          if (c_friendly)
            {
              prefix = "0b";
            }
          else
            {
              prefix = "0bin";
            }
        }
      if (NULL == res)
        {
          os << "nodeprint: BVCONST : could not convert to string" << _bvconst;
          FatalError("");
        }
      os << prefix << res;
      CONSTANTBV::BitVector_Dispose(res);
    }

    // Copy constructor.
    ASTBVConst(const ASTBVConst &sym) :
      ASTInternal(sym._kind, sym._children, sym._bm)
    {
      _bvconst = CONSTANTBV::BitVector_Clone(sym._bvconst);
      _value_width = sym._value_width;
    }

  public:
    virtual ~ASTBVConst()
    {
      CONSTANTBV::BitVector_Destroy(_bvconst);
    }

    CBV GetBVConst() const
    {
      return _bvconst;
    }
  }; //End of ASTBVConst

  /***************************************************************************
   * Typedef ASTNodeMap:  This is a hash table from ASTNodes to ASTNodes.
   * It is very convenient for attributes that are not speed-critical
   **************************************************************************/
  // These are generally useful for storing ASTNodes or attributes thereof
  // Hash table from ASTNodes to ASTNodes
  typedef hash_map<ASTNode, 
                   ASTNode, 
                   ASTNode::ASTNodeHasher, 
                   ASTNode::ASTNodeEqual> ASTNodeMap;

  typedef hash_map<ASTNode, 
                   int32_t, 
                   ASTNode::ASTNodeHasher, 
                   ASTNode::ASTNodeEqual> ASTNodeCountMap;

//   typedef hash_map<int32_t,
// 		   ASTVec,
// 		   hash(int32_t)> IntToASTVecMap;

  // Function to dump contents of ASTNodeMap
  ostream &operator<<(ostream &os, const ASTNodeMap &nmap);

  /***************************************************************************
 Typedef ASTNodeSet:  This is a hash set of ASTNodes.  Very useful
 for representing things like "visited nodes"
  ***************************************************************************/
  typedef hash_set<ASTNode, 
                   ASTNode::ASTNodeHasher, 
                   ASTNode::ASTNodeEqual> ASTNodeSet;

  typedef hash_multiset<ASTNode, 
                        ASTNode::ASTNodeHasher, 
                        ASTNode::ASTNodeEqual> ASTNodeMultiSet;

  //external parser table for declared symbols.
  //FIXME: move to a more appropriate place
  extern ASTNodeSet _parser_symbol_table;

  /***************************************************************************
   * Class BeevMgr.  This holds all "global" variables for the system, such as
   * unique tables for the various kinds of nodes.
   ***************************************************************************/
  class BeevMgr
  {
    friend class ASTNode; // ASTNode modifies AlreadyPrintedSet
    // in BeevMgr
    friend class ASTInterior;
    friend class ASTBVConst;
    friend class ASTSymbol;

    static const int INITIAL_INTERIOR_UNIQUE_TABLE_SIZE = 100;
    static const int INITIAL_SYMBOL_UNIQUE_TABLE_SIZE = 100;
    static const int INITIAL_BVCONST_UNIQUE_TABLE_SIZE = 100;
    static const int INITIAL_BBTERM_MEMO_TABLE_SIZE = 100;
    static const int INITIAL_BBFORM_MEMO_TABLE_SIZE = 100;

    static const int INITIAL_SIMPLIFY_MAP_SIZE = 100;
    static const int INITIAL_SOLVER_MAP_SIZE = 100;
    static const int INITIAL_ARRAYREAD_SYMBOL_SIZE = 100;
    static const int INITIAL_INTRODUCED_SYMBOLS_SIZE = 100;

  private:
    // Typedef for unique Interior node table.
    typedef hash_set<ASTInterior *, 
		     ASTInterior::ASTInteriorHasher, 
		     ASTInterior::ASTInteriorEqual> ASTInteriorSet;

    // Typedef for unique Symbol node (leaf) table.
    typedef hash_set<ASTSymbol *, 
		     ASTSymbol::ASTSymbolHasher, 
		     ASTSymbol::ASTSymbolEqual> ASTSymbolSet;

    // Unique tables to share nodes whenever possible.
    ASTInteriorSet _interior_unique_table;
    //The _symbol_unique_table is also the symbol table to be used
    //during parsing/semantic analysis
    ASTSymbolSet _symbol_unique_table;

    //Typedef for unique BVConst node (leaf) table.
    typedef hash_set<ASTBVConst *, 
		     ASTBVConst::ASTBVConstHasher, 
		     ASTBVConst::ASTBVConstEqual> ASTBVConstSet;

    //table to uniquefy bvconst
    ASTBVConstSet _bvconst_unique_table;

    // type of memo table.
    typedef hash_map<ASTNode, 
		     ASTVec, 
		     ASTNode::ASTNodeHasher, 
		     ASTNode::ASTNodeEqual> ASTNodeToVecMap;

    typedef hash_map<ASTNode, 
		     ASTNodeSet,
		     ASTNode::ASTNodeHasher, 
		     ASTNode::ASTNodeEqual> ASTNodeToSetMap;

    // Memo table for bit blasted terms.  If a node has already been
    // bitblasted, it is mapped to a vector of Boolean formulas for
    // the bits.

    //OLD: ASTNodeToVecMap BBTermMemo;
    ASTNodeMap BBTermMemo;

    // Memo table for bit blasted formulas.  If a node has already
    // been bitblasted, it is mapped to a node representing the
    // bitblasted equivalent
    ASTNodeMap BBFormMemo;

    //public:
    // Get vector of Boolean formulas for sum of two
    // vectors of Boolean formulas
    void BBPlus2(ASTVec& sum, const ASTVec& y, ASTNode cin);
    // Increment
    ASTVec BBInc(ASTVec& x);
    // Add one bit to a vector of bits.
    ASTVec BBAddOneBit(ASTVec& x, ASTNode cin);
    // Bitwise complement
    ASTVec BBNeg(const ASTVec& x);
    // Unary minus
    ASTVec BBUminus(const ASTVec& x);
    // Multiply.
    ASTVec BBMult(const ASTVec& x, const ASTVec& y);
    // AND each bit of vector y with single bit b and return the result.
    // (used in BBMult)
    ASTVec BBAndBit(const ASTVec& y, ASTNode b);
    // Returns ASTVec for result - y.  This destroys "result".
    void BBSub(ASTVec& result, const ASTVec& y);
    // build ITE's (ITE cond then[i] else[i]) for each i.
    ASTVec BBITE(const ASTNode& cond, const ASTVec& thn, const ASTVec& els);
    // Build a vector of zeros.
    ASTVec BBfill(unsigned int width, ASTNode fillval);
    // build an EQ formula
    ASTNode BBEQ(const ASTVec& left, const ASTVec& right);

    // This implements a variant of binary long division.
    // q and r are "out" parameters.  rwidth puts a bound on the
    // recursion depth.   Unsigned only, for now.
    void BBDivMod(const ASTVec &y, const ASTVec &x, ASTVec &q, ASTVec &r, unsigned int rwidth);

    // Return formula for majority function of three formulas.
    ASTNode Majority(const ASTNode& a, const ASTNode& b, const ASTNode& c);

    // Internal bit blasting routines.
    ASTNode BBBVLE(const ASTVec& x, const ASTVec& y, bool is_signed);

    // Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
    ASTNode BBcompare(const ASTNode& form);

    void BBRSignedShift(ASTVec& x, unsigned int shift);
    void BBLShift(ASTVec& x, unsigned int shift);
    void BBRShift(ASTVec& x, unsigned int shift);

  public:
    // Simplifying create functions
    ASTNode CreateSimpForm(Kind kind, ASTVec &children);
    ASTNode CreateSimpForm(Kind kind, const ASTNode& child0);
    ASTNode CreateSimpForm(Kind kind, 
			   const ASTNode& child0, const ASTNode& child1);
    ASTNode CreateSimpForm(Kind kind, const ASTNode& child0,
			   const ASTNode& child1, const ASTNode& child2);

    ASTNode CreateSimpNot(const ASTNode& form);

    // These are for internal use only.
    // FIXME: Find a way to make this local to SimpBool, so they're
    // not in AST.h
    ASTNode CreateSimpXor(const ASTNode& form1, const ASTNode& form2);
    ASTNode CreateSimpXor(ASTVec &children);
    ASTNode CreateSimpAndOr(bool isAnd, 
			    const ASTNode& form1, const ASTNode& form2);
    ASTNode CreateSimpAndOr(bool IsAnd, ASTVec &children);
    ASTNode CreateSimpFormITE(const ASTNode& child0, 
			      const ASTNode& child1, const ASTNode& child2);

    // Declarations of BitBlaster functions (BitBlast.cpp)
  public:
    // Adds or removes a NOT as necessary to negate a literal.
    ASTNode Negate(const ASTNode& form);

    // Bit blast a bitvector term.  The term must have a kind for a
    // bitvector term.  Result is a ref to a vector of formula nodes
    // representing the boolean formula.
    const ASTNode BBTerm(const ASTNode& term);

    const ASTNode BBForm(const ASTNode& formula);

    // Declarations of CNF conversion (ToCNF.cpp)
  public:
    // ToCNF converts a bit-blasted Boolean formula to Conjunctive
    //  Normal Form, suitable for many SAT solvers.  Our CNF representation
    //  is an STL vector of STL vectors, for independence from any particular
    //  SAT solver's representation.  There needs to be a separate driver to
    //  convert our clauselist to the representation used by the SAT solver.
    //  Currently, there is only one such solver and its driver is "ToSAT"

    // Datatype for clauses
    typedef vector<const ASTNode*>* ClausePtr;

    // Datatype for Clauselists
    typedef vector<ClausePtr> ClauseList;

    // Convert a Boolean formula to an equisatisfiable CNF formula.
    ClauseList *ToCNF(const ASTNode& form);

    // Print function for debugging
    void PrintClauseList(ostream& os, ClauseList& cll);

    // Free the clause list and all its clauses.
    void DeleteClauseList(BeevMgr::ClauseList *cllp);

    // Map from formulas to representative literals, for debugging.
    ASTNodeMap RepLitMap;

  private:
    // Global for assigning new node numbers.
    int _max_node_num;

    const ASTNode ASTFalse, ASTTrue, ASTUndefined;

    // I just did this so I could put it in as a fake return value in
    // methods that return a ASTNode &, to make -Wall shut up.
    ASTNode dummy_node;

    //BeevMgr Constructor, Destructor and other misc. functions
  public:

    int NewNodeNum()
    {
      _max_node_num += 2;
      return _max_node_num;
    }

    // Table for DAG printing.
    ASTNodeSet AlreadyPrintedSet;

    //Tables for Presentation language printing

    //Nodes seen so far
    ASTNodeSet PLPrintNodeSet;

    //Map from ASTNodes to LetVars
    ASTNodeMap NodeLetVarMap;

    //This is a vector which stores the Node to LetVars pairs. It
    //allows for sorted printing, as opposed to NodeLetVarMap
    std::vector<pair<ASTNode, ASTNode> > NodeLetVarVec;

    //a partial Map from ASTNodes to LetVars. Needed in order to
    //correctly print shared subterms inside the LET itself
    ASTNodeMap NodeLetVarMap1;

    //functions to lookup nodes from the memo tables. these should be
    //private.
  private:
    //Destructively appends back_child nodes to front_child nodes.
    //If back_child nodes is NULL, no appending is done.  back_child
    //nodes are not modified.  Then it returns the hashed copy of the
    //node, which is created if necessary.
    ASTInterior *CreateInteriorNode(Kind kind, ASTInterior *new_node,
                                    // this is destructively modified.
                                    const ASTVec & back_children = _empty_ASTVec);

    // Create unique ASTInterior node.
    ASTInterior *LookupOrCreateInterior(ASTInterior *n);

    // Create unique ASTSymbol node.
    ASTSymbol *LookupOrCreateSymbol(ASTSymbol& s);

    // Called whenever we want to make sure that the Symbol is
    // declared during semantic analysis
    bool LookupSymbol(ASTSymbol& s);

    // Called by ASTNode constructors to uniqueify ASTBVConst
    ASTBVConst *LookupOrCreateBVConst(ASTBVConst& s);

    //Public functions for CreateNodes and Createterms
  public:
    // Create and return an ASTNode for a symbol
    ASTNode CreateSymbol(const char * const name);

    // Create and return an ASTNode for a symbol
    // Width is number of bits.
    ASTNode CreateBVConst(string*& strval, int base, int bit_width);
    ASTNode CreateBVConst(unsigned int width, unsigned long long int bvconst);
    ASTNode CreateZeroConst(unsigned int width);
    ASTNode CreateOneConst(unsigned int width);
    ASTNode CreateTwoConst(unsigned int width);
    ASTNode CreateMaxConst(unsigned int width);

    // Create and return an ASTNode for a symbol
    // Optional base was a problem because 0 could be an int or char *,
    // so CreateBVConst was ambiguous.
    ASTNode CreateBVConst(const char *strval, int base);

    //FIXME This is a dangerous function
    ASTNode CreateBVConst(CBV bv, unsigned width);

    // Create and return an interior ASTNode
    ASTNode CreateNode(Kind kind, const ASTVec &children = _empty_ASTVec);

    ASTNode CreateNode(Kind kind, const ASTNode& child0, 
		       const ASTVec &children = _empty_ASTVec);

    ASTNode CreateNode(Kind kind, const ASTNode& child0, 
		       const ASTNode& child1, const ASTVec &children = _empty_ASTVec);

    ASTNode CreateNode(Kind kind, const ASTNode& child0, 
		       const ASTNode& child1, const ASTNode& child2, 
		       const ASTVec &children = _empty_ASTVec);

    // Create and return an ASTNode for a term
    inline ASTNode CreateTerm(Kind kind, 
			      unsigned int width, const ASTVec &children = _empty_ASTVec)
    {
      if (!is_Term_kind(kind))
        FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);
      ASTNode n = CreateNode(kind, children);
      n.SetValueWidth(width);

      //by default we assume that the term is a Bitvector. If
      //necessary the indexwidth can be changed later
      n.SetIndexWidth(0);
      return n;
    }

    inline ASTNode CreateTerm(Kind kind, unsigned int width, 
			      const ASTNode& child0, const ASTVec &children = _empty_ASTVec)
    {
      if (!is_Term_kind(kind))
        FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);
      ASTNode n = CreateNode(kind, child0, children);
      n.SetValueWidth(width);
      return n;
    }

    inline ASTNode CreateTerm(Kind kind, unsigned int width, 
			      const ASTNode& child0, const ASTNode& child1, 
			      const ASTVec &children = _empty_ASTVec)
    {
      if (!is_Term_kind(kind))
        FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);
      ASTNode n = CreateNode(kind, child0, child1, children);
      n.SetValueWidth(width);
      return n;
    }

    inline ASTNode CreateTerm(Kind kind,
                              unsigned int width,
                              const ASTNode& child0,
                              const ASTNode& child1,
                              const ASTNode& child2,
                              const ASTVec &children = _empty_ASTVec)
    {
      if (!is_Term_kind(kind))
        FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);
      ASTNode n = CreateNode(kind, child0, child1, child2, children);
      n.SetValueWidth(width);
      return n;
    }

    ASTNode SimplifyFormula_NoRemoveWrites(const ASTNode& a, 
					   bool pushNeg, 
					   ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyFormula_TopLevel(const ASTNode& a, 
				     bool pushNeg,
				     ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyTerm_TopLevel(const ASTNode& b);

    ASTNode SimplifyFormula(const ASTNode& a, 
			    bool pushNeg, 
			    ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyTerm(const ASTNode& inputterm, 
			 ASTNodeMap* VarConstMap=NULL);
    void CheckSimplifyInvariant(const ASTNode& a, const ASTNode& output);
    void BuildReferenceCountMap(const ASTNode& b);

  private:
    //memo table for simplifcation
    ASTNodeMap *SimplifyMap;
    ASTNodeMap *SimplifyNegMap;
    ASTNodeMap SolverMap;
    ASTNodeSet AlwaysTrueFormMap;
    ASTNodeMap MultInverseMap;


    // The number of direct parents of each node. i.e. the number
    // of times the pointer is in "children".  When we simplify we
    // want to be careful sometimes about using the context of a
    // node. For example, given ((x + 23) = 2), the obvious
    // simplification is to join the constants. However, if there
    // are lots of references to the plus node. Then each time we
    // simplify, we'll create an additional plus.
    // nextpoweroftwo064.smt is the motivating benchmark. The
    // splitting increased the number of pluses from 1 to 65.
    ASTNodeCountMap *ReferenceCount;

  public:
    ASTNode SimplifyAtomicFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode CreateSimplifiedEQ(const ASTNode& t1, const ASTNode& t2);
    ASTNode ITEOpt_InEqs(const ASTNode& in1, ASTNodeMap* VarConstMap=NULL);
    ASTNode PullUpITE(const ASTNode& in);
    ASTNode RemoveContradictionsFromAND(const ASTNode& in);
    ASTNode CreateSimplifiedTermITE(const ASTNode& t1, const ASTNode& t2, const ASTNode& t3);
    ASTNode CreateSimplifiedFormulaITE(const ASTNode& in0, const ASTNode& in1, const ASTNode& in2);
    ASTNode CreateSimplifiedINEQ(Kind k, const ASTNode& a0, const ASTNode& a1, bool pushNeg);
    ASTNode SimplifyNotFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyAndOrFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyXorFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyNandFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyNorFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyImpliesFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyIffFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyIteFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode SimplifyForFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    ASTNode FlattenOneLevel(const ASTNode& a);
    ASTNode FlattenAndOr(const ASTNode& a);
    ASTNode CombineLikeTerms(const ASTNode& a);
    ASTNode LhsMinusRhs(const ASTNode& eq);
    ASTNode DistributeMultOverPlus(const ASTNode& a, bool startdistribution = false);
    ASTNode ConvertBVSXToITE(const ASTNode& a);
    //checks if the input constant is odd or not
    bool BVConstIsOdd(const ASTNode& c);
    //computes the multiplicatve inverse of the input
    ASTNode MultiplicativeInverse(const ASTNode& c);

    void ClearAllTables(void);
    void ClearAllCaches(void);
    int  BeforeSAT_ResultCheck(const ASTNode& q);
    SOLVER_RETURN_TYPE  CallSAT_ResultCheck(MINISAT::Solver& newS,
					    const ASTNode& modified_input, 
					    const ASTNode& original_input);
    SOLVER_RETURN_TYPE SATBased_ArrayReadRefinement(MINISAT::Solver& newS, 
						    const ASTNode& modified_input, 
						    const ASTNode& original_input);
    SOLVER_RETURN_TYPE SATBased_ArrayWriteRefinement(MINISAT::Solver& newS,
						     const ASTNode& orig_input);        
   
    SOLVER_RETURN_TYPE SATBased_AllFiniteLoops_Refinement(MINISAT::Solver& newS, 
							  const ASTNode& orig_input);
    
    ASTVec SATBased_FiniteLoop_Refinement(MINISAT::Solver& SatSolver, 
					  const ASTNode& original_input,
					  const ASTNode& finiteloop,
					  ASTNodeMap* ParamToCurrentValMap,
					  bool absrefine_flag=false);    
    
    ASTNode Check_FiniteLoop_UsingModel(const ASTNode& finiteloop,
					ASTNodeMap* ParamToCurrentValMap,
					bool CheckUsingModel_Or_Expand);
    ASTNode Expand_FiniteLoop_TopLevel(const ASTNode& finiteloop);
    ASTNode Check_FiniteLoop_UsingModel(const ASTNode& finiteloop);
  
    //creates array write axiom only for the input term or formula, if
    //necessary. If there are no axioms to produce then it simply
    //generates TRUE
    ASTNode Create_ArrayWriteAxioms(const ASTNode& array_readoverwrite_term, 
                                    const ASTNode& array_newname);
    ASTVec ArrayWrite_RemainingAxioms;
    //variable indicates that counterexample will now be checked by
    //the counterexample checker, and hence simplifyterm must switch
    //off certain optimizations. In particular, array write
    //optimizations
    bool start_abstracting;
    bool Begin_RemoveWrites;
    bool SimplifyWrites_InPlace_Flag;

    //For finiteloop construct
    //
    //A list of all finiteloop constructs in the input formula
    ASTVec GlobalList_Of_FiniteLoops;

    void CopySolverMap_To_CounterExample(void);
    //int LinearSearch(const ASTNode& orig_input);
    //Datastructures and functions needed for counterexample
    //generation, and interface with MINISAT
  private:
    /* MAP: This is a map from ASTNodes to MINISAT::Vars.
     *
     * The map is populated while ASTclauses are read from the AST
     * ClauseList returned by CNF converter. For every new boolean
     * variable in ASTClause a new MINISAT::Var is created (these vars
     * typedefs for ints)
     */
    typedef hash_map<ASTNode, MINISAT::Var, ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> ASTtoSATMap;
    ASTtoSATMap _ASTNode_to_SATVar;

  public:
    //converts the clause to SAT and calls SAT solver
    bool toSATandSolve(MINISAT::Solver& S, ClauseList& cll);

    ///print SAT solver statistics
    void PrintStats(MINISAT::Solver& stats);

    void printCacheStatus();

    //from v8
    SOLVER_RETURN_TYPE TopLevelSATAux(const ASTNode& query);

    //##################################################
    //##################################################

    //accepts query and returns the answer. if query is valid, return
    //true, else return false. Automatically constructs counterexample
    //for invalid queries, and prints them upon request.
    SOLVER_RETURN_TYPE TopLevelSAT(const ASTNode& query, const ASTNode& asserts);

    // Debugging function to find problems in BitBlast and ToCNF.
    // See body in ToSAT.cpp for more explanation.
    ASTNode CheckBBandCNF(MINISAT::Solver& newS, ASTNode form);

    // Internal recursive body of above.
    ASTNode CheckBBandCNF_int(MINISAT::Solver& newS, ASTNode form);

    // Helper function for CheckBBandCNF
    ASTNode SymbolTruthValue(MINISAT::Solver &newS, ASTNode form);

    //looksup a MINISAT var from the minisat-var memo-table. if none
    //exists, then creates one.
    // Treat the result as const.
    /**const**/ MINISAT::Var LookupOrCreateSATVar(MINISAT::Solver& S, const ASTNode& n);

    // Memo table for CheckBBandCNF debugging function
    ASTNodeMap CheckBBandCNFMemo;

    //Data structures for Array Read Transformations
  private:
    /* MAP: This is a map from Array Names to list of array-read
     * indices in the input. This map is used by the TransformArray()
     * function
     *
     * This map is useful in converting array reads into nested ITE
     * constructs. Suppose there are two array reads in the input
     * Read(A,i) and Read(A,j). Then Read(A,i) is replaced with a
     * symbolic constant, say v1, and Read(A,j) is replaced with the
     * following ITE:
     *
     * ITE(i=j,v1,v2)
     */
    //CAUTION: I tried using a set instead of vector for
    //readindicies. for some odd reason the performance went down
    //considerably. this is totally inexplicable.
    ASTNodeToVecMap _arrayname_readindices;

    /* MAP: This is a map from Array Names to nested ITE constructs,
     * which are built as described below. This map is used by the
     * TransformArray() function
     *
     * This map is useful in converting array reads into nested ITE
     * constructs. Suppose there are two array reads in the input
     * Read(A,i) and Read(A,j). Then Read(A,i) is replaced with a
     * symbolic constant, say v1, and Read(A,j) is replaced with the
     * following ITE:
     *
     * ITE(i=j,v1,v2)
     */
    ASTNodeMap _arrayread_ite;

    /*MAP: This is a map from array-reads to symbolic constants. This
     *map is used by the TransformArray()
     */
    ASTNodeMap _arrayread_symbol;

    ASTNodeSet _introduced_symbols;

    //count to keep track of new symbolic constants introduced
    //corresponding to Array Reads
    unsigned int _symbol_count;

    //Formula/Term Transformers. Let Expr Manager, Type Checker
  public:
    //Functions that Transform ASTNodes. TransformArray should be a non-member function,
    // but it accesses private elements. Move it later.
    ASTNode TransformFormula_TopLevel(const ASTNode& form);
    ASTNode TransformArray(const ASTNode& term);

    //LET Management
  private:
    // MAP: This map is from bound IDs that occur in LETs to
    // expression. The map is useful in checking replacing the IDs
    // with the corresponding expressions.
    ASTNodeMap *_letid_expr_map;
  public:

    ASTNode ResolveID(const ASTNode& var);

    //Functions that are used to manage LET expressions
    void LetExprMgr(const ASTNode& var, const ASTNode& letExpr);

    //Delete Letid Map
    void CleanupLetIDMap(void);

    //Allocate LetID map
    void InitializeLetIDMap(void);

    //Substitute Let-vars with LetExprs
    ASTNode SubstituteLetExpr(ASTNode inExpr);

    /* MAP: This is a map from MINISAT::Vars to ASTNodes
     *
     * This is a reverse map, useful in constructing
     * counterexamples. MINISAT returns a model in terms of MINISAT
     * Vars, and this map helps us convert it to a model over ASTNode
     * variables.
     */
    vector<ASTNode> _SATVar_to_AST;

  private:
    /* MAP: This is a map from ASTNodes to vectors of bits
     *
     * This map is used in constructing and printing
     * counterexamples. MINISAT returns values for each bit (a
     * BVGETBIT Node), and this maps allows us to assemble the bits
     * into bitvectors.
     */
    typedef hash_map<ASTNode, 
		     hash_map<unsigned int, bool> *, 
		     ASTNode::ASTNodeHasher, ASTNode::ASTNodeEqual> ASTtoBitvectorMap;
    ASTtoBitvectorMap _ASTNode_to_Bitvector;

    //Data structure that holds the counter-model
    ASTNodeMap CounterExampleMap;

    //Checks if the counter_example is ok. In order for the
    //counter_example to be ok, Every assert must evaluate to true
    //w.r.t couner_example and the query must evaluate to
    //false. Otherwise the counter_example is bogus.
    void CheckCounterExample(bool t);

    //Converts a vector of bools to a BVConst
    ASTNode BoolVectoBVConst(hash_map<unsigned, bool> * w, unsigned int l);

    //accepts a term and turns it into a constant-term w.r.t counter_example
    ASTNode TermToConstTermUsingModel(const ASTNode& term, bool ArrayReadFlag = true);
    ASTNode Expand_ReadOverWrite_UsingModel(const ASTNode& term, bool ArrayReadFlag = true);
    //Computes the truth value of a formula w.r.t counter_example
    ASTNode ComputeFormulaUsingModel(const ASTNode& form);

    //Replaces WRITE(Arr,i,val) with ITE(j=i, val, READ(Arr,j))
    ASTNode RemoveWrites_TopLevel(const ASTNode& term);
    ASTNode RemoveWrites(const ASTNode& term);
    ASTNode SimplifyWrites_InPlace(const ASTNode& term, ASTNodeMap* VarConstMap=NULL);
    ASTNode ReadOverWrite_To_ITE(const ASTNode& term, ASTNodeMap* VarConstMap=NULL);

    ASTNode NewArrayVar(unsigned int index, unsigned int value);
    ASTNode NewVar(unsigned int valuewidth);
    //For ArrayWrite Abstraction: map from read-over-write term to
    //newname.
    ASTNodeMap ReadOverWrite_NewName_Map;
    //For ArrayWrite Refinement: Map new arraynames to Read-Over-Write
    //terms
    ASTNodeMap NewName_ReadOverWrite_Map;

  public:
    ASTNode NewBooleanVar(const ASTNode& var, const ASTNode& param);

    //print the STP solver output
    void PrintOutput(SOLVER_RETURN_TYPE ret);

    //Converts MINISAT counterexample into an AST memotable (i.e. the
    //function populates the datastructure CounterExampleMap)
    void ConstructCounterExample(MINISAT::Solver& S);

    //Prints the counterexample to stdout
    void PrintCounterExample(bool t, std::ostream& os = cout);

    //Prints the counterexample to stdout
    void PrintCounterExample_InOrder(bool t);

    //queries the counterexample, and returns the value corresponding
    //to e
    ASTNode GetCounterExample(bool t, const ASTNode& e);

    int CounterExampleSize(void) const
    {
      return CounterExampleMap.size();
    }

    //FIXME: This is bloody dangerous function. Hack attack to take
    //care of requests from users who want to store complete
    //counter-examples in their own data structures.
    ASTNodeMap GetCompleteCounterExample()
    {
      return CounterExampleMap;
    }

    // prints MINISAT assigment one bit at a time, for debugging.
    void PrintSATModel(MINISAT::Solver& S);

    //accepts constant input and normalizes it.
    ASTNode BVConstEvaluator(const ASTNode& t);

    //FUNCTION TypeChecker: Assumes that the immediate Children of the
    //input ASTNode have been typechecked. This function is suitable
    //in scenarios like where you are building the ASTNode Tree, and
    //you typecheck as you go along. It is not suitable as a general
    //typechecker

    // NB: The boolean value is always true!
    bool BVTypeCheck(const ASTNode& n);

    // Checks recursively all the way down.
    bool BVTypeCheckRecursive(const ASTNode& n);



  private:
    //stack of Logical Context. each entry in the stack is a logical
    //context. A logical context is a vector of assertions. The
    //logical context is represented by a ptr to a vector of
    //assertions in that logical context. Logical contexts are created
    //by PUSH/POP
    std::vector<ASTVec *> _asserts;
    //The query for the current logical context.
    ASTNode _current_query;    

    //this flag, when true, indicates that counterexample is being
    //checked by the counterexample checker
    bool counterexample_checking_during_refinement;

    //this flag indicates as to whether the input has been determined to
    //be valid or not by this tool
    bool ValidFlag;

    //this flag, when true, indicates that a BVDIV divide by zero
    //exception occured. However, the program must not exit with a
    //fatalerror. Instead, it should evaluate the whole formula (which
    //contains the BVDIV term) to be FALSE.
    bool bvdiv_exception_occured;

  public:
    //set of functions that manipulate Logical Contexts.
    //
    //add an assertion to the current logical context
    void AddAssert(const ASTNode& assert);
    void Push(void);
    void Pop(void);
    void AddQuery(const ASTNode& q);
    const ASTNode PopQuery();
    const ASTNode GetQuery();
    const ASTVec GetAsserts(void);

    //reports node size.  Second arg is "clearstatinfo", whatever that is.
    unsigned int NodeSize(const ASTNode& a, bool t = false);

  private:
    //This memo map is used by the ComputeFormulaUsingModel()
    ASTNodeMap ComputeFormulaMap;
    //Map for statiscal purposes
    ASTNodeSet StatInfoSet;

    ASTNodeMap TermsAlreadySeenMap;
    ASTNode CreateSubstitutionMap(const ASTNode& a);
  public:
    //prints statistics for the ASTNode. can add a prefix string c
    void ASTNodeStats(const char * c, const ASTNode& a);

    //Check the map passed to SimplifyTerm
    bool CheckMap(ASTNodeMap* VarConstMap, 
		  const ASTNode& key, ASTNode& output);

    RunTimes runTimes;

    //substitution
    bool CheckSubstitutionMap(const ASTNode& a, ASTNode& output);
    bool CheckSubstitutionMap(const ASTNode& a);
    bool UpdateSubstitutionMap(const ASTNode& e0, const ASTNode& e1);
    //if (a > b) in the termorder, then return 1
    //elseif (a < b) in the termorder, then return -1
    //else return 0
    int TermOrder(const ASTNode& a, const ASTNode& b);
    //fill the arrayname_readindices vector if e0 is a READ(Arr,index)
    //and index is a BVCONST
    void FillUp_ArrReadIndex_Vec(const ASTNode& e0, const ASTNode& e1);
    bool VarSeenInTerm(const ASTNode& var, const ASTNode& term);

    //functions for checking and updating simplifcation map
    bool CheckSimplifyMap(const ASTNode& key, 
			  ASTNode& output, 
			  bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    void UpdateSimplifyMap(const ASTNode& key, 
			   const ASTNode& value, 
			   bool pushNeg, ASTNodeMap* VarConstMap=NULL);
    void ResetSimplifyMaps();
    bool CheckAlwaysTrueFormMap(const ASTNode& key);
    void UpdateAlwaysTrueFormMap(const ASTNode& val);
    bool CheckMultInverseMap(const ASTNode& key, ASTNode& output);
    void UpdateMultInverseMap(const ASTNode& key, const ASTNode& value);

    //Map for solved variables
    bool CheckSolverMap(const ASTNode& a, ASTNode& output);
    bool CheckSolverMap(const ASTNode& a);
    bool UpdateSolverMap(const ASTNode& e0, const ASTNode& e1);

  public:
    ASTVec ListOfDeclaredVars;
    void printVarDeclsToStream(ostream &os);
    void printAssertsToStream(ostream &os, int simplify);

    // Constructor
    BeevMgr() :
      _interior_unique_table(INITIAL_INTERIOR_UNIQUE_TABLE_SIZE), 
      _symbol_unique_table(INITIAL_SYMBOL_UNIQUE_TABLE_SIZE), 
      _bvconst_unique_table(INITIAL_BVCONST_UNIQUE_TABLE_SIZE), 
      BBTermMemo(INITIAL_BBTERM_MEMO_TABLE_SIZE), 
      BBFormMemo(INITIAL_BBFORM_MEMO_TABLE_SIZE),
      _max_node_num(0), ASTFalse(CreateNode(FALSE)), 
      ASTTrue(CreateNode(TRUE)), ASTUndefined(CreateNode(UNDEFINED)), 
      SolverMap(INITIAL_SOLVER_MAP_SIZE), 
      _arrayread_symbol(INITIAL_ARRAYREAD_SYMBOL_SIZE), 
      _introduced_symbols(INITIAL_INTRODUCED_SYMBOLS_SIZE), _symbol_count(0)
    {
      _current_query = ASTUndefined;
      ValidFlag = false;
      bvdiv_exception_occured = false;
      counterexample_checking_during_refinement = false;
      start_abstracting = false;
      Begin_RemoveWrites = false;
      SimplifyWrites_InPlace_Flag = false;
      SimplifyMap = new ASTNodeMap(INITIAL_SIMPLIFY_MAP_SIZE);
      SimplifyNegMap = new ASTNodeMap(INITIAL_SIMPLIFY_MAP_SIZE);
      _letid_expr_map = new ASTNodeMap(INITIAL_INTRODUCED_SYMBOLS_SIZE);
      ReferenceCount = new ASTNodeCountMap(INITIAL_SIMPLIFY_MAP_SIZE);
    }
    ;

    //destructor
    ~BeevMgr();
  };//End of Class BeevMgr


  class CompleteCounterExample
  {
    ASTNodeMap counterexample;
    BeevMgr * bv;
  public:
    CompleteCounterExample(ASTNodeMap a, BeevMgr* beev) :
      counterexample(a), bv(beev)
    {
    }
    ASTNode GetCounterExample(ASTNode e)
    {
      if (BOOLEAN_TYPE == e.GetType() && SYMBOL != e.GetKind())
        {
          FatalError("You must input a term or propositional variables\n", e);
        }
      if (counterexample.find(e) != counterexample.end())
        {
          return counterexample[e];
        }
      else
        {
          if (SYMBOL == e.GetKind() && BOOLEAN_TYPE == e.GetType())
            {
              return bv->CreateNode(BEEV::FALSE);
            }

          if (SYMBOL == e.GetKind())
            {
              ASTNode z = bv->CreateZeroConst(e.GetValueWidth());
              return z;
            }

          return e;
        }
    }
  };//end of Class CompleteCounterExample


  /*****************************************************************
   * INLINE METHODS from various classed, declared here because of
   * dependencies on classes that are declared later.
   *****************************************************************/
  // ASTNode accessor function.
  inline Kind ASTNode::GetKind() const
  {
    //cout << "GetKind: " << _int_node_ptr;
    return _int_node_ptr->GetKind();
  }

  // FIXME: should be const ASTVec const?
  // Declared here because of same ordering problem as  GetKind.
  inline const ASTVec &ASTNode::GetChildren() const
  {
    return _int_node_ptr->GetChildren();
  }

  // Access node number
  inline int ASTNode::GetNodeNum() const
  {
    return _int_node_ptr->_node_num;
  }

  inline unsigned int ASTNode::GetIndexWidth() const
  {
    return _int_node_ptr->_index_width;
  }

  inline void ASTNode::SetIndexWidth(unsigned int iw) const
  {
    _int_node_ptr->_index_width = iw;
  }

  inline unsigned int ASTNode::GetValueWidth() const
  {
    return _int_node_ptr->_value_width;
  }

  inline void ASTNode::SetValueWidth(unsigned int vw) const
  {
    _int_node_ptr->_value_width = vw;
  }

  //return the type of the ASTNode: 0 iff BOOLEAN; 1 iff BITVECTOR; 2
  //iff ARRAY; 3 iff UNKNOWN;
  inline types ASTNode::GetType() const
  {
    if ((GetIndexWidth() == 0) && (GetValueWidth() == 0)) //BOOLEAN
      return BOOLEAN_TYPE;
    if ((GetIndexWidth() == 0) && (GetValueWidth() > 0)) //BITVECTOR
      return BITVECTOR_TYPE;
    if ((GetIndexWidth() > 0) && (GetValueWidth() > 0)) //ARRAY
      return ARRAY_TYPE;
    return UNKNOWN_TYPE;
  }

  // Constructor; creates a new pointer, increments refcount of
  // pointed-to object.
  inline ASTNode::ASTNode(ASTInternal *in) :
    _int_node_ptr(in)
  {
    if (in)
      in->IncRef();
  }

  // Assignment.  Increment refcount of new value, decrement refcount of
  // old value and destroy if this was the last pointer.  FIXME:
  // accelerate this by creating an intnode with a ref counter instead
  // of pointing to NULL.  Need a special check in CleanUp to make sure
  // the null node never gets freed.

  inline ASTNode& ASTNode::operator=(const ASTNode& n)
  {
    if (n._int_node_ptr)
      {
        n._int_node_ptr->IncRef();
      }
    if (_int_node_ptr)
      {
        _int_node_ptr->DecRef();
      }
    _int_node_ptr = n._int_node_ptr;
    return *this;
  }

  inline void ASTInternal::DecRef()
  {
    if (--_ref_count == 0)
      {
        // Delete node from unique table and kill it.
        CleanUp();
      }
  }

  // Destructor
  inline ASTNode::~ASTNode()
  {
    if (_int_node_ptr)
      {
        _int_node_ptr->DecRef();
      }
  }

  inline BeevMgr& ASTNode::GetBeevMgr() const
  {
    return _int_node_ptr->_bm;
  }

  //Return the unsigned constant value of the input 'n'
  inline unsigned int GetUnsignedConst(const ASTNode n)
  {
    if(BVCONST != n.GetKind()){
      FatalError("GetUnsignedConst: cannot extract an "\
                 "unsigned value from a non-bvconst");
    }

    if (sizeof(unsigned int) * 8 <= n.GetValueWidth())
      {
        // It may only contain a small value in a bit type,
        // which fits nicely into an unsigned int.  This is
        // common for functions like: bvshl(bv1[128],
        // bv1[128]) where both operands have the same type.
        signed long maxBit = CONSTANTBV::Set_Max(n.GetBVConst());
        if (maxBit >= ((signed long) sizeof(unsigned int)) * 8)
          {
            n.LispPrint(cerr); //print the node so they can find it.
            FatalError("GetUnsignedConst: cannot convert bvconst "\
                       "of length greater than 32 to unsigned int");
          }
      }
    return (unsigned int) *((unsigned int *) n.GetBVConst());
  } //end of GetUnsignedConst
}; // end namespace BEEV
#endif
