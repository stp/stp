// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#ifndef ASTINTERNAL_H
#define ASTINTERNAL_H

/********************************************************************
 *  This file gives the class description of the ASTInternal class  *
 ********************************************************************/
namespace BEEV
{
  /******************************************************************
   * Class ASTInternal:                                             *
   *                                                                *
   * Abstract base class for internal node representation. Requires *
   * Kind and ChildNodes so same traversal works on all nodes.      *
   ******************************************************************/
  class ASTInternal
  {
    friend class ASTNode;
    friend class CNFMgr;

  protected:
    /****************************************************************
     * Protected Data                                               *
     ****************************************************************/

    //reference counting for garbage collection
    unsigned int   _ref_count;
   
    // Kind. It's a type tag and the operator.
    enumeration<Kind,unsigned char> _kind;

    // The vector of children
    ASTVec _children;

    //Nodenum is a unique positive integer for the node.  The nodenum
    //of a node should always be greater than its descendents (which
    //is easily achieved by incrementing the number each time a new
    //node is created).
    //FIXME: Get rid of this
    unsigned int _node_num;

    /*******************************************************************
     * ASTNode is of type BV      <==> ((indexwidth=0)&&(valuewidth>0))*
     * ASTNode is of type ARRAY   <==> ((indexwidth>0)&&(valuewidth>0))*
     * ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))*
     *                                                                 *
     * Width of the index of an array. Positive for array, 0 otherwise *
     *******************************************************************/
#ifdef LESSBYTES_PERNODE
    unsigned char _index_width;
#else
    unsigned int  _index_width;
#endif

    /*******************************************************************
     * ASTNode is of type BV      <==> ((indexwidth=0)&&(valuewidth>0))*
     * ASTNode is of type ARRAY   <==> ((indexwidth>0)&&(valuewidth>0))*
     * ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))*
     *                                                                 *
     * Number of bits of bitvector. +ve for array/bitvector,0 otherwise*
     *******************************************************************/
#ifdef LESSBYTES_PERNODE
    unsigned char _value_width;
#else
    unsigned int  _value_width;
#endif

    /****************************************************************
     * Protected Member Functions                                   *
     ****************************************************************/

    // Copying assign operator.  Also copies contents of children.
    ASTInternal& operator=(const ASTInternal &int_node);

    // Cleanup function for removing from hash table
    virtual void CleanUp() = 0;

    // Destructor (does nothing, but is declared virtual here.
    virtual ~ASTInternal()
    {
    }

    // Abstract virtual print function for internal node. c_friendly
    // is for printing hex. numbers that C compilers will accept
    virtual void nodeprint(ostream& os, bool c_friendly = false)
    {
      os << "*";
    }
    ;

    // Treat the result as const pleases
    virtual Kind GetKind() const
    {
      return _kind;
    }

    // Get the child nodes of this node
    virtual ASTVec const &GetChildren() const
    {
      return _children;
    }

  public:

    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/
    
    // Constructor
    ASTInternal(int nodenum = 0) :
      _ref_count(0), _kind(UNDEFINED),
      _node_num(nodenum), 
      _index_width(0), _value_width(0)
    {
    }

    // Constructor (kind only, empty children, int nodenum)
    ASTInternal(Kind kind, int nodenum = 0) :
      _ref_count(0), _kind(kind),
      _node_num(nodenum),
      _index_width(0), _value_width(0)
    {
    }

    // Constructor (kind and children).
    ASTInternal(Kind kind, const ASTVec &children, int nodenum = 0) :
      _ref_count(0), _kind(kind), _children(children), 
      _node_num(nodenum),
      _index_width(0), _value_width(0)
    {
    }

    // Copy constructor.  This copies the contents of the child nodes
    // array, along with everything else.  Assigning the smart pointer,
    // ASTNode, does NOT invoke this; This should only be used for
    // temporary hash keys before uniquefication.
    // FIXME:  I don't think children need to be copied.
    ASTInternal(const ASTInternal &int_node, int nodenum = 0) :
      _ref_count(0), _kind(int_node._kind), 
      _children(int_node._children),
      _node_num(int_node._node_num), 
      _index_width(int_node._index_width), 
      _value_width(int_node._value_width)
    {
    }

    // Increment Reference Count
    void IncRef()
    {
      ++_ref_count;
    }

    // Decrement Reference Count
    void DecRef();

    int GetNodeNum() const
    {
      return _node_num;
    }

    void SetNodeNum(int nn)
    {
      _node_num = nn;
    }
    ;
  }; //End of Class ASTInternal

}; //end of namespace
#endif
