// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef ASTBVCONST_H
#define ASTBVCONST_H
namespace BEEV
{
  void FatalError(const char * str);

  /******************************************************************
   *  Class ASTBVConst:                                             *
   *                                                                *
   *  Class to represent internals of a bitvector constant          *
   ******************************************************************/
  class ASTBVConst: public ASTInternal
  {
    friend class BeevMgr;
    friend class ASTNode;
    friend class ASTNodeHasher;
    friend class ASTNodeEqual;

  private:
    /****************************************************************
     * Private Data                                                 *
     ****************************************************************/

    //CBV is actually an unsigned*. The bitvector constant is
    //represented using an external library in extlib-bvconst.
    CBV _bvconst;

    /****************************************************************
     * Class ASTBVConstHasher:                                      *
     *                                                              *
     * Hasher for ASTBVConst nodes                                  *
     ****************************************************************/
    class ASTBVConstHasher
    {
    public:
      size_t operator()(const ASTBVConst * bvc) const
      {
        return CONSTANTBV::BitVector_Hash(bvc->_bvconst);
      }
      ;
    };

    /****************************************************************
     * Class ASTBVConstEqual:                                       *
     *                                                              *
     * Equality for ASTBVConst nodes                                *
     ****************************************************************/
    class ASTBVConstEqual
    {
    public:
      bool operator()(const ASTBVConst * bvc1, 
		      const ASTBVConst * bvc2) const
      {
        if (bvc1->_value_width != bvc2->_value_width)
          {
            return false;
          }
        return (0 == 
		CONSTANTBV::BitVector_Compare(bvc1->_bvconst, 
					      bvc2->_bvconst));
      }
    };


    /****************************************************************
     * Private Functions (virtual defs and friends)                 *
     ****************************************************************/
    ASTBVConst(CBV bv, unsigned int width) :
      ASTInternal(BVCONST)
    {
      _bvconst = CONSTANTBV::BitVector_Clone(bv);
      _value_width = width;
    }

    friend bool operator==(const ASTBVConst &bvc1, const ASTBVConst &bvc2)
    {
      if (bvc1._value_width != bvc2._value_width)
        return false;
      return (0 == CONSTANTBV::BitVector_Compare(bvc1._bvconst, 
						 bvc2._bvconst));
    }

    // Call this when deleting a node that has been stored in the the
    // unique table
    virtual void CleanUp();

    // Print function for bvconst -- return _bvconst value in bin
    // format (c_friendly is for printing hex. numbers that C
    // compilers will accept)
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
      ASTInternal(sym._kind, sym._children)
    {
      _bvconst = CONSTANTBV::BitVector_Clone(sym._bvconst);
      _value_width = sym._value_width;
    }

  public:

    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/

    //Destructor. Call the external destructor
    virtual ~ASTBVConst()
    {
      CONSTANTBV::BitVector_Destroy(_bvconst);
    }

    // Return the bvconst. It is a const-value
    CBV GetBVConst() const
    {
      return _bvconst;
    }
  }; //End of ASTBVConst
};//end of namespace
#endif
