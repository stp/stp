// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "AST.h"
namespace BEEV
{
  /****************************************************************
   * ASTBVConst Member Function definitions                       *
   ****************************************************************/

  //Constructor
  ASTBVConst::ASTBVConst(CBV bv, unsigned int width) :
    ASTInternal(BVCONST)
  {
    _bvconst = CONSTANTBV::BitVector_Clone(bv);
    _value_width = width;
  } //End of ASTBVConst constructor

  // Copy constructor.
  ASTBVConst::ASTBVConst(const ASTBVConst &sym) :
    ASTInternal(sym._kind, sym._children)
  {
    _bvconst = CONSTANTBV::BitVector_Clone(sym._bvconst);
    _value_width = sym._value_width;
  } //End of copy constructor()

  // Call this when deleting a node that has been stored in the the
  // unique table
  void ASTBVConst::CleanUp()
  {
    GlobalBeevMgr->_bvconst_unique_table.erase(this);
    delete this;
  } //End of Cleanup()

  // Print function for bvconst -- return _bvconst value in bin
  // format (c_friendly is for printing hex. numbers that C
  // compilers will accept)
  void ASTBVConst::nodeprint(ostream& os, bool c_friendly)
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
  } //End of nodeprint()

  // Return the bvconst. It is a const-value
  CBV ASTBVConst::GetBVConst() const
  {
    return _bvconst;
  } //End of GetBVConst()
};//End of namespace

