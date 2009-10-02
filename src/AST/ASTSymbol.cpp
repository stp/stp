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
   * ASTSymbol Member Function definitions                        *
   ****************************************************************/

  // Get the name of the symbol
  const char * ASTSymbol::GetName() const
  {
    return _name;
  }//End of GetName()
  
  // Print function for symbol -- return name. (c_friendly is for
  // printing hex. numbers that C compilers will accept)
  void ASTSymbol::nodeprint(ostream& os, bool c_friendly)
  {
    os << _name;
  } //end of nodeprint()

  // Call this when deleting a node that has been stored in the the
  // unique table
  void ASTSymbol::CleanUp()
  {
    GlobalBeevMgr->_symbol_unique_table.erase(this);
    free((char*) this->_name);
    delete this;
  }//End of cleanup()
};//end of namespace
