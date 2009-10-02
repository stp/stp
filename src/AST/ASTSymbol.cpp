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

  
  /****************************************************************
   * ASTSymbolHasher and ASTSymbolEqual functions                 *
   *                                                              *   
   ****************************************************************/
  size_t 
  ASTSymbol::ASTSymbolHasher::operator()(const ASTSymbol *sym_ptr) const
  {
#ifdef TR1_UNORDERED_MAP
    tr1::hash<string> h;
#else
    hash<char*> h;
#endif
    return h(sym_ptr->_name);
  } //End of ASTSymbolHasher operator

  bool ASTSymbol::ASTSymbolEqual::operator()(const ASTSymbol *sym_ptr1, 
					     const ASTSymbol *sym_ptr2) const
  {
    return (*sym_ptr1 == *sym_ptr2);
  } //End of ASTSymbolEqual operator
};//end of namespace
