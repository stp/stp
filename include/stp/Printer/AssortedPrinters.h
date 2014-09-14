// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef PRINTER_H
#define PRINTER_H

#include "stp/AST/AST.h"
namespace BEEV
{

  /***************************************************************************
 Class LispPrinter:  iomanipulator for printing ASTNode or ASTVec
  ***************************************************************************/
  class LispPrinter
  {

  public:
    ASTNode _node;

    // number of spaces to print before first real character of
    // object.
    int _indentation;

    // FIXME: pass ASTNode by reference
    // Constructor to build the LispPrinter object
    LispPrinter(ASTNode node, int indentation) :
      _node(node), _indentation(indentation)
    {
    }

    friend ostream &operator<<(ostream &os, const LispPrinter &lp)
    {
      return lp._node.LispPrint(os, lp._indentation);
    }
    ;

  }; //End of ListPrinter

  //global function which accepts an integer and looks up the
  //corresponding ASTNode and prints a string of that ASTNode
  void Convert_MINISATVar_To_ASTNode_Print(int minisat_var,
                                           int decision, int polarity=0);

  void print_STPInput_Back(const ASTNode& query);
} // end of namespace BEEV
#endif
