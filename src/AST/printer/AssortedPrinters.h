// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef PRINTER_H
#define PRINTER_H

#include "../AST.h"

namespace BEEV
{
  using namespace std;

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

  /***************************************************************************/
  /*  Class LispVecPrinter:iomanipulator for printing vector of ASTNodes     */
  /***************************************************************************/
  class LispVecPrinter
  {

  public:
    const ASTVec * _vec;
    // number of spaces to print before first real
    // character of object.
    int _indentation;

    // Constructor to build the LispPrinter object
    LispVecPrinter(const ASTVec &vec, int indentation)
    {
      _vec = &vec;
      _indentation = indentation;
    }

    friend ostream &operator<<(ostream &os, const LispVecPrinter &lvp)
    {
      LispPrintVec(os, *lvp._vec, lvp._indentation);
      return os;
    }
    ;
  }; //End of Class ListVecPrinter
};// end of namespace BEEV
#endif
