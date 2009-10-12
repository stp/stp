/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#ifndef PRINTERS_H_
#define PRINTERS_H_
#include <iostream>
#include <vector>
#include <cstring>

#include "../AST/AST.h"
#include "../AST/ASTKind.h"
#include "../STPManager/STP.h"

//using namespace std;
namespace printer
{
  ostream& Dot_Print(ostream &os, const BEEV::ASTNode n);

  ostream& SMTLIB_Print(ostream &os, 
			const BEEV::ASTNode n, const int indentation = 0);
  ostream& C_Print(ostream &os, 
		   const BEEV::ASTNode n, const int indentation = 0);
  ostream& PL_Print(ostream &os, 
		    const BEEV::ASTNode& n, int indentation=0);

  ostream& Lisp_Print(ostream &os, 
		      const BEEV::ASTNode& n,  int indentation=0);
  ostream& Lisp_Print_indent(ostream &os,  
			     const BEEV::ASTNode& n,int indentation=0);
  void SMTLIB_PrintBack(ostream &os, 
			const BEEV::ASTNode& n );

}

#endif /* PRINTERS_H_ */
