#ifndef PRINTERS_H_
#define PRINTERS_H_

#include "../AST.h"
#include "../ASTUtil.h"
#include "../ASTKind.h"


namespace printer
{

	ostream& Dot_Print(ostream &os, const BEEV::ASTNode n);
	ostream& SMTLIB_Print(ostream &os, const BEEV::ASTNode n, const int indentation=0);
	ostream& C_Print(ostream &os, const BEEV::ASTNode n, const int indentation=0);
}

#endif /* PRINTERS_H_ */
