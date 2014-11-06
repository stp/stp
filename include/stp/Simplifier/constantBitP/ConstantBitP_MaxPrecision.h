// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: Februrary, 2010
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ********************************************************************/

#ifndef CONSTANTBITPROPAGATION_MAXPRECISION_H_
#define CONSTANTBITPROPAGATION_MAXPRECISION_H_

#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include <vector>
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/AST/ASTKind.h"



namespace simplifier
{
namespace constantBitP
{

   enum Direction
   {
     UPWARDS_ONLY, BOTH_WAYS
   };

   // This is used for very specific purposes.
   enum Type
   {
     BOOL_TYPE, VALUE_TYPE
   };

struct Signature
{
	BEEV::Kind kind;
	Type resultType;
	Type inputType;
	int maxInputWidth;
	int numberOfInputs;
	Direction direction;
	bool imprecise;
	Signature()
	{
		imprecise=false;
	}
};

bool maxPrecision(std::vector<FixedBits*> children, FixedBits& output, BEEV::Kind kind, BEEV::STPMgr* beev);
}
}

#endif /* CONSTANTBITPROPAGATION_MAXPRECISION_H_ */
