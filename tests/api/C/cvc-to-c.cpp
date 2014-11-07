/***********
AUTHORS:  Philip Guo, Vijay Ganesh, Mate Soos, Dan Liew

BEGIN DATE: Feb, 2009

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
**********************/

/*
Take a .cvc file specified by argv[1] and transform to C code
g++ -I$HOME/stp/c_interface cvc-to-c.cpp -L$HOME/stp/lib -lstp -o cvc-to-c
*/

#include "stp/c_interface.h"
#include <iostream>

int main(int argc, char** argv) {
  VC vc = vc_createValidityChecker();

  //vc_setFlags(vc,'n');
  //vc_setFlags(vc,'d');
  //vc_setFlags(vc,'p');

  Expr c = vc_parseExpr(vc, argv[1]);

  vc_printExprCCode(vc, c);

  vc_Destroy(vc);
  return 0;
}

