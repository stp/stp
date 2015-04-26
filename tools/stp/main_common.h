/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen, Mate Soos
 *
 * BEGIN DATE: November, 2005
 *
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
********************************************************************/

#ifndef __MAIN_COMMON_H__
#define __MAIN_COMMON_H__

#include <stdio.h>
#include "STPProgramGlobals.h"
#include "stp/AST/AST.h"
#include "stp/Printer/AssortedPrinters.h"
#include "stp/Printer/printers.h"
#include "stp/STPManager/STPManager.h"
#include "stp/STPManager/STP.h"
#include "stp/AST/NodeFactory/TypeChecker.h"
#include "stp/AST/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/cpp_interface.h"
#include <sys/time.h>
#include <memory>
#include <string>
#include <stdio.h>
#include "stp/Util/GitSHA1.h"

class Main
{
public:
  Main();
  virtual ~Main();
  int main(int argc, char** argv);
  void parse_file(ASTVec* AssertsQuery);
  void print_back(ASTNode& query, ASTNode& asserts);
  void read_file();

  STPMgr* bm;
  bool onePrintBack;
  FILE* toClose;

  virtual int create_and_parse_options(int argc, char** argv);

  // Files to read
  std::string infile;
  void check_infile_type();

  // For options
  int64_t max_num_confl;
  size_t random_seed;
};

#endif //__MAIN_COMMON_H__
