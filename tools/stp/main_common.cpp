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

#include "main_common.h"
#include "extlib-abc/cnf_short.h"
#include "stp/Parser/parser.h"
#include "stp/cpp_interface.h"
#include "stp/ToSat/ToSATAIG.h"
#include <memory>


extern void errorHandler(const char* error_msg);

using namespace stp;
using std::unique_ptr;
using std::cout;
using std::cerr;
using std::endl;

void errorHandler(const char* error_msg)
{
  cerr << "STP Error: " << error_msg << endl;
  exit(-1);
}

Main::Main() : onePrintBack(false)
{
  bm = NULL;
  toClose = NULL;
  setCVCIn(NULL);
  setSMTIn(NULL);
  setSMT2In(NULL);

  // Register the error handler
  vc_error_hdlr = errorHandler;

  bm = new STPMgr();
  GlobalParserBM = bm;
}

Main::~Main()
{
  delete bm;
}

void Main::printVersionInfo()
{
  cout << "STP version " << stp::get_git_version_tag() << std::endl;
  cout << "STP version SHA string " << stp::get_git_version_sha() << std::endl;
  cout << "STP compilation options " << stp::get_compilation_env() << std::endl;
#ifdef __GNUC__
  cout << "c compiled with gcc version " << __VERSION__ << endl;
#else
  cout << "c compiled with non-gcc compiler" << endl;
#endif
}

void Main::parse_file(ASTVec* AssertsQuery)
{
  TypeChecker nfTypeCheckSimp(*bm->defaultNodeFactory, *bm);
  TypeChecker nfTypeCheckDefault(*bm->hashingNodeFactory, *bm);

  Cpp_interface piTypeCheckSimp(*bm, &nfTypeCheckSimp);
  Cpp_interface piTypeCheckDefault(*bm, &nfTypeCheckDefault);

  // If you are converting formats, you probably don't want it simplifying
  if (onePrintBack)
  {
    GlobalParserInterface = &piTypeCheckDefault;
  }
  else
  {
    GlobalParserInterface = &piTypeCheckSimp;
  }

  GlobalParserInterface->startup();

  if (onePrintBack)
  {
    if (bm->UserFlags.smtlib2_parser_flag)
    {
      cerr << "Printback from SMTLIB2 inputs isn't currently working." << endl;
      cerr << "Please try again later" << endl;
      cerr << "It works prior to revision 1354" << endl;
      exit(1);
    }
  }

  if (bm->UserFlags.smtlib1_parser_flag)
  {
    SMTParse((void*)AssertsQuery);
    smtlex_destroy();
  }
  else if (bm->UserFlags.smtlib2_parser_flag)
  {
    SMT2Parse();
    smt2lex_destroy();
  }
  else
  {
    CVCParse((void*)AssertsQuery);
    cvclex_destroy();
  }
  GlobalParserInterface = NULL;
  if (toClose != NULL)
  {
    fclose(toClose);
  }
}

void Main::print_back(ASTNode& query, ASTNode& asserts)
{
  ASTNode original_input =
      bm->CreateNode(AND, bm->CreateNode(NOT, query), asserts);

  if (bm->UserFlags.print_STPinput_back_flag)
  {
    if (bm->UserFlags.smtlib1_parser_flag)
    {
      bm->UserFlags.print_STPinput_back_SMTLIB2_flag = true;
    }
    else
    {
      bm->UserFlags.print_STPinput_back_CVC_flag = true;
    }
  }

  if (bm->UserFlags.print_STPinput_back_CVC_flag)
  {
    // needs just the query. Reads the asserts out of the data structure.
    print_STPInput_Back(original_input, bm);
  }

  if (bm->UserFlags.print_STPinput_back_SMTLIB1_flag)
  {
    printer::SMTLIB1_PrintBack(cout, original_input, bm);
  }

  if (bm->UserFlags.print_STPinput_back_SMTLIB2_flag)
  {
    printer::SMTLIB2_PrintBack(cout, original_input, bm);
  }

  if (bm->UserFlags.print_STPinput_back_C_flag)
  {
    printer::C_Print(cout, original_input, bm);
  }

  if (bm->UserFlags.print_STPinput_back_GDL_flag)
  {
    printer::GDL_Print(cout, original_input);
  }

  if (bm->UserFlags.print_STPinput_back_dot_flag)
  {
    printer::Dot_Print(cout, original_input);
  }
}

void Main::read_file()
{
  bool error = false;
  if (bm->UserFlags.smtlib1_parser_flag)
  {
    setSMTIn(fopen(infile.c_str(), "r"));
    toClose = getSMTIn();
    if (getSMTIn() == NULL)
    {
      error = true;
    }
  }
  else if (bm->UserFlags.smtlib2_parser_flag)
  {
    setSMT2In(fopen(infile.c_str(), "r"));
    toClose = getSMT2In();
    if (getSMT2In() == NULL)
    {
      error = true;
    }
  }
  else
  {
    setCVCIn(fopen(infile.c_str(), "r"));
    toClose = getCVCIn();
    if (getCVCIn() == NULL)
    {
      error = true;
    }
  }

  if (error)
  {
    std::string errorMsg("Cannot open ");
    errorMsg += infile;
    FatalError(errorMsg.c_str());
  }
}

int Main::create_and_parse_options(int /*argc*/, char** /*argv*/)
{
  return 0;
}

void Main::check_infile_type()
{
  if (infile.size() >= 5)
  {
    if (!infile.compare(infile.length() - 4, 4, ".cvc"))
    {
      bm->UserFlags.smtlib1_parser_flag = false;
      bm->UserFlags.smtlib2_parser_flag = false;
    }

    if (!infile.compare(infile.length() - 4, 4, ".smt"))
    {
      bm->UserFlags.smtlib1_parser_flag = true;
      bm->UserFlags.smtlib2_parser_flag = false;
    }
    if (!infile.compare(infile.length() - 5, 5, ".smt2"))
    {
      bm->UserFlags.smtlib1_parser_flag = false;
      bm->UserFlags.smtlib2_parser_flag = true;
    }
  }
}

int Main::main(int argc, char** argv)
{
  auto simplifyingNF = std::make_unique<SimplifyingNodeFactory> (*bm->hashingNodeFactory, *bm);
  bm->defaultNodeFactory = simplifyingNF.get();

  int ret = create_and_parse_options(argc, argv);
  if (ret != 0)
  {
    return ret;
  }

  // ensure that all output is (at most) line buffered
  setvbuf(stdout, NULL, _IOLBF, 0);

  STP* stp = new STP(bm);

  GlobalSTP = stp;
  // If we're not reading the file from stdin.
  if (!infile.empty())
    read_file();

  // want to print the output always from the commandline.
  bm->UserFlags.print_output_flag = true;
  ASTVec* AssertsQuery = new ASTVec;

  bm->GetRunTimes()->start(RunTimes::Parsing);
  parse_file(AssertsQuery);
  bm->GetRunTimes()->stop(RunTimes::Parsing);

  GlobalSTP = NULL;

  /*  The SMTLIB2 has a command language. The parser calls all the functions,
   *  so when we get to here the parser has already called "exit". i.e. if the
   *  language is smt2 then all the work has already been done, and all we need
   *  to do is cleanup...
   *    */
  if (!bm->UserFlags.smtlib2_parser_flag)
  {
    if (AssertsQuery->empty())
      FatalError("Input is Empty. Please enter some asserts and query\n");

    if (AssertsQuery->size() != 2)
      FatalError("Input must contain a query\n");

    ASTNode asserts = (*AssertsQuery)[0];
    ASTNode query = (*AssertsQuery)[1];

    if (onePrintBack)
    {
      print_back(query, asserts);
    }
    else
    {
      SOLVER_RETURN_TYPE ret = stp->TopLevelSTP(asserts, query);

      if (bm->UserFlags.quick_statistics_flag)
      {
        bm->GetRunTimes()->print();
      }
      stp->tosat->PrintOutput(ret);
    }

    asserts = ASTNode();
    query = ASTNode();
  }

  // Save time by not calling the destructors.
  #ifdef NDEBUG
    std::exit(0);
  #endif


  //Cleanup
  AssertsQuery->clear();
  delete AssertsQuery;
  _empty_ASTVec.clear();
  delete stp;
  CNFClearMemory();

  return 0;
}
