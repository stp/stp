/********************************************************************
 * AUTHORS: Mate Soos
 *
 * BEGIN DATE: Nov, 2014
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

#include "../stp/main_common.h"
#include <iostream>

using namespace stp;

class SimpleMain : public Main
{
public:
  virtual int create_and_parse_options(int argc, char** argv);
};

int SimpleMain::create_and_parse_options(int argc, char** argv)
{
  bm->UserFlags.smtlib2_parser_flag = true;

  for (int i = 1; i < argc; i++)
  {
    if (std::string(argv[i]) == "--array-equality")
    {
      bm->UserFlags.enable_array_equality = true;
    }
    else if (infile.empty())
    {
      infile = argv[i];
      check_infile_type();
    }
    else
    {
      std::cerr << "Only --array-equality and one input file are allowed"
                << std::endl;
      exit(-1);
    }
  }

  return 0;
}

int main(int argc, char** argv)
{
  SimpleMain main;
  return main.main(argc, argv);
}
