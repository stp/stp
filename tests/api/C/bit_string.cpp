/***********
AUTHORS:   Andrew V. Jones

BEGIN DATE: July, 2020

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
#include "stp/c_interface.h"
#include <gtest/gtest.h>
#include <string>

TEST(bit_string, one)
{
  // Random input bit string
  std::string bit_string("0101010101");

  // Create a STP VC
  VC vc = vc_createValidityChecker();

  // Create an expression from our original bit string
  Expr e = vc_bvConstExprFromStr(vc, bit_string.c_str());

  // Convert it back to a bit string
  char* buf;
  unsigned long len;
  vc_printBVBitStringToBuffer(e, &buf, &len);

  // 'buf' should now be allocated
  assert(buf);

  // Get the resulting std::string
  std::string result = std::string(buf);

  // Free the STP-allocated buffer
  free(buf);

  // strings should be equal
  assert(result == bit_string);

  // Free the VC
  vc_Destroy(vc);
}
