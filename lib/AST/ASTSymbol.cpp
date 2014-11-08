/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
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

#include "stp/AST/AST.h"
#include "stp/STPManager/STP.h"
namespace BEEV
{
  const ASTVec ASTSymbol::empty_children;


  /****************************************************************
   * ASTSymbol Member Function definitions                        *
   ****************************************************************/

  // Get the name of the symbol
  const char * ASTSymbol::GetName() const
  {
    return _name;
  }//End of GetName()
  
  // Print function for symbol -- return name. (c_friendly is for
  // printing hex. numbers that C compilers will accept)
  void ASTSymbol::nodeprint(ostream& os, bool c_friendly)
  {
    os << _name;
  } //end of nodeprint()

  // Call this when deleting a node that has been stored in the the
  // unique table
  void ASTSymbol::CleanUp()
  {
    (ParserBM)->_symbol_unique_table.erase(this);
    free((char*) this->_name);
    delete this;
  }//End of cleanup()

  unsigned long long hash(unsigned char *str)
  {
    unsigned long long hash = 5381;
    long long c;

    while ((c = *str++))
      hash = ((hash << 5) + hash) + c; /* hash * 33 + c */

    //cout << "Hash value computed is: " << hash << endl;

    return (unsigned long long)hash;
  }

} //end of namespace
