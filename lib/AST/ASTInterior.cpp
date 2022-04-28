/********************************************************************
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

#include "stp/AST/ASTInterior.h"
#include "stp/STPManager/STPManager.h"
namespace stp
{
/******************************************************************
 * ASTInterior Member Functions                                   *
 ******************************************************************/

// Call this when deleting a node that has been stored in the
// the unique table
void ASTInterior::CleanUp()
{
  nodeManager->_interior_unique_table.erase(this);
  delete this;
}

// Returns kinds.  "lispprinter" handles printing of parenthesis
// and childnodes. (c_friendly is for printing hex. numbers that C
// compilers will accept)
void ASTInterior::nodeprint(ostream& os, bool /*c_friendly*/)
{
  os << _kind_names[_kind];
}

/******************************************************************
 * ASTInteriorHasher and ASTInteriorEqual Member Functions        *
 ******************************************************************/

// ASTInteriorHasher operator()
size_t ASTInterior::ASTInteriorHasher::
operator()(const ASTInterior* int_node_ptr) const
{
  size_t hashval = ((size_t)int_node_ptr->GetKind());
  const ASTVec& ch = int_node_ptr->GetChildren();
  ASTVec::const_iterator iend = ch.end();
  for (ASTVec::const_iterator i = ch.begin(); i != iend; i++)
  {
    hashval += i->Hash();
    hashval += (hashval << 10);
    hashval ^= (hashval >> 6);
  }

  hashval += (hashval << 3);
  hashval ^= (hashval >> 11);
  hashval += (hashval << 15);
  return hashval;
}

// ASTInteriorEqual operator()
bool ASTInterior::ASTInteriorEqual::
operator()(const ASTInterior* int_node_ptr1,
           const ASTInterior* int_node_ptr2) const
{
  return (*int_node_ptr1 == *int_node_ptr2);
}

ASTInterior::~ASTInterior()
{
}

} // end of namespace
