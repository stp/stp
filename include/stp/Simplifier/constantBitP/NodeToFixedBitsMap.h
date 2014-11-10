// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: July, 2010
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

/*
 * pimpl class to make compiling easier.
 */

#ifndef NODETOFIXEDBITSMAP_H_
#define NODETOFIXEDBITSMAP_H_

#include "stp/AST/AST.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"

namespace simplifier
{
namespace constantBitP
{

class NodeToFixedBitsMap
{
public:
  typedef hash_map<BEEV::ASTNode, FixedBits*, BEEV::ASTNode::ASTNodeHasher,
                   BEEV::ASTNode::ASTNodeEqual> NodeToFixedBitsMapType;

  NodeToFixedBitsMapType* map;

  NodeToFixedBitsMap(int size) { map = new NodeToFixedBitsMapType(size); }
  virtual ~NodeToFixedBitsMap()
  {
    clear();
    delete map;
  }

  void clear()
  {
    NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator itD = map->begin();
    for (; itD != map->end(); itD++)
      delete itD->second;
    map->clear();
  }
};
}
}

#endif /* NODETOFIXEDBITSMAP_H_ */
