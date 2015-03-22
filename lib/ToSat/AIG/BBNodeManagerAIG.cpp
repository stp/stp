/********************************************************************
 * AUTHORS: Unknown
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

#include "stp/ToSat/AIG/BBNodeManagerAIG.h"
#include "abc/aig.h"
#include "abc/cnf.h"
#include "abc/dar.h"

// FIXME: What is the point of this??
namespace stp
{

BBNodeAIG BBNodeManagerAIG::CreateNode(Kind kind, vector<BBNodeAIG>& children)
{
  Aig_Obj_t* pNode;
  assert(children.size() != 0);

  for (size_t i = 0, size = children.size(); i < size; ++i)
    assert(!children[i].IsNull());

  switch (kind)
  {
    case AND:
      if (children.size() == 1)
        pNode = children[0].n;
      else if (children.size() == 2)
        pNode = Aig_And(aigMgr, children[0].n, children[1].n);
      else
        pNode = makeTower(Aig_And, children);
      break;

    case OR:
      if (children.size() == 1)
        pNode = children[0].n;
      else if (children.size() == 2)
        pNode = Aig_Or(aigMgr, children[0].n, children[1].n);
      else
        pNode = makeTower(Aig_Or, children);
      break;

    case NAND:
      if (children.size() == 2)
        pNode = Aig_And(aigMgr, children[0].n, children[1].n);
      else
        pNode = makeTower(Aig_And, children);
      pNode = Aig_Not(pNode);
      break;

    case NOT:
      assert(children.size() == 1);
      pNode = Aig_Not(children[0].n);
      break;

    case NOR:
      if (children.size() == 2)
        pNode = Aig_Or(aigMgr, children[0].n, children[1].n);
      else
        pNode = makeTower(Aig_Or, children);
      pNode = Aig_Not(pNode);
      break;

    case XOR:
      if (children.size() == 2)
        pNode = Aig_Exor(aigMgr, children[0].n, children[1].n);
      else
        pNode = makeTower(Aig_Exor, children);
      break;

    case IFF:
      assert(children.size() == 2);
      pNode = Aig_Exor(aigMgr, children[0].n, children[1].n);
      pNode = Aig_Not(pNode);
      break;

    case IMPLIES:
      assert(children.size() == 2);
      pNode = Aig_Or(aigMgr, Aig_Not(children[0].n), children[1].n);
      break;

    case ITE:
      assert(children.size() == 3);
      pNode = Aig_Mux(aigMgr, children[0].n, children[1].n, children[2].n);
      break;

    default:
      cerr << "Not handled::!!" << _kind_names[kind];
      FatalError("Never here");
  }
  return BBNodeAIG(pNode);
}

int BBNodeManagerAIG::totalNumberOfNodes()
{
  return aigMgr->nObjs[AIG_OBJ_AND]; // without having removed non-reachable.
}

BBNodeManagerAIG::BBNodeManagerAIG() : aigMgr(NULL)
{
  aigMgr = Aig_ManStart(0);
  // fancier strashing.
  aigMgr->fAddStrash = 1;
}

void BBNodeManagerAIG::stop()
{
  if (aigMgr != NULL)
    Aig_ManStop(aigMgr);
  aigMgr = NULL;
}

BBNodeManagerAIG::~BBNodeManagerAIG() { stop(); }

BBNodeAIG BBNodeManagerAIG::getTrue() { return BBNodeAIG(Aig_ManConst1(aigMgr)); }

BBNodeAIG BBNodeManagerAIG::getFalse() { return BBNodeAIG(Aig_ManConst0(aigMgr)); }

// The same symbol always needs to return the same AIG node,
// if it doesn't you will get the wrong answer.
BBNodeAIG BBNodeManagerAIG::CreateSymbol(const ASTNode& n, unsigned i)
{
  assert(n.GetKind() == SYMBOL);

  // booleans have width 0.
  const unsigned width = std::max((unsigned)1, n.GetValueWidth());

  SymbolToBBNode::iterator it;
  it = symbolToBBNode.find(n);
  if (symbolToBBNode.end() == it)
  {
    symbolToBBNode[n] = vector<BBNodeAIG>(width);
    it = symbolToBBNode.find(n);
  }

  assert(it->second.size() == width);
  assert(i < width);

  if (!it->second[i].IsNull())
    return it->second[i];

  it->second[i] = BBNodeAIG(Aig_ObjCreatePi(aigMgr));
  it->second[i].symbol_index = aigMgr->vPis->nSize - 1;
  return it->second[i];
}

BBNodeAIG
BBNodeManagerAIG::CreateNode(Kind kind, const BBNodeAIG& child0,
           const vector<BBNodeAIG>& back_children)
{
  vector<BBNodeAIG> front_children;
  front_children.reserve(1 + back_children.size());
  front_children.push_back(child0);
  front_children.insert(front_children.end(), back_children.begin(),
                        back_children.end());
  return CreateNode(kind, front_children);
}

BBNodeAIG
BBNodeManagerAIG::CreateNode(Kind kind, const BBNodeAIG& child0, const BBNodeAIG& child1,
           const vector<BBNodeAIG>& back_children)
{
  vector<BBNodeAIG> front_children;
  front_children.reserve(2 + back_children.size());
  front_children.push_back(child0);
  front_children.push_back(child1);
  front_children.insert(front_children.end(), back_children.begin(),
                        back_children.end());
  return CreateNode(kind, front_children);
}

BBNodeAIG
BBNodeManagerAIG::CreateNode(Kind kind, const BBNodeAIG& child0, const BBNodeAIG& child1,
           const BBNodeAIG& child2,
           const vector<BBNodeAIG>& back_children)
{
  vector<BBNodeAIG> front_children;
  front_children.reserve(3 + back_children.size());
  front_children.push_back(child0);
  front_children.push_back(child1);
  front_children.push_back(child2);
  front_children.insert(front_children.end(), back_children.begin(),
                        back_children.end());
  return CreateNode(kind, front_children);
}

}
