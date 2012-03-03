#ifndef REWRITERULE_H
#define REWRITERULE_H

#include "../../STPManager/STPManager.h"

extern const int widen_to;
extern const int bits;

ASTNode
widen(const ASTNode& w, int width);

vector<ASTNode>
getVariables(const ASTNode& n);

class Rewrite_rule
{
private:
   ASTNode from;
   ASTNode to;
   ASTNode n;

  int id;

  static int  static_id;

public:

  int time;

  const ASTNode&
  getFrom() const
  {return from;}

  const ASTNode&
  getTo() const
  {return to;}

  int
  getTime() const
  {return time;}

  ASTNode
  getN() const
  {
    return n;
  }

  bool
  sameID(const Rewrite_rule& t) const
  {
    if  (id == t.id)
      {
        assert(n == t.n);
        return true;
      }
    return false;
  }

  bool
  operator==(const Rewrite_rule& t) const
  {
    return (n == t.n);
  }

  bool
  isOK()
  {
    if (getN().GetKind() != EQ)
      return false;

    ASTNode w = widen(getN(), widen_to);

    BVTypeCheckRecursive(n);
    BVTypeCheckRecursive(w);

    if  (w.IsNull() || w.GetKind() == UNDEFINED)
      return false;

    if (from.isAtom() && to.isAtom())
        return false;

    if (from == to)
      return false;

    return true;

  }

  Rewrite_rule(BEEV::STPMgr* bm, const BEEV::ASTNode& from_, const BEEV::ASTNode& to_, const int t)
  : from(from_), to(to_), n ( bm->CreateNode(BEEV::EQ,to_,from_))
    {
      id = static_id++;

      time = t;

      ////
      assert(!from.IsNull());
      assert(from.GetKind() != UNDEFINED);

      ////
      assert(!to.IsNull());
      assert(to.GetKind() != UNDEFINED);

      ////
      assert(!n.IsNull());
      assert(n.GetKind() != UNDEFINED);
      ////

      if (from.GetKind() == SYMBOL)
        {
          assert(to == from); // If it's a symbol. It should be the same one.
        }

      if (from.isAtom())
        {
          assert(to.isAtom()); // sometimes its easiest to make it 0->0 rather than deleting it.
        }

      // only v or w
      vector<ASTNode> s_from= getVariables(from);
      for (vector<ASTNode>::iterator it = s_from.begin(); it != s_from.end() ;it++)
        {
          assert(strlen(it->GetName()) ==1);
          assert(it->GetName()[0] =='v' || it->GetName()[0] =='w');
          assert(it->GetValueWidth() == bits);
        }

      vector<ASTNode> s_to= getVariables(to);
      for (vector<ASTNode>::iterator it = s_to.begin(); it != s_to.end() ;it++)
        {
          assert(strlen(it->GetName()) ==1);
          assert(it->GetName()[0] =='v' || it->GetName()[0] =='w');
          assert(it->GetValueWidth() == bits);
        }

      // The "to" side should have fewer nodes.
      assert(s_from.size() >= s_to.size());
    }

  bool
  operator<(const Rewrite_rule& t) const
  {
    return (n < t.n);
  }
};
#endif
