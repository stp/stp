#ifndef REWRITESYSTEM_H
#define REWRITESYSTEM_H

#include "rewrite_rule.h"

extern const int widen_to;
extern ASTNode v, v0, w, w0;
extern NodeFactory* nf;
extern BEEV::STPMgr* mgr;

bool
orderEquivalence(ASTNode& from, ASTNode& to);

ASTNode
create(Kind k, const ASTNode& n0, const ASTNode& n1);


template<class T>
  void
  removeDuplicates(T & big);

ASTNode
widen(const ASTNode& w, int width);

bool
unifyNode(const ASTNode& n0, const ASTNode& n1,  ASTNodeMap& fromTo);

ASTNode
renameVars(const ASTNode &n);

ASTNode
rewrite(const ASTNode&n, const Rewrite_rule& original_rule, ASTNodeMap& seen);

bool
checkRule(const ASTNode & from, const ASTNode & to, VariableAssignment& assignment, bool&bad);

ASTNode
renameVarsBack(const ASTNode &n);

ASTNode
rename_then_rewrite(ASTNode n, const Rewrite_rule& original_rule);

bool
isConstantToSat(const ASTNode & query);


class Rewrite_system
{
private:

  friend void writeOutRules(string fileName);

  friend ASTNode  rewrite(const ASTNode&n, const Rewrite_rule& original_rule, ASTNodeMap& seen);

  // Rules to write out when we get the chance.
  vector<Rewrite_rule> toWrite;
  std::map< Kind, vector<Rewrite_rule> > kind_to_rr;
  std::map< Kind, std::map< Kind, vector<Rewrite_rule> > > kind_kind_to_rr;

public:

  Rewrite_system()
  {
  }

  void
  buildRules()
  {
    kind_to_rr.clear();
    kind_kind_to_rr.clear();

    for (int i = 0; i < toWrite.size(); i++)
      {
        ASTNode from = toWrite[i].getFrom();
        kind_to_rr[from.GetKind()].push_back(toWrite[i]);

        if (from[0].Degree() > 0)
          kind_kind_to_rr[from.GetKind()][from[0].GetKind()].push_back(toWrite[i]);
      }
  }

  void
  eraseDuplicates()
  {
    removeDuplicates(toWrite);
  }

  void
  push_back(Rewrite_rule rr)
  {
    toWrite.push_back(rr);
  }

  int
  size() const
  {
    return toWrite.size();
  }

  ASTNode rewriteNode(ASTNode n)
  {
    Rewrite_rule  null_rule( Rewrite_rule(mgr,mgr->CreateZeroConst(1), mgr->CreateZeroConst(1),0));
    return rename_then_rewrite(n,null_rule);
  }

  void
  rewriteAll()
  {
    eraseDuplicates();
    cerr << "Size before rewriteAll:" << toWrite.size() << endl;

    buildRules();

    for (int i = 0; i < toWrite.size(); i++)
      {
        if (i % 1000 == 0)
          cerr << "rewrite all:" << i << " of " << toWrite.size() << endl;

        if (!toWrite[i].isOK())
          {
            toWrite.erase(toWrite.begin() + i);
            i--;
            continue;
          }

        ASTNode n = renameVars(toWrite[i].getFrom());
        ASTNodeMap seen;
        ASTNode rewritten_from = rewrite(n, toWrite[i],seen);

        if (n != rewritten_from)
          {
            assert (isConstantToSat(create(EQ, rewritten_from,n)));

            rewritten_from = renameVarsBack(rewritten_from);
            ASTNode to = toWrite[i].getTo();
            bool r = orderEquivalence(rewritten_from, to);
            if (r)
              {
                Rewrite_rule rr(mgr, rewritten_from, to, 0);
                if (rr.isOK())
                  {
                    toWrite[i] = rr;
                    buildRules(); // Otherwise two rules will remove each other?
                  }
                else
                  {
                    cout << "Erasing rule";
                    toWrite.erase(toWrite.begin() + i);
                    i--;
                  }
              }
            else
              {
                cerr << "Mapped but couldn't order";
                cerr << rewritten_from << to;
              }
          }
      }

    eraseDuplicates();
    cerr << "Size after rewriteAll:" << toWrite.size() << endl;
  }

  void clear()
  {
    toWrite.clear();
  }

  void
  verifyAllwithSAT()
  {
    for (int i = 0; i < toWrite.size(); i++)
      {
        VariableAssignment assignment;
        bool bad = false;
        const int st = getCurrentTime();
        bool r = checkRule(toWrite[i].getFrom(), toWrite[i].getTo(), assignment, bad);
        if (!r || bad)
          {
            cerr << "Bad to, then from" << endl;
            cerr << toWrite[i].getFrom();
            cerr << toWrite[i].getTo();
            assert(r);
            assert(!bad);
          }
        toWrite[i].time = getCurrentTime() - st;
      }
  }
};
#endif
