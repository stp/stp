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

bool
isConstant(const ASTNode& n, VariableAssignment& different);

class Rewrite_system
{
public:

  // Rules to write out when we get the chance.
  typedef list<Rewrite_rule> RewriteRuleContainer;

private:

  friend
  void
  writeOutRules();


  friend ASTNode rewrite(const ASTNode&n, const Rewrite_rule& original_rule, ASTNodeMap& seen);

  RewriteRuleContainer toWrite;
  std::map< Kind, vector<Rewrite_rule> > kind_to_rr;
  std::map< Kind, std::map< Kind, vector<Rewrite_rule> > > kind_kind_to_rr;

public:

  Rewrite_system()
  {
  }

  RewriteRuleContainer::iterator
  begin()
  {
    return toWrite.begin();
  }

  RewriteRuleContainer::iterator
  end()
  {
    return toWrite.end();
  }


  void
  addRuleToLookup(Rewrite_rule& r)
  {
    const ASTNode& from = r.getFrom();
    kind_to_rr[from.GetKind()].push_back(r);

    assert(from.Degree() > 0); // Shouldn't map from a constant, nor from a variable.

    if (from[0].Degree() > 0)
      kind_kind_to_rr[from.GetKind()][from[0].GetKind()].push_back(r);
  }

  void
  deleteID(int id)
  {
    for (RewriteRuleContainer::iterator it = toWrite.begin() ; it != toWrite.end(); it++)
      {
        if (it->getId() == id)
          {
            toWrite.erase(it--);
            cerr << "matched" << id;
          }
      }
  }

  void
  buildLookupTable()
  {
    kind_to_rr.clear();
    kind_kind_to_rr.clear();

    for (RewriteRuleContainer::iterator it = toWrite.begin() ; it != toWrite.end(); it++)
      {
        addRuleToLookup(*it);
      }
  }

  void
  removeBad()
  {
    for (RewriteRuleContainer::iterator it = toWrite.begin() ; it != toWrite.end(); it++)
      {
        if (!it->isOK())
          {
            cout << "Removing Rule that is bad";
            cout << it->getFrom();
            cout << it->getTo();
            cout << "----\n";

            toWrite.erase(it--);
          }
      }
  }

  void
  eraseDuplicates()
  {
    removeBad();
    toWrite.sort();
    toWrite.unique();
  }

  void
  push_back(Rewrite_rule rr)
  {
    toWrite.push_back(rr);
    addRuleToLookup(rr);
  }

  void
  erase(RewriteRuleContainer::iterator it)
  {
    toWrite.erase(it);
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
    cout << "Size before rewriteAll:" << toWrite.size() << endl;

    buildLookupTable();

    int i=0;
    for (RewriteRuleContainer::iterator it = toWrite.begin() ; it != toWrite.end(); it++, i++)
      {
        if (i % 1000 == 0)
          cout << "rewrite all:" << i << " of " << toWrite.size() << endl;

        // if not OK, should have been removed during duplicates.
        // shouldn't add extra rules that aren't ok.
        assert (it->isOK());

        ASTNode n = renameVars(it->getFrom());
        ASTNodeMap seen;
        ASTNode rewritten_from = rewrite(n, *it,seen);

        if (n != rewritten_from)
          {
            assert (isConstantToSat(create(EQ, rewritten_from,n)));

            rewritten_from = renameVarsBack(rewritten_from);
            ASTNode to = it->getTo();
            bool ok = orderEquivalence(rewritten_from, to);
            if (ok)
              {
                Rewrite_rule rr(mgr, rewritten_from, to, 0);
                if (rr.isOK())
                  {
                    cout << "Modifying Rule\n";
                    cout << "Initially From";
                    cout << it->getFrom();
                    cout << "new From";
                    cout << rewritten_from;
                    cout << "---";

                    *it= rr;
                    buildLookupTable(); // Otherwise two rules will remove each other?
                  }
                else
                  {
                    cout << "Erasing rule";
                    cout << "Initially From";
                    cout << it->getFrom();
                    cout << "new From";
                    cout << rewritten_from;
                    cout << "---";

                    erase(it--);
                    i--;
                    buildLookupTable(); // Otherwise two rules will remove each other?
                  }
              }
            else
              {
                if (rewritten_from != to)
                  {
                      cout << "Mapped but couldn't order";
                      cout << rewritten_from << to;
                  }
                erase(it--);
                i--;
                buildLookupTable(); // Otherwise two rules will remove each other?
              }
          }
      }

    eraseDuplicates();
    cout << "Size after rewriteAll:" << toWrite.size() << endl;
  }

  void clear()
  {
    toWrite.clear();
  }

  void
  verifyAllwithSAT()
  {
    for (RewriteRuleContainer::iterator it = toWrite.begin() ; it != toWrite.end(); it++)
      {
        VariableAssignment assignment;
        bool bad = false;
        const int st = getCurrentTime();
        bool r = checkRule(it->getFrom(), it->getTo(), assignment, bad);
        if (!r || bad)
          {
            cout << "Bad to, then from" << endl;
            cout << it->getFrom();
            cout << it->getTo();
            assert(r);
            assert(!bad);
          }
        if (bits > it->getVerifiedToBits())
          it->setVerified(bits,getCurrentTime() - st);
      }
  }


  void
  writeOut(ostream &o)
  {
    for (RewriteRuleContainer::iterator it = toWrite.begin() ; it != toWrite.end(); it++)
      {
        it->writeOut(o);
      }
  }
};
#endif
