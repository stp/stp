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
matchNode(const ASTNode& n0, const ASTNode& n1,  ASTNodeMap& fromTo, const int term_variable_width);

bool
commutative_matchNode(const ASTNode& n0, const ASTNode& n1, ASTNodeMap& fromTo, const int term_variable_width);


ASTNode
renameVars(const ASTNode &n);

ASTNode
rewrite(const ASTNode&n, const Rewrite_rule& original_rule, ASTNodeMap& seen, int depth);

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

ASTNode
rewriteThroughWithAIGS(const ASTNode &n_);


class Rewrite_system
{
public:

  // Rules to write out when we get the chance.
  typedef list<Rewrite_rule> RewriteRuleContainer;

private:

  friend
  void
  writeOutRules();

  friend ASTNode rewrite(const ASTNode&n, const Rewrite_rule& original_rule, ASTNodeMap& seen, int depth);

  RewriteRuleContainer toWrite;

  std::map< Kind, vector<Rewrite_rule> > kind_to_rr;
   bool lookups_invalid; // whether the above table is bad.

  void
  addRuleToLookup(Rewrite_rule& r)
  {
    const ASTNode& from = r.getFrom();
    kind_to_rr[from.GetKind()].push_back(r);
    assert(from.Degree() > 0); // Shouldn't map from a constant, nor from a variable.
  }


public:

  bool
  checkInvariant()
  {
    int size=0;
    std::map< Kind, vector<Rewrite_rule> >::iterator it;
    for(it=kind_to_rr.begin();it != kind_to_rr.end();it++)
      {
        for (int i=0; i < it->second.size();i++)
          {
            assert(it->second[i].getFrom().GetKind() == it->first); // All have the same kind as the lookup kind.
          }
        size+= it->second.size();
      }

    return size == toWrite.size();
  }

  Rewrite_system()
  {
    lookups_invalid = false;
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

  bool areLookupsGood()
  {
    return lookups_invalid;
  }

  void
  buildLookupTable()
  {
    kind_to_rr.clear();

    for (RewriteRuleContainer::iterator it = toWrite.begin() ; it != toWrite.end(); it++)
      {
        addRuleToLookup(*it);
      }
    lookups_invalid =false;
  }

  void
  eraseDuplicates()
  {
    toWrite.sort();
    toWrite.unique();
    lookups_invalid = true;
  }

  // Rewrite the "from" and "To", add the rule if it's still good.
  // NB: Doesn't rebuild the lookup table.
  void
  push_back(Rewrite_rule& rr)
  {
    toWrite.push_back(rr);
    addRuleToLookup(rr);
  }

  void
  erase(RewriteRuleContainer::iterator it)
  {
    toWrite.erase(it);
    lookups_invalid = true;
  }

  int
  size() const
  {
    return toWrite.size();
  }

  static ASTNode rewriteNode(ASTNode n)
  {
    return rename_then_rewrite(n,Rewrite_rule::getNullRule());
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

        ASTNode from_wide = renameVars(it->getFrom());
        ASTNode to_wide = renameVars(it->getTo());

        // The renamed should match the original, and vice versa.
          {
            ASTNodeMap fromTo;
            assert(commutative_matchNode(from_wide, it->getFrom(),fromTo,2));
            fromTo.clear();
            assert(commutative_matchNode(it->getFrom(), from_wide, fromTo, 1));
            fromTo.clear();
            assert(commutative_matchNode(to_wide, it->getTo(),fromTo,2));
            fromTo.clear();
            assert(commutative_matchNode(it->getTo(),to_wide, fromTo,1));
          }

        ASTNodeMap seen;
        ASTNode from_wide_rewritten = rewrite(from_wide, *it,seen,0);
        seen = ASTNodeMap();
        ASTNode to_wide_rewritten = rewrite(to_wide, *it,seen,0);
        seen = ASTNodeMap();

        // Also apply the AIG rules.
        to_wide_rewritten = rewriteThroughWithAIGS(to_wide_rewritten);

        if ((from_wide != from_wide_rewritten) || (to_wide != to_wide_rewritten))
          {
            ASTNode from_rewritten = renameVarsBack(from_wide_rewritten);
            ASTNode to_rewritten = renameVarsBack(to_wide_rewritten);

            assert(BVTypeCheckRecursive(from_rewritten));
            assert(BVTypeCheckRecursive(to_rewritten));

            assert (isConstantToSat(create(EQ, from_wide_rewritten,from_wide)));
            assert (isConstantToSat(create(EQ, to_wide_rewritten,to_wide)));
            assert (isConstantToSat(create(EQ, it->getFrom(),from_rewritten)));
            assert (isConstantToSat(create(EQ, it->getTo(),to_rewritten)));

            bool ok = orderEquivalence(from_rewritten, to_rewritten);
            if (ok)
              {
                Rewrite_rule rr(mgr, from_rewritten, to_rewritten, 0);
                cout << "Modifying Rule\n";
                cout << "Initially From";
                cout << it->getFrom();
                cout << "Initially To";
                cout << it->getTo();
                cout << "New From";
                cout << from_rewritten;
                cout << "New To";
                cout << to_rewritten;
                cout << "---";
                cout << getDifficulty(rr.getFrom()) << " --> " << getDifficulty(rr.getTo()) << endl;

                *it = rr;
                lookups_invalid = true;

              }
            if (!ok)
            {
                cout << "Erasing bad rule.\n";
                erase(it--);
                i--;
                lookups_invalid = true;
              }
          }
      }

    eraseDuplicates();
    cout << "Size after rewriteAll:" << toWrite.size() << endl;
    buildLookupTable();
  }

  void clear()
  {
    toWrite.clear();
    buildLookupTable();
  }

  void
  verifyAllwithSAT()
  {
    cerr << "Started verifying all" << endl;
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
        if (bits >= it->getVerifiedToBits())
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
