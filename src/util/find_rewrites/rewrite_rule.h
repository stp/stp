#ifndef REWRITERULE_H
#define REWRITERULE_H

#include "../../STPManager/STPManager.h"

extern const int widen_to;
extern const int bits;

ASTNode
widen(const ASTNode& w, int width);

int
getDifficulty(const ASTNode& n_);

void soft_time_out(int ignored)
{
  mgr->soft_timeout_expired = true;
}

bool
isConstant(const ASTNode& n, VariableAssignment& different);


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

   int time_to_verify;
   int verified_to_bits;

public:

  void writeOut(ostream& outputFileSMT2)
  {
    assert(isOK());
    outputFileSMT2 << ";id:" << getId()
        << "\tverified_to:" << verified_to_bits << "\ttime:" << getTime()
        << "\tfrom_difficulty:" << getDifficulty(getFrom())
        << "\tto_difficulty:"   << getDifficulty(getTo())
        << "\n";
    outputFileSMT2 << "(push 1)" << endl;
    printer::SMTLIB2_PrintBack(outputFileSMT2, getN(), true, false);
    outputFileSMT2 << "(exit)" << endl;
  }

  // If we've verified it to bigger than before. Then store the bit / time.
  void
  setVerified(int bits_, int time_)
  {
    if (bits_ > verified_to_bits)
      {
        verified_to_bits = bits_;
        time_to_verify = time_;
      }
  }

  int
  getVerifiedToBits()
  {
    return verified_to_bits;
  }

  const ASTNode&
  getFrom() const
  {return from;}

  const ASTNode&
  getTo() const
  {return to;}

  int
  getTime() const
  {return time_to_verify;}

  ASTNode
  getN() const
  {
    return n;
  }

  int
  getId() const
  {
    return id;
  }

  bool
  sameID(const Rewrite_rule& t) const
  {
    return (*this == t);

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
    ASTNode w = widen(getN(), widen_to);

    if  (w.IsNull() || w.GetKind() == UNDEFINED)
      return false;

    assert(BVTypeCheckRecursive(n));
    assert(BVTypeCheckRecursive(w));

    if (from.isAtom() && to.isAtom())
        return false;

    if (from == to)
      return false;

    return true;

  }

  Rewrite_rule(BEEV::STPMgr* bm, const BEEV::ASTNode& from_, const BEEV::ASTNode& to_, const int t, int _id=-1)
  : from(from_), to(to_)
    {
      if (_id ==-1)
        id = static_id++;
      else
        {
          id =_id; // relied on to be unique. So be careful.
          static_id =id+1; // assuming we are loading them all up..
        }
      verified_to_bits = 0;
      time_to_verify = t;

      ASTVec c;
      c.push_back(to_);
      c.push_back(from_);
      n =  bm->hashingNodeFactory->CreateNode(BEEV::EQ,c);


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

  // Tests for the timeout amount of time. FALSE if a bad instance was found. Otherwise true.
  bool
  timedCheck(int timeout_ms)
  {
    VariableAssignment assignment;

    mgr->soft_timeout_expired = false;
    itimerval timeout;
    signal(SIGVTALRM, soft_time_out);
    timeout.it_interval.tv_usec = 0;
    timeout.it_interval.tv_sec = 0;
    timeout.it_value.tv_usec = 1000 * (timeout_ms % 1000);
    timeout.it_value.tv_sec = timeout_ms / 1000;
    setitimer(ITIMER_VIRTUAL, &timeout, NULL);

    const int st = getCurrentTime();
    int checked_to = 0;

    // Start it verifying where we left off..
    for (int i = std::max(bits, getVerifiedToBits() + 1); i < 1024; i++)
      {
        //cout << i << " ";
        ASTVec children;
        children.push_back(from);
        children.push_back(to);

        const ASTNode n = mgr->hashingNodeFactory->CreateNode(EQ, children);
        const ASTNode& widened = widen(n, i);
        if (widened == mgr->ASTUndefined)
          {
            cout << "cannot widen";
            cerr << from << to;
          }

        bool result = isConstant(widened, assignment);
        if (!result && !mgr->soft_timeout_expired)
          {
            // not a constant, and not timed out!
            cerr << "FAILED:" << getId() << endl << i << from << to;
            writeOut(cerr);
            return false;
          }
        if (mgr->soft_timeout_expired)
          break;

        checked_to = i;
      }

    if (getVerifiedToBits() <= checked_to)
      setVerified(checked_to, getTime() + (getCurrentTime() - st));

    return true;
  }

};
#endif
