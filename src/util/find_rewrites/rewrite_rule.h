#ifndef REWRITERULE_H
#define REWRITERULE_H

#include "../../STPManager/STPManager.h"
#include "misc.h"

void
soft_time_out(int ignored)
{
  mgr->soft_timeout_expired = true;
}

bool
orderEquivalence(ASTNode& from, ASTNode& to);

class Rewrite_rule
{
  ASTNode from;
  ASTNode to;
  ASTNode n;

  int time_to_verify;
  int verified_to_bits;

  // Only used to build the NULL rule
  Rewrite_rule()
  {
    from = mgr->CreateZeroConst(1);
    to = mgr->CreateZeroConst(1);
    n = mgr->ASTTrue;
  }

public:

  static Rewrite_rule
  getNullRule()
  {
    return Rewrite_rule();
  }

  void
  writeOut(ostream& outputFileSMT2) const
  {
    outputFileSMT2 << ";id:0" << "\tverified_to:" << verified_to_bits << "\ttime:" << getTime() << "\tfrom_difficulty:"
        << getDifficulty(getFrom()) << "\tto_difficulty:" << getDifficulty(getTo()) << "\n";
    outputFileSMT2 << "(push 1)" << endl;
    printer::SMTLIB2_PrintBack(outputFileSMT2, getN(), true);
    outputFileSMT2 << "(exit)" << endl;
  }

  // If we've verified it to bigger than before. Then store the bit / time.
  void
  setVerified(int bits_, int time_)
  {
    if (bits_ >= verified_to_bits)
      {
        verified_to_bits = bits_;
        time_to_verify = time_;
      }
  }

  int
  getVerifiedToBits() const
  {
    return verified_to_bits;
  }

  const ASTNode&
  getFrom() const
  {
    return from;
  }

  const ASTNode&
  getTo() const
  {
    return to;
  }

  int
  getTime() const
  {
    return time_to_verify;
  }

  ASTNode
  getN() const
  {
    return n;
  }

  bool
  operator==(const Rewrite_rule& t) const
  {
    return (n == t.n);
  }

  // The "from" and "to" should be ordered with the orderEquivalence function.
  Rewrite_rule(BEEV::STPMgr* bm, const BEEV::ASTNode& from_, const BEEV::ASTNode& to_, const int t, int _id = -1) :
      from(from_), to(to_)
  {
#if 0
    if (_id ==-1)
    id = static_id++;
    else
      {
        id =_id; // relied on to be unique. So be careful.
        static_id =id+1;// assuming we are loading them all up..
      }
#endif
    verified_to_bits = 0;
    time_to_verify = t;

    ASTVec c;
    c.push_back(to_);
    c.push_back(from_);
    n = bm->hashingNodeFactory->CreateNode(BEEV::EQ, c);

    assert(orderEquivalence(from,to));
    assert(from == from_);
    assert(to == to_);
    assert(BVTypeCheckRecursive(n));
    assert(!n.isConstant());
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

        bool result = isConstant(widened, assignment, i);
        if (!result && !mgr->soft_timeout_expired)
          {
            // not a constant, and not timed out!
            cerr << "FAILED:" << endl << i << from << to;
            writeOut(cerr);

            // The timer might not have expired yet.
            setitimer(ITIMER_VIRTUAL, NULL, NULL);
            mgr->soft_timeout_expired = false;
            return false;
          }
        if (mgr->soft_timeout_expired)
          break;

        checked_to = i;
      }

    if (getVerifiedToBits() <= checked_to)
      setVerified(checked_to, getTime() + (getCurrentTime() - st));

    // The timer might not have expired yet.
    setitimer(ITIMER_VIRTUAL, NULL, NULL);
    mgr->soft_timeout_expired = false;
    return true;
  }

};
#endif
