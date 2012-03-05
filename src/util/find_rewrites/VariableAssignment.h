/*
 * VariableAssignment.h
 *
 */

#ifndef VARIABLEASSIGNMENT_H_
#define VARIABLEASSIGNMENT_H_

extern ASTNode v, v0, w ,w0;
extern NodeFactory* nf;
extern BEEV::STPMgr* mgr;


struct VariableAssignment
{
private:
  ASTNode v;
  ASTNode w;

public:
  ASTNode
  getV() const
  {
    assert(v.isConstant());
    return v;
  }

  ASTNode
  getW() const
  {
    assert(w.isConstant());
    return w;
  }

  void
  setV(const ASTNode& nv)
  {
    assert(nv.isConstant());
    v = nv;
  }

  void
  setW(const ASTNode& nW)
  {
    assert(nW.isConstant());
    w = nW;
  }

  bool
  isEmpty()
  {
    return (v == mgr->ASTUndefined || w == mgr->ASTUndefined);
  }

  VariableAssignment()
  {
  }

  // Generate w from v a bit randomly.
  explicit
  VariableAssignment(const ASTNode & n)
  {
    setV(n);
    srand(v.GetUnsignedConst());
    w = mgr->CreateBVConst(n.GetValueWidth(), rand());
  }

  VariableAssignment(ASTNode & n0, ASTNode & n1)
  {
    setV(n0);
    setV(n1);
  }
};


#endif /* VARIABLEASSIGNMENT_H_ */
