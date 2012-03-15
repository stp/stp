#ifndef VARIABLEASSIGNMENT_H_
#define VARIABLEASSIGNMENT_H_

// A pair of constants of the same bit-width assigned to v and w..

struct VariableAssignment
{
private:
  ASTNode v;
  ASTNode w;
  bool empty;

public:
  ASTNode
  getV() const
  {
    assert(!empty);
    return v;
  }

  ASTNode
  getW() const
  {
    assert(!empty);
    return w;
  }

  void
  setValues(const ASTNode& nv, const ASTNode& nw)
  {
    assert(nv.isConstant());
    assert(nw.isConstant());
    assert(nw.GetValueWidth() == nv.GetValueWidth());
    w = nw;
    v = nv;
    empty = false;
  }

  VariableAssignment()
  {
    empty = true;
  }

};

#endif
