// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

// to get the PRIu64 macro from inttypes, this needs to be defined.
#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#include <cmath>
#include "../sat/sat.h"
#include "../STPManager/STPManager.h"

namespace BEEV
{
  ASTInterior *STPMgr::LookupOrCreateInterior(ASTInterior *n_ptr)
  {
    ASTInteriorSet::iterator it = _interior_unique_table.find(n_ptr);
    if (it == _interior_unique_table.end())
      {
        // Make a new ASTInterior node We want (NOT alpha) always to
        // have alpha.nodenum + 1.
        if (n_ptr->GetKind() == NOT)
          {
            n_ptr->SetNodeNum(n_ptr->GetChildren()[0].GetNodeNum() + 1);
          }
        else
          {
            n_ptr->SetNodeNum(NewNodeNum());
          }
        pair<ASTInteriorSet::const_iterator, bool> p = 
          _interior_unique_table.insert(n_ptr);
        return *(p.first);
      }
    else
      // Delete the temporary node, and return the found node.
      delete n_ptr;
    return *it;
  }

  
 
  ////////////////////////////////////////////////////////////////
  //  STPMgr members
  ////////////////////////////////////////////////////////////////
  ASTNode STPMgr::CreateNode(Kind kind, const ASTVec & back_children)
  {
    // create a new node.  Children will be modified.
    ASTInterior *n_ptr = new ASTInterior(kind);

    // insert all of children at end of new_children.
    ASTNode n(CreateInteriorNode(kind, n_ptr, back_children));
    return n;
  }

  ASTNode STPMgr::CreateNode(Kind kind, 
                             const ASTNode& child0, 
                             const ASTVec & back_children)
  {

    ASTInterior *n_ptr = new ASTInterior(kind);
    ASTVec &front_children = n_ptr->_children;
    front_children.push_back(child0);
    ASTNode n(CreateInteriorNode(kind, n_ptr, back_children));
    return n;
  }

  ASTNode STPMgr::CreateNode(Kind kind, 
                             const ASTNode& child0, 
                             const ASTNode& child1, 
                             const ASTVec & back_children)
  {
    ASTInterior *n_ptr = new ASTInterior(kind);
    ASTVec &front_children = n_ptr->_children;
    front_children.push_back(child0);
    front_children.push_back(child1);
    ASTNode n(CreateInteriorNode(kind, n_ptr, back_children));
    return n;
  }

  ASTNode STPMgr::CreateNode(Kind kind, 
                             const ASTNode& child0, 
                             const ASTNode& child1, 
                             const ASTNode& child2, 
                             const ASTVec & back_children)
  {
    ASTInterior *n_ptr = new ASTInterior(kind);
    ASTVec &front_children = n_ptr->_children;
    front_children.push_back(child0);
    front_children.push_back(child1);
    front_children.push_back(child2);
    ASTNode n(CreateInteriorNode(kind, n_ptr, back_children));
    return n;
  }

  ASTInterior *STPMgr::CreateInteriorNode(Kind kind,
                                          // children array of this node will be modified.
                                          ASTInterior *n_ptr,
                                          const ASTVec & back_children)
  {

    // insert back_children at end of front_children
    ASTVec &front_children = n_ptr->_children;

    front_children.insert(front_children.end(), 
                          back_children.begin(), 
                          back_children.end());

    // check for undefined nodes.
    ASTVec::const_iterator it_end = front_children.end();
    for (ASTVec::const_iterator it = front_children.begin(); it != it_end; it++)
      {
        if (it->IsNull())
          {
            FatalError("CreateInteriorNode:"\
                       "Undefined childnode in CreateInteriorNode: ", 
                       ASTUndefined);
          }
      }

    return LookupOrCreateInterior(n_ptr);
  }

  ostream &operator<<(ostream &os, const ASTNodeMap &nmap)
  {
    ASTNodeMap::const_iterator iend = nmap.end();
    for (ASTNodeMap::const_iterator i = nmap.begin(); i != iend; i++)
      {
        os << "Key: " << i->first << endl;
        os << "Value: " << i->second << endl;
      }
    return os;
  }

  ////////////////////////////////////////////////////////////////
  // STPMgr member functions to create ASTSymbol and ASTBVConst
  ////////////////////////////////////////////////////////////////
  ASTNode STPMgr::CreateSymbol(const char * const name)
  {
    ASTSymbol temp_sym(name);    
    ASTNode n(LookupOrCreateSymbol(temp_sym));
    return n;
  }

  // FIXME: _name is now a constant field, and this assigns to it
  // because it tries not to copy the string unless it needs to.  How
  // do I avoid copying children in ASTInterior?  Perhaps I don't!

  // Note: There seems to be a limitation of hash_set, in that insert
  // returns a const iterator to the value.  That prevents us from
  // modifying the name (in a hash-preserving way) after the symbol is
  // inserted.  FIXME: Is there a way to do this with insert?  Need a
  // function to make a new object in the middle of insert.  Read STL
  // documentation.
  ASTSymbol *STPMgr::LookupOrCreateSymbol(ASTSymbol& s)
  {
    ASTSymbol *s_ptr = &s; // it's a temporary key.

    //_symbol_unique_table.insert(s_ptr);
    //return s_ptr;
    // Do an explicit lookup to see if we need to create a copy of the
    // string.
    ASTSymbolSet::const_iterator it = _symbol_unique_table.find(s_ptr);
    if (it == _symbol_unique_table.end())
      {
        // Make a new ASTSymbol with duplicated string (can't assign
        // _name because it's const).  Can cast the iterator to
        // non-const -- carefully.
        //std::string strname(s_ptr->GetName());
        ASTSymbol * s_ptr1 = new ASTSymbol(strdup(s_ptr->GetName()));
        s_ptr1->SetNodeNum(NewNodeNum());
        s_ptr1->_value_width = s_ptr->_value_width;
        pair<ASTSymbolSet::const_iterator, bool> p = 
          _symbol_unique_table.insert(s_ptr1);
        return *p.first;
      }
    else
      {
        // return symbol found in table.
        return *it;
      }
  } // End of LookupOrCreateSymbol

  bool STPMgr::LookupSymbol(ASTSymbol& s)
  {
    ASTSymbol* s_ptr = &s; // it's a temporary key.

    if (_symbol_unique_table.find(s_ptr) == 
        _symbol_unique_table.end())
      return false;
    else
      return true;
  }

  //Create a ASTBVConst node
  ASTNode STPMgr::CreateBVConst(unsigned int width, unsigned long long int bvconst)
  {
    if (width > (sizeof(unsigned long long int) << 3) || width <= 0)
      FatalError("CreateBVConst: "\
                 "trying to create a bvconst using unsigned long long of width: ", 
                 ASTUndefined, width);

    CBV bv = CONSTANTBV::BitVector_Create(width, true);
    unsigned long c_val = (~((unsigned long) 0)) & bvconst;
    unsigned int copied = 0;

    // sizeof(unsigned long) returns the number of bytes in unsigned
    // long. In order to convert it to bits, we need to shift left by
    // 3. Hence, sizeof(unsigned long) << 3

    //The algo below works as follows: It starts by copying the
    //lower-order bits of the input "bvconst" in chunks of size =
    //number of bits in unsigned long. The variable "copied" keeps
    //track of the number of chunks copied so far

    int shift_amount = (sizeof(unsigned long) << 3);
    while (copied + (sizeof(unsigned long) << 3) < width)
      {
        CONSTANTBV::BitVector_Chunk_Store(bv, shift_amount, copied, c_val);
        bvconst = bvconst >> shift_amount;
        c_val = (~((unsigned long) 0)) & bvconst;
        copied += shift_amount;
      }
    CONSTANTBV::BitVector_Chunk_Store(bv, width - copied, copied, c_val);
    return CreateBVConst(bv, width);
  }

  ASTNode STPMgr::CreateBVConst(string*& strval, int base, int bit_width)
  {

    if (bit_width <= 0)
      FatalError("CreateBVConst: trying to create a bvconst of width: ", ASTUndefined, bit_width);


    if (!(2 == base || 10 == base || 16 == base))
      {
        FatalError("CreateBVConst: unsupported base: ", ASTUndefined, base);
      }

    //checking if the input is in the correct format
    CBV bv = CONSTANTBV::BitVector_Create(bit_width, true);
    CONSTANTBV::ErrCode e;
    if (2 == base)
      {
        e = CONSTANTBV::BitVector_from_Bin(bv, (unsigned char*) strval->c_str());
      }
    else if (10 == base)
      {
        e = CONSTANTBV::BitVector_from_Dec(bv, (unsigned char*) strval->c_str());
      }
    else if (16 == base)
      {
        e = CONSTANTBV::BitVector_from_Hex(bv, (unsigned char*) strval->c_str());
      }
    else
      {
        e = CONSTANTBV::ErrCode_Pars;
      }

    if (0 != e)
      {
        cerr << "CreateBVConst: " << BitVector_Error(e);
        FatalError("", ASTUndefined);
      }

    return CreateBVConst(bv, bit_width);
  }

  //Create a ASTBVConst node from std::string
  ASTNode STPMgr::CreateBVConst(const char* const strval, int base)
  {
    size_t width = strlen((const char *) strval);
    if (!(2 == base || 10 == base || 16 == base))
      {
        FatalError("CreateBVConst: unsupported base: ", ASTUndefined, base);
      }
    //FIXME Tim: Earlier versions of the code assume that the length of
    //binary strings is 32 bits.
    if (10 == base)
      width = 32;
    if (16 == base)
      width = width * 4;

    //checking if the input is in the correct format
    CBV bv = CONSTANTBV::BitVector_Create(width, true);
    CONSTANTBV::ErrCode e;
    if (2 == base)
      {
        e = CONSTANTBV::BitVector_from_Bin(bv, (unsigned char*) strval);
      }
    else if (10 == base)
      {
        e = CONSTANTBV::BitVector_from_Dec(bv, (unsigned char*) strval);
      }
    else if (16 == base)
      {
        e = CONSTANTBV::BitVector_from_Hex(bv, (unsigned char*) strval);
      }
    else
      {
        e = CONSTANTBV::ErrCode_Pars;
      }

    if (0 != e)
      {
        cerr << "CreateBVConst: " << BitVector_Error(e);
        FatalError("", ASTUndefined);
      }

    //FIXME
    return CreateBVConst(bv, width);
  }

  //FIXME Code currently assumes that it will destroy the bitvector passed to it
  ASTNode STPMgr::CreateBVConst(CBV bv, unsigned width)
  {
    ASTBVConst temp_bvconst(bv, width);
    ASTNode n(LookupOrCreateBVConst(temp_bvconst));

    CONSTANTBV::BitVector_Destroy(bv);

    return n;
  }

  ASTNode STPMgr::CreateZeroConst(unsigned width)
  {
    CBV z = CONSTANTBV::BitVector_Create(width, true);
    return CreateBVConst(z, width);
  }

  ASTNode STPMgr::CreateOneConst(unsigned width)
  {
    CBV o = CONSTANTBV::BitVector_Create(width, true);
    CONSTANTBV::BitVector_increment(o);

    return CreateBVConst(o, width);
  }

  ASTNode STPMgr::CreateTwoConst(unsigned width)
  {
    CBV two = CONSTANTBV::BitVector_Create(width, true);
    CONSTANTBV::BitVector_increment(two);
    CONSTANTBV::BitVector_increment(two);

    return CreateBVConst(two, width);
  }

  ASTNode STPMgr::CreateMaxConst(unsigned width)
  {
    CBV max = CONSTANTBV::BitVector_Create(width, false);
    CONSTANTBV::BitVector_Fill(max);

    return CreateBVConst(max, width);
  }

  //To ensure unique BVConst nodes, lookup the node in unique-table
  //before creating a new one.
  ASTBVConst *STPMgr::LookupOrCreateBVConst(ASTBVConst &s)
  {
    ASTBVConst *s_ptr = &s; // it's a temporary key.

    // Do an explicit lookup to see if we need to create a copy of the string.
    ASTBVConstSet::const_iterator it;
    if ((it = _bvconst_unique_table.find(s_ptr)) == _bvconst_unique_table.end())
      {
        // Make a new ASTBVConst with duplicated string (can't assign
        // _name because it's const).  Can cast the iterator to
        // non-const -- carefully.

        ASTBVConst * s_copy = new ASTBVConst(s);
        s_copy->SetNodeNum(NewNodeNum());

        pair<ASTBVConstSet::const_iterator, bool> p = _bvconst_unique_table.insert(s_copy);
        return *p.first;
      }
    else
      {
        // return symbol found in table.
        return *it;
      }
  }

  // Create and return an ASTNode for a term
  ASTNode STPMgr::CreateTerm(Kind kind, 
                             unsigned int width, 
                             const ASTVec &children)
  {
    if (!is_Term_kind(kind))
      FatalError("CreateTerm:  Illegal kind to CreateTerm:", 
                 ASTUndefined, kind);
    ASTNode n = CreateNode(kind, children);
    n.SetValueWidth(width);
    
    //by default we assume that the term is a Bitvector. If
    //necessary the indexwidth can be changed later
    n.SetIndexWidth(0);
    return n;
  }

  ASTNode STPMgr::CreateTerm(Kind kind, 
                             unsigned int width, 
                             const ASTNode& child0, 
                             const ASTVec &children)
  {
    if (!is_Term_kind(kind))
      FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);
    ASTNode n = CreateNode(kind, child0, children);
    n.SetValueWidth(width);
    BVTypeCheck(n);
    return n;
  }

  ASTNode STPMgr::CreateTerm(Kind kind, 
                             unsigned int width, 
                             const ASTNode& child0,
                             const ASTNode& child1, 
                             const ASTVec &children)
  {
    if (!is_Term_kind(kind))
      FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);
    ASTNode n = CreateNode(kind, child0, child1, children);
    n.SetValueWidth(width);
    return n;
  }
  
  ASTNode STPMgr::CreateTerm(Kind kind,
                             unsigned int width,
                             const ASTNode& child0,
                             const ASTNode& child1,
                             const ASTNode& child2,
                             const ASTVec &children)
  {
    if (!is_Term_kind(kind))
      FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);
    ASTNode n = CreateNode(kind, child0, child1, child2, children);
    n.SetValueWidth(width);
    return n;
  }


  ////////////////////////////////////////////////////////////////
  //
  //  IO manipulators for Lisp format printing of AST.
  //
  ////////////////////////////////////////////////////////////////

  // FIXME: Additional controls
  //   * Print node numbers  (addresses/nums)
  //   * Printlength limit
  //   * Printdepth limit

  /** Print a vector of ASTNodes in lisp format */
  ostream &LispPrintVec(ostream &os, const ASTVec &v, int indentation)
  {
    // Print the children
    ASTVec::const_iterator iend = v.end();
    for (ASTVec::const_iterator i = v.begin(); i != iend; i++)
      {
        i->LispPrint_indent(os, indentation);
      }
    return os;
  }

  ostream &LispPrintVecSpecial(ostream &os, const vector<const ASTNode*> &v, int indentation)
  {
    // Print the children
    vector<const ASTNode*>::const_iterator iend = v.end();
    for (vector<const ASTNode*>::const_iterator i = v.begin(); i != iend; i++)
      {
        (*i)->LispPrint_indent(os, indentation);
      }
    return os;
  }

  //add an assertion to the current logical context
  void STPMgr::AddAssert(const ASTNode& assert)
  {
    if (!(is_Form_kind(assert.GetKind()) && BOOLEAN_TYPE == assert.GetType()))
      {
        FatalError("AddAssert:Trying to assert a non-formula:", assert);
      }

    ASTVec * v;
    //if the stack of ASTVec is not empty, then take the top ASTVec
    //and add the input assert to it
    if (!_asserts.empty())
      {
        v = _asserts.back();
        //v->push_back(TransformFormula(assert));
        v->push_back(assert);
      }
    else
      {
        //else create a logical context, and add it to the top of the
        //stack
        v = new ASTVec();
        //v->push_back(TransformFormula(assert));
        v->push_back(assert);
        _asserts.push_back(v);
      }
  }

  void STPMgr::Push(void)
  {
    ASTVec * v;
    v = new ASTVec();
    _asserts.push_back(v);
  }

  void STPMgr::Pop(void)
  {
    if (!_asserts.empty())
      {
        ASTVec * c = _asserts.back();
        //by calling the clear function we ensure that the ref count is
        //decremented for the ASTNodes stored in c
        c->clear();
        delete c;
        _asserts.pop_back();
      }
  }

  void STPMgr::AddQuery(const ASTNode& q)
  {
    //_current_query = TransformFormula(q);
    //cerr << "\nThe current query is: " << q << endl;
    _current_query = q;
  }

  const ASTNode STPMgr::PopQuery()
  {
    ASTNode q = _current_query;
    _current_query = ASTTrue;
    return q;
  }

  const ASTNode STPMgr::GetQuery()
  {
    return _current_query;
  }

  const ASTVec STPMgr::GetAsserts(void)
  {
    vector<ASTVec *>::iterator it = _asserts.begin();
    vector<ASTVec *>::iterator itend = _asserts.end();

    ASTVec v;
    for (; it != itend; it++)
      {
        if (!(*it)->empty())
          v.insert(v.end(), (*it)->begin(), (*it)->end());
      }
    return v;
  }

  // //Create a new variable of ValueWidth 'n'
  //   ASTNode STPMgr::NewArrayVar(unsigned int index, unsigned int value)
  //   {
  //     std::string c("v");
  //     char d[32];
  //     sprintf(d, "%d", _symbol_count++);
  //     std::string ccc(d);
  //     c += "_writearray_" + ccc;

  //     ASTNode CurrentSymbol = CreateSymbol(c.c_str());
  //     CurrentSymbol.SetValueWidth(value);
  //     CurrentSymbol.SetIndexWidth(index);
  //     return CurrentSymbol;
  //   } //end of NewArrayVar()

  //prints statistics for the ASTNode
  void STPMgr::ASTNodeStats(const char * c, const ASTNode& a)
  {
    if (!UserFlags.stats_flag)
      return;

    StatInfoSet.clear();
    //print node size:
    cout << endl << "Printing: " << c;
    if (UserFlags.print_nodes_flag)
      {
        //a.PL_Print(cout,0);
        //cout << endl;
        cout << a << endl;
      }
    cout << "Node size is: ";
    cout << NodeSize(a) << endl;
  }

  unsigned int STPMgr::NodeSize(const ASTNode& a, bool clearStatInfo)
  {
    if (clearStatInfo)
      StatInfoSet.clear();

    ASTNodeSet::iterator it;
    if ((it = StatInfoSet.find(a)) != StatInfoSet.end())
      //has already been counted
      return 0;

    //record that you have seen this node already
    StatInfoSet.insert(a);
    // cout << "Number of bytes per Node is: ";
    // cout << sizeof(*(a._int_node_ptr)) << endl;

    //leaf node has a size of 1
    if (a.Degree() == 0)
      return 1;

    unsigned newn = 1;
    ASTVec c = a.GetChildren();
    for (ASTVec::iterator it = c.begin(), itend = c.end(); it != itend; it++)
      newn += NodeSize(*it);
    return newn;
  }

  // GLOBAL FUNCTION: Prints statistics from the MINISAT Solver
  void STPMgr::PrintStats(MINISAT::Solver& s)
  {
    if (!UserFlags.stats_flag)
      return;
    double cpu_time = MINISAT::cpuTime();
    uint64_t mem_used = MINISAT::memUsed();
    reportf("restarts              : %"PRIu64"\n",                      s.starts);
    reportf("conflicts             : %"PRIu64"   (%.0f /sec)\n",        s.conflicts   , s.conflicts   /cpu_time);
    reportf("decisions             : %"PRIu64"   (%.0f /sec)\n",        s.decisions   , s.decisions   /cpu_time);
    reportf("propagations          : %"PRIu64"   (%.0f /sec)\n",        s.propagations, s.propagations/cpu_time);
    reportf("conflict literals     : %"PRIu64"   (%4.2f %% deleted)\n", s.tot_literals,
            (s.max_literals - s.tot_literals)*100 / (double)s.max_literals);
    if (mem_used != 0)
      reportf("Memory used           : %.2f MB\n", mem_used / 1048576.0);
    reportf("CPU time              : %g s\n", cpu_time);
  } //end of PrintStats()


  //Create a new variable of ValueWidth 'n'
  ASTNode STPMgr::NewVar(unsigned int n)
  {
    std::string c("v");
    char d[32];
    sprintf(d, "%d", _symbol_count++);
    std::string ccc(d);
    c += "_solver_" + ccc;

    ASTNode CurrentSymbol = CreateSymbol(c.c_str());
    CurrentSymbol.SetValueWidth(n);
    CurrentSymbol.SetIndexWidth(0);
    return CurrentSymbol;
  } //end of NewVar()

  bool STPMgr::VarSeenInTerm(const ASTNode& var, const ASTNode& term)
  {
    if (READ == term.GetKind() 
        && WRITE == term[0].GetKind() 
        && !GetRemoveWritesFlag())
      {
        return false;
      }

    if (READ == term.GetKind() 
        && WRITE == term[0].GetKind() 
        && GetRemoveWritesFlag())
      {
        return true;
      }

    ASTNodeMap::iterator it;
    if ((it = TermsAlreadySeenMap.find(term)) != TermsAlreadySeenMap.end())
      {
        if (it->second == var)
          {
            return false;
          }
      }

    if (var == term)
      {
        return true;
      }

    for (ASTVec::const_iterator it = term.begin(), itend = term.end(); it != itend; it++)
      {
        if (VarSeenInTerm(var, *it))
          {
            return true;
          }
        else
          {
            TermsAlreadySeenMap[*it] = var;
          }
      }

    TermsAlreadySeenMap[term] = var;
    return false;
  }//End of VarSeenInTerm

  
  ASTNode STPMgr::NewParameterized_BooleanVar(const ASTNode& var,
                                              const ASTNode& constant)
  {
    ostringstream outVar;
    ostringstream outNum;
    //Get the name of Boolean Var
    var.PL_Print(outVar);
    constant.PL_Print(outNum);
    std::string str(outVar.str());
    str += "(";
    str += outNum.str();
    str += ")";
    ASTNode CurrentSymbol = CreateSymbol(str.c_str());
    CurrentSymbol.SetValueWidth(0);
    CurrentSymbol.SetIndexWidth(0);
    return CurrentSymbol;
  } // End of NewParameterized_BooleanVar()

}; // end namespace beev

