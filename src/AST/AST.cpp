/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "AST.h"

#include <assert.h>
#include "printer/printers.h"
#include "printer/AssortedPrinters.h"

namespace BEEV
{
  //some global variables that are set through commandline options. it
  //is best that these variables remain global. Default values set
  //here
  //
  //collect statistics on certain functions
  bool stats_flag = false;
  //print DAG nodes
  bool print_nodes_flag = false;
  //run STP in optimized mode
  bool optimize_flag = true;
  //do sat refinement, i.e. underconstraint the problem, and feed to
  //SAT. if this works, great. else, add a set of suitable constraints
  //to re-constraint the problem correctly, and call SAT again, until
  //all constraints have been added.
  bool arrayread_refinement_flag = true;
  //flag to control write refinement
  bool arraywrite_refinement_flag = true;
  //check the counterexample against the original input to STP
  bool check_counterexample_flag = false;
  //construct the counterexample in terms of original variable based
  //on the counterexample returned by SAT solver
  bool construct_counterexample_flag = true;
  bool print_counterexample_flag = false;
  bool print_binary_flag = false;
  //if this option is true then print the way dawson wants using a
  //different printer. do not use this printer.
  bool print_arrayval_declaredorder_flag = false;
  //flag to decide whether to print "valid/invalid" or not
  bool print_output_flag = false;
  //print the variable order chosen by the sat solver while it is
  //solving.
  bool print_sat_varorder_flag = false;
  //turn on word level bitvector solver
  bool wordlevel_solve_flag = true;
  //turn off XOR flattening
  bool xor_flatten_flag = false;
  //Flag to switch on the smtlib parser
  bool smtlib_parser_flag = false;
  //print the input back
  bool print_STPinput_back_flag = false;

  // If enabled. division, mod and remainder by zero will evaluate to 1.
  bool division_by_zero_returns_one = false;

  enum inputStatus input_status = NOT_DECLARED;

  // Used only in smtlib lexer/parser
  ASTNode SingleBitOne;
  ASTNode SingleBitZero;

  //global BEEVMGR for the parser
  BeevMgr * globalBeevMgr_for_parser;

  void (*vc_error_hdlr)(const char* err_msg) = NULL;
  /** This is reusable empty vector, for representing empty children arrays */
  ASTVec _empty_ASTVec;
  ////////////////////////////////////////////////////////////////
  //  ASTInternal members
  ////////////////////////////////////////////////////////////////
  /** Trivial but virtual destructor */
  ASTInternal::~ASTInternal()
  {
  }

  ////////////////////////////////////////////////////////////////
  //  ASTInterior members
  ////////////////////////////////////////////////////////////////
  /** Copy constructor */
  // ASTInterior::ASTInterior(const ASTInterior &int_node)
  // {
  //   _kind = int_node._kind;
  //   _children = int_node._children;
  // }

  /** Trivial but virtual destructor */
  ASTInterior::~ASTInterior()
  {
  }

  // FIXME: Darn it! I think this ends up copying the children twice!
  /** Either return an old node or create it if it doesn't exist.
      Note that nodes are physically allocated in the hash table. */

  // There is  an inelegance here that  I don't know how  to solve.  I'd
  // like to heap allocate and do some other initialization on keys only
  // if  they aren't  in  the hash  table.   It would  be  great if  the
  // "insert"  method took a  "creator" class  so that  I could  do that
  // between  when it  notices that  the key  is not  there and  when it
  // inserts it.  Alternatively, it would be great if I could insert the
  // temporary key and replace it  if it actually got inserted.  But STL
  // hash_set  doesn't have  the creator  feature  and paternalistically
  // declares that keys are immutable, even though (it seems to me) that
  // they  could be  mutated if  the hash  value and  eq values  did not
  // change.

  ASTInterior *BeevMgr::LookupOrCreateInterior(ASTInterior *n_ptr)
  {
    ASTInteriorSet::iterator it;

    if ((it = _interior_unique_table.find(n_ptr)) == _interior_unique_table.end())
      {
        // Make a new ASTInterior node
        // We want (NOT alpha) always to have alpha.nodenum + 1.
        if (n_ptr->GetKind() == NOT)
          {
            n_ptr->SetNodeNum(n_ptr->GetChildren()[0].GetNodeNum() + 1);
          }
        else
          {
            n_ptr->SetNodeNum(NewNodeNum());
          }
        pair<ASTInteriorSet::const_iterator, bool> p = _interior_unique_table.insert(n_ptr);
        return *(p.first);
      }
    else
      // Delete the temporary node, and return the found node.
      delete n_ptr;
    return *it;
  }

  size_t ASTInterior::ASTInteriorHasher::operator()(const ASTInterior *int_node_ptr) const
  {
    //size_t hashval = 0;
    size_t hashval = ((size_t) int_node_ptr->GetKind());
    const ASTVec &ch = int_node_ptr->GetChildren();
    ASTVec::const_iterator iend = ch.end();
    for (ASTVec::const_iterator i = ch.begin(); i != iend; i++)
      {
        //Using "One at a time hash" by Bob Jenkins
        hashval += i->Hash();
        hashval += (hashval << 10);
        hashval ^= (hashval >> 6);
      }

    hashval += (hashval << 3);
    hashval ^= (hashval >> 11);
    hashval += (hashval << 15);
    return hashval;
    //return hashval += ((size_t) int_node_ptr->GetKind());
  }

  void ASTInterior::CleanUp()
  {
    // cout << "Deleting node " << this->GetNodeNum() << endl;
    _bm._interior_unique_table.erase(this);
    delete this;
  }

  ////////////////////////////////////////////////////////////////
  //  ASTNode members
  ////////////////////////////////////////////////////////////////
  //ASTNode constructors are inlined in AST.h
  bool ASTNode::IsAlreadyPrinted() const
  {
    BeevMgr &bm = GetBeevMgr();
    return (bm.AlreadyPrintedSet.find(*this) != bm.AlreadyPrintedSet.end());
  }

  void ASTNode::nodeprint(ostream& os, bool c_friendly) const
  {
    _int_node_ptr->nodeprint(os, c_friendly);
  }

  void ASTNode::MarkAlreadyPrinted() const
  {
    // FIXME: Fetching BeevMgr is annoying.  Can we put this in lispprinter class?
    BeevMgr &bm = GetBeevMgr();
    bm.AlreadyPrintedSet.insert(*this);
  }

  // Get the name from a symbol (char *).  It's an error if kind != SYMBOL
  const char * const ASTNode::GetName() const
  {
    if (GetKind() != SYMBOL)
      FatalError("GetName: Called GetName on a non-symbol: ", *this);
    return ((ASTSymbol *) _int_node_ptr)->GetName();
  }

  void ASTNode::NFASTPrint(int l, int max, int prefix) const
  {
    //****************************************
    // stop
    //****************************************
    if (l > max)
      {
        return;
      }

    //****************************************
    // print
    //****************************************
    printf("[%10d]", 0);
    for (int i = 0; i < prefix; i++)
      {
        printf("    ");
      }
    cout << GetKind();
    printf("\n");

    //****************************************
    // recurse
    //****************************************

    const ASTVec &children = GetChildren();
    ASTVec::const_iterator it = children.begin();
    for (; it != children.end(); it++)
      {
        it->NFASTPrint(l + 1, max, prefix + 1);
      }
  }



  //traverse "*this", and construct "let variables" for terms that
  //occur more than once in "*this".
  void ASTNode::LetizeNode(void) const
  {
    Kind kind = this->GetKind();

    if (kind == SYMBOL || kind == BVCONST || kind == FALSE || kind == TRUE)
      return;

    //FIXME: this is ugly.
    BeevMgr& bm = GetBeevMgr();
    const ASTVec &c = this->GetChildren();
    for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
      {
        ASTNode ccc = *it;
        if (bm.PLPrintNodeSet.find(ccc) == bm.PLPrintNodeSet.end())
          {
            //If branch: if *it is not in NodeSet then,
            //
            //1. add it to NodeSet
            //
            //2. Letize its childNodes

            //FIXME: Fetching BeevMgr is annoying.  Can we put this in
            //some kind of a printer class
            bm.PLPrintNodeSet.insert(ccc);
            //debugging
            //cerr << ccc;
            ccc.LetizeNode();
          }
        else
          {
            Kind k = ccc.GetKind();
            if (k == SYMBOL || k == BVCONST || k == FALSE || k == TRUE)
              continue;

            //0. Else branch: Node has been seen before
            //
            //1. Check if the node has a corresponding letvar in the
            //1. NodeLetVarMap.
            //
            //2. if no, then create a new var and add it to the
            //2. NodeLetVarMap
            if (bm.NodeLetVarMap.find(ccc) == bm.NodeLetVarMap.end())
              {
                //Create a new symbol. Get some name. if it conflicts with a
                //declared name, too bad.
                int sz = bm.NodeLetVarMap.size();
                ostringstream oss;
                oss << "let_k_" << sz;

                ASTNode CurrentSymbol = bm.CreateSymbol(oss.str().c_str());
                CurrentSymbol.SetValueWidth(this->GetValueWidth());
                CurrentSymbol.SetIndexWidth(this->GetIndexWidth());
                /* If for some reason the variable being created here is
                 * already declared by the user then the printed output will
                 * not be a legal input to the system. too bad. I refuse to
                 * check for this.  [Vijay is the author of this comment.]
                 */

                bm.NodeLetVarMap[ccc] = CurrentSymbol;
                std::pair<ASTNode, ASTNode> node_letvar_pair(CurrentSymbol, ccc);
                bm.NodeLetVarVec.push_back(node_letvar_pair);
              }
          }
      }
  } //end of LetizeNode()



  ////////////////////////////////////////////////////////////////
  //  BeevMgr members
  ////////////////////////////////////////////////////////////////
  ASTNode BeevMgr::CreateNode(Kind kind, const ASTVec & back_children)
  {
    // create a new node.  Children will be modified.
    ASTInterior *n_ptr = new ASTInterior(kind, *this);

    // insert all of children at end of new_children.
    ASTNode n(CreateInteriorNode(kind, n_ptr, back_children));
    return n;
  }

  ASTNode BeevMgr::CreateNode(Kind kind, const ASTNode& child0, const ASTVec & back_children)
  {

    ASTInterior *n_ptr = new ASTInterior(kind, *this);
    ASTVec &front_children = n_ptr->_children;
    front_children.push_back(child0);
    ASTNode n(CreateInteriorNode(kind, n_ptr, back_children));
    return n;
  }

  ASTNode BeevMgr::CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1, const ASTVec & back_children)
  {

    ASTInterior *n_ptr = new ASTInterior(kind, *this);
    ASTVec &front_children = n_ptr->_children;
    front_children.push_back(child0);
    front_children.push_back(child1);
    ASTNode n(CreateInteriorNode(kind, n_ptr, back_children));
    return n;
  }

  ASTNode BeevMgr::CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1, const ASTNode& child2, const ASTVec & back_children)
  {
    ASTInterior *n_ptr = new ASTInterior(kind, *this);
    ASTVec &front_children = n_ptr->_children;
    front_children.push_back(child0);
    front_children.push_back(child1);
    front_children.push_back(child2);
    ASTNode n(CreateInteriorNode(kind, n_ptr, back_children));
    return n;
  }

  ASTInterior *BeevMgr::CreateInteriorNode(Kind kind,
                                           // children array of this node will be modified.
                                           ASTInterior *n_ptr,
                                           const ASTVec & back_children)
  {

    // insert back_children at end of front_children
    ASTVec &front_children = n_ptr->_children;

    front_children.insert(front_children.end(), back_children.begin(), back_children.end());

    // check for undefined nodes.
    ASTVec::const_iterator it_end = front_children.end();
    for (ASTVec::const_iterator it = front_children.begin(); it != it_end; it++)
      {
        if (it->IsNull())
          FatalError("CreateInteriorNode: Undefined childnode in CreateInteriorNode: ", ASTUndefined);
      }

    return LookupOrCreateInterior(n_ptr);
  }

  /** Trivial but virtual destructor */
  ASTSymbol::~ASTSymbol()
  {
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
  // BeevMgr member functions to create ASTSymbol and ASTBVConst
  ////////////////////////////////////////////////////////////////
  ASTNode BeevMgr::CreateSymbol(const char * const name)
  {
    ASTSymbol temp_sym(name, *this);
    ASTNode n(LookupOrCreateSymbol(temp_sym));
    return n;
  }

  //Create a ASTBVConst node
  ASTNode BeevMgr::CreateBVConst(unsigned int width, unsigned long long int bvconst)
  {
    if (width > (sizeof(unsigned long long int) << 3) || width <= 0)
      FatalError("CreateBVConst: trying to create a bvconst of width: ", ASTUndefined, width);

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

  ASTNode BeevMgr::CreateBVConst(string*& strval, int base, int bit_width)
  {

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
  ASTNode BeevMgr::CreateBVConst(const char* const strval, int base)
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
  ASTNode BeevMgr::CreateBVConst(CBV bv, unsigned width)
  {
    ASTBVConst temp_bvconst(bv, width, *this);
    ASTNode n(LookupOrCreateBVConst(temp_bvconst));

    CONSTANTBV::BitVector_Destroy(bv);

    return n;
  }

  ASTNode BeevMgr::CreateZeroConst(unsigned width)
  {
    CBV z = CONSTANTBV::BitVector_Create(width, true);
    return CreateBVConst(z, width);
  }

  ASTNode BeevMgr::CreateOneConst(unsigned width)
  {
    CBV o = CONSTANTBV::BitVector_Create(width, true);
    CONSTANTBV::BitVector_increment(o);

    return CreateBVConst(o, width);
  }

  ASTNode BeevMgr::CreateTwoConst(unsigned width)
  {
    CBV two = CONSTANTBV::BitVector_Create(width, true);
    CONSTANTBV::BitVector_increment(two);
    CONSTANTBV::BitVector_increment(two);

    return CreateBVConst(two, width);
  }

  ASTNode BeevMgr::CreateMaxConst(unsigned width)
  {
    CBV max = CONSTANTBV::BitVector_Create(width, false);
    CONSTANTBV::BitVector_Fill(max);

    return CreateBVConst(max, width);
  }

  //To ensure unique BVConst nodes, lookup the node in unique-table
  //before creating a new one.
  ASTBVConst *BeevMgr::LookupOrCreateBVConst(ASTBVConst &s)
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

  // Inline because we need to wait until unique_table is defined
  void ASTBVConst::CleanUp()
  {
    //  cout << "Deleting node " << this->GetNodeNum() << endl;
    _bm._bvconst_unique_table.erase(this);
    delete this;
  }

  // Get the value of bvconst from a bvconst.  It's an error if kind != BVCONST
  CBV const ASTNode::GetBVConst() const
  {
    if (GetKind() != BVCONST)
      FatalError("GetBVConst: non bitvector-constant: ", *this);
    return ((ASTBVConst *) _int_node_ptr)->GetBVConst();
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

  ASTSymbol *BeevMgr::LookupOrCreateSymbol(ASTSymbol& s)
  {
    ASTSymbol *s_ptr = &s; // it's a temporary key.

    // Do an explicit lookup to see if we need to create a copy of the string.
    ASTSymbolSet::const_iterator it;
    if ((it = _symbol_unique_table.find(s_ptr)) == _symbol_unique_table.end())
      {
        // Make a new ASTSymbol with duplicated string (can't assign
        // _name because it's const).  Can cast the iterator to
        // non-const -- carefully.
        //std::string strname(s_ptr->GetName());
        ASTSymbol * s_ptr1 = new ASTSymbol(strdup(s_ptr->GetName()), *this);
        s_ptr1->SetNodeNum(NewNodeNum());
        s_ptr1->_value_width = s_ptr->_value_width;
        pair<ASTSymbolSet::const_iterator, bool> p = _symbol_unique_table.insert(s_ptr1);
        return *p.first;
      }
    else
      // return symbol found in table.
      return *it;
  }

  bool BeevMgr::LookupSymbol(ASTSymbol& s)
  {
    ASTSymbol* s_ptr = &s; // it's a temporary key.

    if (_symbol_unique_table.find(s_ptr) == _symbol_unique_table.end())
      return false;
    else
      return true;
  }

  // Inline because we need to wait until unique_table is defined
  void ASTSymbol::CleanUp()
  {
    //  cout << "Deleting node " << this->GetNodeNum() << endl;
    _bm._symbol_unique_table.erase(this);
    //FIXME This is a HUGE free to invoke.
    //TEST IT!
    free((char*) this->_name);
    delete this;
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

  // Copy constructor.  Maintain _ref_count
  ASTNode::ASTNode(const ASTNode &n) :
    _int_node_ptr(n._int_node_ptr)
  {
    if (n._int_node_ptr)
      {
        n._int_node_ptr->IncRef();
      }
  }

  // If there is a lot of sharing in the graph, this will take a long
  // time.  it doesn't mark subgraphs as already having been
  // typechecked.
  bool BeevMgr::BVTypeCheckRecursive(const ASTNode& n)
  {
    const ASTVec& c = n.GetChildren();

    BVTypeCheck(n);

    for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
      BVTypeCheckRecursive(*it);

    return true;
  }



  /* FUNCTION: Typechecker for terms and formulas
   *
   * TypeChecker: Assumes that the immediate Children of the input
   * ASTNode have been typechecked. This function is suitable in
   * scenarios like where you are building the ASTNode Tree, and you
   * typecheck as you go along. It is not suitable as a general
   * typechecker.
   *
   * If this returns, this ALWAYS returns true. If there is an error it
   * will call FatalError() and abort.
   */


  bool BeevMgr::BVTypeCheck(const ASTNode& n)
  {
    Kind k = n.GetKind();
    //The children of bitvector terms are in turn bitvectors.
    const ASTVec& v = n.GetChildren();
    if (is_Term_kind(k))
      {
        switch (k)
          {
          case BVCONST:
            if (BITVECTOR_TYPE != n.GetType())
              FatalError("BVTypeCheck: The term t does not typecheck, where t = \n", n);
            break;
          case SYMBOL:
            return true;
          case ITE:
            if (BOOLEAN_TYPE != n[0].GetType() || (n[1].GetType() != n[2].GetType()))
              FatalError("BVTypeCheck: The term t does not typecheck, where t = \n", n);
            if (n[1].GetValueWidth() != n[2].GetValueWidth())
              FatalError("BVTypeCheck: length of THENbranch != length of ELSEbranch in the term t = \n", n);
            if (n[1].GetIndexWidth() != n[2].GetIndexWidth())
              FatalError("BVTypeCheck: length of THENbranch != length of ELSEbranch in the term t = \n", n);
            break;
          case READ:
            if (n.GetChildren().size() !=2)
              FatalError("2 params to read.");
            if (n[0].GetIndexWidth() != n[1].GetValueWidth())
              {
                cerr << "Length of indexwidth of array: " << n[0] << " is : " << n[0].GetIndexWidth() << endl;
                cerr << "Length of the actual index is: " << n[1] << " is : " << n[1].GetValueWidth() << endl;
                FatalError("BVTypeCheck: length of indexwidth of array != length of actual index in the term t = \n", n);
              }
            if (ARRAY_TYPE != n[0].GetType())
              FatalError("First parameter to read should be an array", n[0]);
            if (BITVECTOR_TYPE != n[1].GetType())
              FatalError("Second parameter to read should be a bitvector", n[1]);
            break;
          case WRITE:
            if (n.GetChildren().size() !=3)
              FatalError("3 params to write.");
            if (n[0].GetIndexWidth() != n[1].GetValueWidth())
              FatalError("BVTypeCheck: length of indexwidth of array != length of actual index in the term t = \n", n);
            if (n[0].GetValueWidth() != n[2].GetValueWidth())
              FatalError("BVTypeCheck: valuewidth of array != length of actual value in the term t = \n", n);
            if (ARRAY_TYPE != n[0].GetType())
              FatalError("First parameter to read should be an array", n[0]);
            if (BITVECTOR_TYPE != n[1].GetType())
              FatalError("Second parameter to read should be a bitvector", n[1]);
            if (BITVECTOR_TYPE != n[2].GetType())
              FatalError("Third parameter to read should be a bitvector", n[2]);

            break;
          case BVOR:
          case BVAND:
          case BVXOR:
          case BVNOR:
          case BVNAND:
          case BVXNOR:
          case BVPLUS:
          case BVMULT:
          case BVDIV:
          case BVMOD:
          case BVSUB:
            {
              if (!(v.size() >= 2))
                FatalError("BVTypeCheck:bitwise Booleans and BV arith operators must have atleast two arguments\n", n);
              unsigned int width = n.GetValueWidth();
              for (ASTVec::const_iterator it = v.begin(), itend = v.end(); it != itend; it++)
                {
                  if (width != it->GetValueWidth())
                    {
                      cerr << "BVTypeCheck:Operands of bitwise-Booleans and BV arith operators must be of equal length\n";
                      cerr << n << endl;
                      cerr << "width of term:" << width << endl;
                      cerr << "width of offending operand:" << it->GetValueWidth() << endl;
                      FatalError("BVTypeCheck:Offending operand:\n", *it);
                    }
                  if (BITVECTOR_TYPE != it->GetType())
                    FatalError("BVTypeCheck: ChildNodes of bitvector-terms must be bitvectors\n", n);
                }
              break;
            }
          case BVSX:
            //in BVSX(n[0],len), the length of the BVSX term must be
            //greater than the length of n[0]
            if (n[0].GetValueWidth() > n.GetValueWidth())
              {
                FatalError("BVTypeCheck: BVSX(t,bvsx_len) : length of 't' must be <= bvsx_len\n", n);
              }
            if ((v.size() != 2))
              FatalError("BVTypeCheck:BVSX must have two arguments. The second is the new width\n", n);
            break;

          case BVZX:
            //in BVZX(n[0],len), the length of the BVZX term must be
            //greater than the length of n[0]
            if (n[0].GetValueWidth() > n.GetValueWidth())
              {
                FatalError("BVTypeCheck: BVZX(t,bvzx_len) : length of 't' must be <= bvzx_len\n", n);
              }
            if ((v.size() != 2))
              FatalError("BVTypeCheck:BVZX must have two arguments. The second is the new width\n", n);

            break;

          default:
            for (ASTVec::const_iterator it = v.begin(), itend = v.end(); it != itend; it++)
              if (BITVECTOR_TYPE != it->GetType())
                {
                  cerr << "The type is: " << it->GetType() << endl;
                  FatalError("BVTypeCheck:ChildNodes of bitvector-terms must be bitvectors\n", n);
                }
            break;
          }

        switch (k)
          {
          case BVCONCAT:
            if (n.Degree() != 2)
              FatalError("BVTypeCheck: should have exactly 2 args\n", n);
            if (n.GetValueWidth() != n[0].GetValueWidth() + n[1].GetValueWidth())
              FatalError("BVTypeCheck:BVCONCAT: lengths do not add up\n", n);
            break;
          case BVUMINUS:
          case BVNEG:
            if (n.Degree() != 1)
              FatalError("BVTypeCheck: should have exactly 1 args\n", n);
            break;
          case BVEXTRACT:
            if (n.Degree() != 3)
              FatalError("BVTypeCheck: should have exactly 3 args\n", n);
            if (!(BVCONST == n[1].GetKind() && BVCONST == n[2].GetKind()))
              FatalError("BVTypeCheck: indices should be BVCONST\n", n);
            if (n.GetValueWidth() != GetUnsignedConst(n[1]) - GetUnsignedConst(n[2]) + 1)
              FatalError("BVTypeCheck: length mismatch\n", n);
            break;
          case BVLEFTSHIFT:
          case BVRIGHTSHIFT:
            if (n.Degree() != 2)
              FatalError("BVTypeCheck: should have exactly 2 args\n", n);
            break;
            //case BVVARSHIFT:
            //case BVSRSHIFT:
            break;
          default:
            break;
          }
      }
    else
      {
        if (!(is_Form_kind(k) && BOOLEAN_TYPE == n.GetType()))
          FatalError("BVTypeCheck: not a formula:", n);
        switch (k)
          {
          case TRUE:
          case FALSE:
          case SYMBOL:
            return true;
          case EQ:
          case NEQ:
            if (!(n[0].GetValueWidth() == n[1].GetValueWidth() && n[0].GetIndexWidth() == n[1].GetIndexWidth()))
              {
                cerr << "valuewidth of lhs of EQ: " << n[0].GetValueWidth() << endl;
                cerr << "valuewidth of rhs of EQ: " << n[1].GetValueWidth() << endl;
                cerr << "indexwidth of lhs of EQ: " << n[0].GetIndexWidth() << endl;
                cerr << "indexwidth of rhs of EQ: " << n[1].GetIndexWidth() << endl;
                FatalError("BVTypeCheck: terms in atomic formulas must be of equal length", n);
              }
            break;
          case BVLT:
          case BVLE:
          case BVGT:
          case BVGE:
          case BVSLT:
          case BVSLE:
          case BVSGT:
          case BVSGE:
            if (BITVECTOR_TYPE != n[0].GetType() && BITVECTOR_TYPE != n[1].GetType())
              FatalError("BVTypeCheck: terms in atomic formulas must be bitvectors", n);
            if (n[0].GetValueWidth() != n[1].GetValueWidth())
              FatalError("BVTypeCheck: terms in atomic formulas must be of equal length", n);
            if (n[0].GetIndexWidth() != n[1].GetIndexWidth())
              FatalError("BVTypeCheck: terms in atomic formulas must be of equal length", n);
            break;
          case NOT:
            if (1 != n.Degree())
              FatalError("BVTypeCheck: NOT formula can have exactly one childNode", n);
            break;
          case AND:
          case OR:
          case XOR:
          case NAND:
          case NOR:
            if (2 > n.Degree())
              FatalError("BVTypeCheck: AND/OR/XOR/NAND/NOR: must have atleast 2 ChildNodes", n);
            break;
          case IFF:
          case IMPLIES:
            if (2 != n.Degree())
              FatalError("BVTypeCheck:IFF/IMPLIES must have exactly 2 ChildNodes", n);
            break;
          case ITE:
            if (3 != n.Degree())
              FatalError("BVTypeCheck:ITE must have exactly 3 ChildNodes", n);
            break;
          case FOR:
            //FIXME: Todo
            break;
          default:
            FatalError("BVTypeCheck: Unrecognized kind: ", ASTUndefined);
            break;
          }
      }
    return true;
  } //End of TypeCheck function

  //add an assertion to the current logical context
  void BeevMgr::AddAssert(const ASTNode& assert)
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

  void BeevMgr::Push(void)
  {
    ASTVec * v;
    v = new ASTVec();
    _asserts.push_back(v);
  }

  void BeevMgr::Pop(void)
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

  void BeevMgr::AddQuery(const ASTNode& q)
  {
    //_current_query = TransformFormula(q);
    //cerr << "\nThe current query is: " << q << endl;
    _current_query = q;
  }

  const ASTNode BeevMgr::PopQuery()
  {
    ASTNode q = _current_query;
    _current_query = ASTTrue;
    return q;
  }

  const ASTNode BeevMgr::GetQuery()
  {
    return _current_query;
  }

  const ASTVec BeevMgr::GetAsserts(void)
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

  //Create a new variable of ValueWidth 'n'
  ASTNode BeevMgr::NewArrayVar(unsigned int index, unsigned int value)
  {
    std::string c("v");
    char d[32];
    sprintf(d, "%d", _symbol_count++);
    std::string ccc(d);
    c += "_writearray_" + ccc;

    ASTNode CurrentSymbol = CreateSymbol(c.c_str());
    CurrentSymbol.SetValueWidth(value);
    CurrentSymbol.SetIndexWidth(index);
    return CurrentSymbol;
  } //end of NewArrayVar()


  //Create a new variable of ValueWidth 'n'
  ASTNode BeevMgr::NewVar(unsigned int value)
  {
    std::string c("v");
    char d[32];
    sprintf(d, "%d", _symbol_count++);
    std::string ccc(d);
    c += "_new_stp_var_" + ccc;

    ASTNode CurrentSymbol = CreateSymbol(c.c_str());
    CurrentSymbol.SetValueWidth(value);
    CurrentSymbol.SetIndexWidth(0);
    _introduced_symbols.insert(CurrentSymbol);
    return CurrentSymbol;
  } //end of NewVar()

  //prints statistics for the ASTNode
  void BeevMgr::ASTNodeStats(const char * c, const ASTNode& a)
  {
    if (!stats_flag)
      return;

    StatInfoSet.clear();
    //print node size:
    cout << endl << "Printing: " << c;
    if (print_nodes_flag)
      {
        //a.PL_Print(cout,0);
        //cout << endl;
        cout << a << endl;
      }
    cout << "Node size is: ";
    cout << NodeSize(a) << endl << endl;
  }

  unsigned int BeevMgr::NodeSize(const ASTNode& a, bool clearStatInfo)
  {
    if (clearStatInfo)
      StatInfoSet.clear();

    ASTNodeSet::iterator it;
    if ((it = StatInfoSet.find(a)) != StatInfoSet.end())
      //has already been counted
      return 0;

    //record that you have seen this node already
    StatInfoSet.insert(a);

    //leaf node has a size of 1
    if (a.Degree() == 0)
      return 1;

    unsigned newn = 1;
    ASTVec c = a.GetChildren();
    for (ASTVec::iterator it = c.begin(), itend = c.end(); it != itend; it++)
      newn += NodeSize(*it);
    return newn;
  }

  void BeevMgr::ClearAllTables(void)
  {
    //clear all tables before calling toplevelsat
    _ASTNode_to_SATVar.clear();
    _SATVar_to_AST.clear();

    for (ASTtoBitvectorMap::iterator it = _ASTNode_to_Bitvector.begin(), itend = _ASTNode_to_Bitvector.end(); it != itend; it++)
      {
        (it->second)->clear();
        delete (it->second);
      }
    _ASTNode_to_Bitvector.clear();

    /* OLD Destructor
     * for(ASTNodeToVecMap::iterator ivec = BBTermMemo.begin(),
     ivec_end=BBTermMemo.end();ivec!=ivec_end;ivec++) {
     ivec->second.clear();
     }*/

    /*What should I do here? For ASTNodes?
     * for(ASTNodeMap::iterator ivec = BBTermMemo.begin(),
     ivec_end=BBTermMemo.end();ivec!=ivec_end;ivec++) {
     ivec->second.clear();
     }*/
    BBTermMemo.clear();
    BBFormMemo.clear();
    NodeLetVarMap.clear();
    NodeLetVarMap1.clear();
    PLPrintNodeSet.clear();
    AlreadyPrintedSet.clear();
    SimplifyMap->clear();
    SimplifyNegMap->clear();
    ReferenceCount->clear();
    SolverMap.clear();
    AlwaysTrueFormMap.clear();
    _arrayread_ite.clear();
    _arrayread_symbol.clear();
    _introduced_symbols.clear();
    //TransformMap.clear();
    _letid_expr_map->clear();
    CounterExampleMap.clear();
    ComputeFormulaMap.clear();
    StatInfoSet.clear();

    // for(std::vector<ASTVec *>::iterator it=_asserts.begin(),
    //    itend=_asserts.end();it!=itend;it++) {
    //       (*it)->clear();
    //     }
    _asserts.clear();
    for (ASTNodeToVecMap::iterator iset = _arrayname_readindices.begin(), iset_end = _arrayname_readindices.end(); iset != iset_end; iset++)
      {
        iset->second.clear();
      }

    _arrayname_readindices.clear();
    _interior_unique_table.clear();
    _symbol_unique_table.clear();
    _bvconst_unique_table.clear();
  }

  void BeevMgr::ClearAllCaches(void)
  {
    //clear all tables before calling toplevelsat
    _ASTNode_to_SATVar.clear();
    _SATVar_to_AST.clear();

    for (ASTtoBitvectorMap::iterator it = _ASTNode_to_Bitvector.begin(), itend = _ASTNode_to_Bitvector.end(); it != itend; it++)
      {
        (it->second)->clear();
        delete (it->second);
      }
    _ASTNode_to_Bitvector.clear();

    /*OLD destructor
     * for(ASTNodeToVecMap::iterator ivec = BBTermMemo.begin(),
     ivec_end=BBTermMemo.end();ivec!=ivec_end;ivec++) {
     ivec->second.clear();
     }*/

    /*What should I do here?
     *for(ASTNodeMap::iterator ivec = BBTermMemo.begin(),
     ivec_end=BBTermMemo.end();ivec!=ivec_end;ivec++) {
     ivec->second.clear();
     }*/
    BBTermMemo.clear();
    BBFormMemo.clear();
    NodeLetVarMap.clear();
    NodeLetVarMap1.clear();
    PLPrintNodeSet.clear();
    AlreadyPrintedSet.clear();
    SimplifyMap->clear();
    SimplifyNegMap->clear();
    ReferenceCount->clear();
    SolverMap.clear();
    AlwaysTrueFormMap.clear();
    _arrayread_ite.clear();
    _arrayread_symbol.clear();
    _introduced_symbols.clear();
    _letid_expr_map->clear();
    CounterExampleMap.clear();
    ComputeFormulaMap.clear();
    StatInfoSet.clear();

    for (ASTNodeToVecMap::iterator iset = _arrayname_readindices.begin(), iset_end = _arrayname_readindices.end(); iset != iset_end; iset++)
      {
        iset->second.clear();
      }

    _arrayname_readindices.clear();
    //_interior_unique_table.clear();
    //_symbol_unique_table.clear();
    //_bvconst_unique_table.clear();
  }

  void BeevMgr::CopySolverMap_To_CounterExample(void)
  {
    if (!SolverMap.empty())
      {
        CounterExampleMap.insert(SolverMap.begin(), SolverMap.end());
      }
  }

  void FatalError(const char * str, const ASTNode& a, int w)
  {
    if (a.GetKind() != UNDEFINED)
      {
        cerr << "Fatal Error: " << str << endl << a << endl;
        cerr << w << endl;
      }
    else
      {
        cerr << "Fatal Error: " << str << endl;
        cerr << w << endl;
      }
    if (vc_error_hdlr)
      vc_error_hdlr(str);
    exit(-1);
    //assert(0);
  }

  void FatalError(const char * str)
  {
    cerr << "Fatal Error: " << str << endl;
    if (vc_error_hdlr)
      vc_error_hdlr(str);
    exit(-1);
    //assert(0);
  }

  //Variable Order Printer: A global function which converts a MINISAT
  //var into a ASTNODE var. It then prints this var along with
  //variable order dcisions taken by MINISAT.
  void Convert_MINISATVar_To_ASTNode_Print(int minisat_var, int decision_level, int polarity)
  {
    BEEV::ASTNode vv = globalBeevMgr_for_parser->_SATVar_to_AST[minisat_var];
    cout << spaces(decision_level);
    if (polarity)
      {
        cout << "!";
      }
    printer::PL_Print(cout,vv, 0);
    cout << endl;
  }

  void SortByExprNum(ASTVec& v)
  {
    sort(v.begin(), v.end(), exprless);
  }

  void SortByArith(ASTVec& v)
  {
    sort(v.begin(), v.end(), arithless);
  }

  bool isAtomic(Kind kind)
  {
    if (TRUE == kind || FALSE == kind || EQ == kind || NEQ == kind || BVLT == kind || BVLE == kind || BVGT == kind || BVGE == kind || BVSLT == kind
        || BVSLE == kind || BVSGT == kind || BVSGE == kind || SYMBOL == kind || BVGETBIT == kind)
      return true;
    return false;
  }

  BeevMgr::~BeevMgr()
  {
    ClearAllTables();

    delete SimplifyMap;
    delete SimplifyNegMap;
    delete _letid_expr_map;
    delete ReferenceCount;
  }

}
; // end namespace

