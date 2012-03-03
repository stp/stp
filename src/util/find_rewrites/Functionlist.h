/*
 * Functionlist.h
 *
 */

#ifndef FUNCTIONLIST_H_
#define FUNCTIONLIST_H_

extern const int bits;
extern Simplifier *simp;
extern Rewrite_system to_write;

ASTNode
widen(const ASTNode& w, int width);

ASTNode
create(Kind k, const ASTNode& n0, const ASTNode& n1);


class Function_list
{

  // Because v and w might come from "result", if "result" is resized, they will
  // be moved. So we can't use references to them.
  void
  getAllFunctions(const ASTNode v, const ASTNode w, ASTVec& result)
  {

    Kind types[] = {BVMULT, BVPLUS, BVXOR, BVAND};


    //Kind types[] = {BVMULT, BVDIV, SBVDIV, SBVREM, SBVMOD, BVPLUS, BVMOD, BVRIGHTSHIFT, BVLEFTSHIFT, BVOR, BVAND, BVXOR, BVSRSHIFT};
    const int number_types = sizeof(types) / sizeof(Kind);

    // all two argument functions.
    for (int i = 0; i < number_types; i++)
      result.push_back(create(types[i], v, w));
  }


  ASTNode
  rewriteThroughWithAIGS(const ASTNode &n_)
  {
    assert(n_.GetType() == BITVECTOR_TYPE);
    ASTNode f = mgr->LookupOrCreateSymbol("rewriteThroughWithAIGS");
    f.SetValueWidth(n_.GetValueWidth());
    ASTNode n = create(EQ, n_, f);

    BBNodeManagerAIG nm;
    BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&nm, simp, mgr->defaultNodeFactory, &mgr->UserFlags);
    ASTNodeMap fromTo;
    ASTNodeMap equivs;
    bb.getConsts(n, fromTo, equivs);

    ASTNode result = n_;
    if (equivs.size() > 0)
      {
        ASTNodeMap cache;
        result = SubstitutionMap::replace(result, equivs, cache, nf, false, true);
      }

    if (fromTo.size() > 0)
      {
        ASTNodeMap cache;
        result = SubstitutionMap::replace(result, fromTo, cache, nf);
      }
    return result;
  }

  void
  applyBigRewrite()
  {
    BEEV::BigRewriter b;

    for (int i = 0; i < functions.size(); i++)
      {
        if (functions[i] == mgr->ASTUndefined)
          continue;

        if (i % 100000 == 0)
          cerr << "BigRewrite:" << i << " of " << functions.size();

        ASTNodeMap fromTo;
        ASTNode s = b.rewrite(functions[i], fromTo, nf, mgr);
        if (s != functions[i])
          {
            functions[i] = s;
          }
      }
  }

  void
  applyRewritesToAll(ASTVec& functions)
  {
    to_write.buildLookupTable();
    cerr << "Applying:" << to_write.size()  <<"rewrite rules" << endl;

    for (int i = 0; i < functions.size(); i++)
      {
        if (functions[i] == mgr->ASTUndefined)
          continue;

        if (i % 100000 == 0)
          cerr << "applyRewritesToAll:" << i << " of " << functions.size() << endl;

        ASTNode r = to_write.rewriteNode(functions[i]);
        if (r!= functions[i])
          {
         //   cerr << "changed" << functions[i] << " to "<< r;

            functions[i] =r;
          }
      }
  }


  // If there only w variables in the problem. We can delete it because
  // we will have another with just v's.
  // NB: Can only apply at the top level.
  void
  removeSingleVariable()
  {
    for (int i = 0; i < functions.size(); i++)
      {
        vector<ASTNode> symbols = getVariables(functions[i]);

        if (i % 100000 == 0)
          cout << "removeSingleVariable:" << i << " of " << functions.size() << "\n";

        if (symbols.size() == 1 && symbols[0] == w)
          {
            functions[i] = mgr->ASTUndefined; // We can't widen it later. So remove it.
            continue;
          }
      }
  }

  void
  removeSingleUndefined()
  {
    for (int i = 0; i < functions.size(); i++)
      {
        if (functions[i] == mgr->ASTUndefined)
          {
            functions.erase(functions.begin() + i);
            break;
          }
      }
  }

  void
  applySpeculative()
  {
    for (int i = 0; i < functions.size(); i++)
      {
        if (functions[i] == mgr->ASTUndefined)
          continue;

        if (i % 100000 == 0)
          cerr << "applySpeculative:" << i << " of " << functions.size() << "\n";

        functions[i] = simp->SimplifyTerm_TopLevel(functions[i]);
      }
  }

  void
  checkFunctions()
  {
    for (int i = 0; i < functions.size(); i++)
      {
        assert(functions[i].GetType() == BITVECTOR_TYPE);
        assert(functions[i].GetValueWidth() == bits);
        assert(BVTypeCheckRecursive(functions[i]));
      }
  }

  void
  removeNonWidened()
  {
    for (int i = 0; i < functions.size(); i++)
      {
        if (mgr->ASTUndefined == functions[i])
          continue;

        if (i % 100000 == 0)
          cerr << "Widen check:" << i << " of " << functions.size() << endl;

        if (mgr->ASTUndefined == widen(functions[i], bits + 1))
          {
            cerr << "Can't widen" << functions[i];
            functions[i] = mgr->ASTUndefined; // We can't widen it later. So remove it.
            continue;
          }
      }
  }


  // Triples the number of functions by adding all the unary ones.
  void
  allUnary()
  {
    for (int i = 0, size = functions.size(); i < size; i++)
      {
        if (functions[i] == mgr->ASTUndefined)
          continue;

        functions.push_back(nf->CreateTerm(BEEV::BVNEG, bits, functions[i]));
        functions.push_back(nf->CreateTerm(BEEV::BVUMINUS, bits, functions[i]));
      }
  }


  void
  applyAIGs()
  {
    ASTNode f = mgr->LookupOrCreateSymbol("rewriteThroughWithAIGS");
    f.SetValueWidth(bits);

    for (int i = 0; i < functions.size(); i++)
      {
        if (functions[i] == mgr->ASTUndefined)
          continue;

        if (i % 100000 == 0)
          cerr << "ApplyAigs:" << i << " of " << functions.size() << endl;

        rewriteThroughWithAIGS(functions[i]);
      }
  }

public:

  void
  buildAll()
  {
    /////////////////////////// BV, BV -> BV.
    functions.push_back(w);
    functions.push_back(v);

    functions.push_back(mgr->CreateBVConst(bits, 0));
    functions.push_back(mgr->CreateBVConst(bits, 1));
    functions.push_back(mgr->CreateMaxConst(bits));

    // All unary of the leaves.
    allUnary();
    removeDuplicates(functions);
    cerr << "Leaves:" << functions.size() << endl;

    // We've got the leaves, and their unary operations,
    // now get the binary operations of all of those.
    int size = functions.size();
    for (int i = 0; i < size; i++)
      for (int j = 0; j < size; j++)
        getAllFunctions(functions[i], functions[j], functions);

    allUnary();


    applyAIGs();
    applySpeculative();
    applyRewritesToAll(functions);
    checkFunctions();
    removeDuplicates(functions);
    removeSingleUndefined();

    cerr << "One Level:" << functions.size() << endl;

   const bool two_level = true;

    if (two_level)
      {
        int last = 0;
        ASTVec functions_copy(functions);
        size = functions_copy.size();
        for (int i = 0; i < size; i++)
          for (int j = 0; j < size; j++)
            getAllFunctions(functions_copy[i], functions_copy[j], functions);

        cerr << "Removing single variables" <<endl;
        checkFunctions();
        removeNonWidened();

        removeSingleVariable();
        removeDuplicates(functions);
        applySpeculative();

        //applyRewritesToAll(functions);

        applyAIGs();

        removeDuplicates(functions);
        removeSingleUndefined();

        // All the unary combinations of the binaries.
        //allUnary(functions);

        cerr << "Two Level:" << functions.size() << endl;
      }
    else
      {
        removeSingleVariable();
      }
  }

public:
  ASTVec functions;
};

#endif /* FUNCTIONLIST_H_ */
