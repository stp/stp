// -*- c++ -*-
/********************************************************************
 * AUTHORS: Unknown
 *
 * BEGIN DATE: November, 2005
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ********************************************************************/

#ifndef SUBSTITUTIONMAP_H_
#define SUBSTITUTIONMAP_H_

#include "stp/AST/AST.h"
#include "stp/STPManager/STPManager.h"
#include "stp/AST/NodeFactory/SimplifyingNodeFactory.h"
#include "stp/Simplifier/VariablesInExpression.h"
#include <boost/utility.hpp>

namespace BEEV
{

  class Simplifier;
  class ArrayTransformer;

  const bool debug_substn = false;

  class SubstitutionMap : boost::noncopyable
  {

    ASTNodeMap * SolverMap;
    Simplifier *simp;
    STPMgr* bm;
    ASTNode ASTTrue, ASTFalse, ASTUndefined;
    NodeFactory *nf;

    // These are used to avoid substituting {x = f(y,z), z = f(x)}
    typedef hash_map<ASTNode, Symbols*, ASTNode::ASTNodeHasher> DependsType;
    DependsType dependsOn; // The lhs depends on the variables in the rhs.
    ASTNodeSet rhs; // All the rhs that have been seeen.
    std::set<ASTNodeSet*> rhsAlreadyAdded;
    VariablesInExpression::SymbolPtrSet rhs_visited; // the rhs contains all the variables in here already.

    int loopCount;

    void
    buildDepends(const ASTNode& n0, const ASTNode& n1);
    void
    loops_helper(const std::set<ASTNode>& varsToCheck, std::set<ASTNode>& visited);
    bool
    loops(const ASTNode& n0, const ASTNode& n1);

    size_t substitutionsLastApplied;
  public:

    bool
    hasUnappliedSubstitutions()
    {
      return (substitutionsLastApplied != SolverMap->size());
    }

    // When the substitutionMap has been applied globally, then,
    // these are no longer needed.
    void
    haveAppliedSubstitutionMap()
    {
      dependsOn.clear();
      rhs.clear();
      rhs_visited.clear();
      rhsAlreadyAdded.clear();
      substitutionsLastApplied = SolverMap->size();
    }

    VariablesInExpression vars;

    SubstitutionMap(Simplifier *_simp, STPMgr* _bm)
    {
      simp = _simp;
      bm = _bm;

      ASTTrue = bm->CreateNode(TRUE);
      ASTFalse = bm->CreateNode(FALSE);
      ASTUndefined = bm->CreateNode(UNDEFINED);

      SolverMap = new ASTNodeMap(INITIAL_TABLE_SIZE);
      loopCount = 0;
      substitutionsLastApplied = 0;
      nf = bm->defaultNodeFactory;
    }

    void
    clear()
    {
      SolverMap->clear();
      haveAppliedSubstitutionMap();
    }

    virtual
    ~SubstitutionMap();

    //check the solver map for 'key'. If key is present, then return the
    //value by reference in the argument 'output'
    bool
    CheckSubstitutionMap(const ASTNode& key, ASTNode& output)
    {
      ASTNodeMap::iterator it = SolverMap->find(key);
      if (it != SolverMap->end())
        {
        output = it->second;
        return true;
        }
      return false;
    }

    //update solvermap with (key,value) pair
    bool
    UpdateSolverMap(const ASTNode& key, const ASTNode& value)
    {
      ASTNode var = (BVEXTRACT == key.GetKind()) ? key[0] : key;

      if (var.GetKind() == SYMBOL && loops(var, value))
        return false;

      if (!CheckSubstitutionMap(var) && key != value)
        {
        //cerr << "from" << key << "to" <<value;
        buildDepends(key, value);
        (*SolverMap)[key] = value;
        return true;
        }
      return false;
    } //end of UpdateSolverMap()

    ASTNodeMap *
    Return_SolverMap()
    {
      return SolverMap;
    } // End of SolverMap()

    bool
    CheckSubstitutionMap(const ASTNode& key)
    {
      if (SolverMap->find(key) != SolverMap->end())
        return true;
      else
        return false;
    }

    // It's depressingly expensive to perform all of the loop checks etc.
    // If you use this function you are promising:
    // 1) That UpdateSubstitutionMap(e0,e1) would have returned true.
    // 2) That all of the substitutions will be written in fully before other code
    bool
    UpdateSubstitutionMapFewChecks(const ASTNode& e0, const ASTNode& e1)
    {
      assert(e0.GetKind() == SYMBOL);
      assert(!CheckSubstitutionMap(e0));
      (*SolverMap)[e0] = e1;
      return true;
    }

    // The substitutionMap will be updated, given x <-> f(w,z,y), iff,
    // 1) x doesn't appear in the rhs.
    // 2) x hasn't already been stored in the substitution map.
    // 3) none of the variables in the transitive closure of the rhs depend on x.
    bool
    UpdateSubstitutionMap(const ASTNode& e0, const ASTNode& e1);

    ASTNode
    applySubstitutionMap(const ASTNode& n);

    ASTNode
    applySubstitutionMapUntilArrays(const ASTNode& n);

    // Replace any nodes in "n" that exist in the fromTo map.
    // NB the fromTo map is changed.
    static ASTNode
    replace(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& cache, NodeFactory *nf);
    static ASTNode
    replace(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& cache, NodeFactory *nf, bool stopAtArrays,
        bool preventInfiniteLoops);

  };

}

#endif /* SUBSTITUTIONMAP_H_ */
