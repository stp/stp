/********************************************************************
 * AUTHORS: Trevor Hansen
 *
  *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

/*
  Consider (bvuminus(ite, p , 6 ,5 ))
  If there's no other use of the ite anywhere else, it'd be good to push the bvuminus through,
  because it will remove a unary minus from the problem. However, if the ITE is used somewhere else, 
  well it's not necessasrily an improvment.

  This implements sharing aware rewrites. It's different to other simplifiers in STP, which apply
  the rewrites then check later if it's better, and revert if not. This one is like hill climbing.

  Rules that are both sharing-independent and size-neutral belong in the
  SimplifyingNodeFactory instead, where they apply on every node creation.

  Every rule here should leave the node count the same or smaller, using the
  share count to prove that the nodes it replaces really die. The one
  deliberate exception is the comparison-vs-plus splitting rules, which add
  a single node in exchange for eliminating a plus from under a comparison --
  a large win on the difficulty score.
*/



#include "stp/Simplifier/Rewriting.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include "stp/Util/DagWalk.h"
#include <list>
#include <deque>
#include <vector>

namespace stp
{

  ASTNode Rewriting::topLevel(ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::Rewriting);
    
    removed=0;

    buildShareCount(n);
    ASTNode result = rewrite(n);

    if (stpMgr->UserFlags.stats_flag)
    {
      std::cerr << "{Rewriting} Nodes removed:" << removed << std::endl;
    }

    shareCount.clear();
    fromTo.clear();

    stpMgr->GetRunTimes()->stop(RunTimes::Rewriting);
    return result;
  }

  // counter is 1 if the node has one reference in the tree.
  //
  // The walk is iterative because the input decides how deep it goes, and
  // deep inputs exist: a call per level of the DAG exhausts the stack. The
  // continuation stack holds pointers into each node's own child storage,
  // which the node above keeps alive for the whole walk. It stores suspended
  // ancestors, not every sibling in a wide frontier.
  void Rewriting::buildShareCount(const ASTNode& n)
  {
    walkPreOrder(n, [&](const ASTNode& current) {
      if (current.Degree() == 0)
        return false;

      if (shareCount[current.GetNodeNum()]++ > 0) // 0 first time, 1 second.
        return false;
      return true;
    });
  }

  // Every sharing-aware rule, in order, applied to one node. Each rule
  // sees what the rules before it produced. Nothing here descends into
  // the DAG: the caller decides what to do with a node that changed.
  ASTNode Rewriting::applyRules(ASTNode c)
  {

     if (
        c.GetKind() == EQ 
        && c[0].GetKind() == BVCONST 
        && c[1].GetKind() == BVPLUS  
        && c[1][0].GetKind() == BVCONST  
        && c[1].Degree() > 2
        && shareCount[c[1].GetNodeNum()] <= 1
        )
     {
          // combine constants on the lhs. Note because the plus is two arity, we MUST consider sharing now.
          const auto width  =  c[0].GetValueWidth();
          auto lhs = nf->CreateTerm(BVUMINUS, width, c[1][0]);
          lhs = nf->CreateTerm(BVPLUS, width, lhs, c[0]);
          assert(lhs.GetKind() == BVCONST);

          assert (c[1].Degree() > 2);
          ASTVec otherPlusChildren;
          for (unsigned i = 1; i < c[1].Degree(); i++)
            otherPlusChildren.push_back(c[1][i]);
          c = nf->CreateNode(EQ, lhs, nf->CreateTerm(BVPLUS, width, otherPlusChildren));            
        
     }

     if (c.GetKind() == stp::BVEXTRACT 
         && c[0].GetKind() == ITE 
         && c[0][1].GetKind() == BVCONST 
         && c[0][2].GetKind() == BVCONST 
         && shareCount[c[0].GetNodeNum()] <= 1
         )
     {
        // push the extract through.

          const auto width  =  c.GetValueWidth();
          const auto first  =  nf->CreateTerm(BVEXTRACT, width, c[0][1], c[1], c[2]);
          const auto second  =  nf->CreateTerm(BVEXTRACT, width, c[0][2], c[1], c[2]);
          c = nf->CreateTerm(ITE, width, c[0][0], first, second);
     }

      if (c.GetKind() == BVPLUS
        && c.Degree() == 2
        && c[0].GetKind() == BVCONST
        && c[1].GetKind() == ITE
        && c[1][1].GetKind() == BVCONST
        && c[1][2].GetKind() == BVCONST
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
        // Push the addition through the ITE.
       
          const auto width = c.GetValueWidth();
          const auto first = nf->CreateTerm(BVPLUS, width, c[1][1], c[0]  );
          const auto second = nf->CreateTerm(BVPLUS, width, c[1][2], c[0]  );
          c = nf->CreateTerm(ITE, width, c[1][0], first, second);
       }


      if ( (c.GetKind() == BVUMINUS || c.GetKind() == BVNOT )
        && c[0].GetKind() == ITE
        && c[0][1].GetKind() == BVCONST
        && c[0][2].GetKind() == BVCONST
        && shareCount[c[0].GetNodeNum()] <= 1
       )
       {
        // Push the uminus/bvnot through the ITE.
       
          const auto width = c.GetValueWidth();
          const auto first = nf->CreateTerm(c.GetKind(), width, c[0][1] );
          const auto second = nf->CreateTerm(c.GetKind(), width, c[0][2] );

          c = nf->CreateTerm(ITE, width, c[0][0], first, second);
       }

      if (
        c.GetKind() == BVEXTRACT
        && c[0].GetKind() == BVXOR
        && c[0][0].GetKind() == BVCONST
        && shareCount[c[0].GetNodeNum()] <= 1
       )
       {
          // Extracts over BVXOR can be replaced by BVNOT maybe, or removed.
          const auto width = c.GetValueWidth();
          const auto extract = nf->CreateTerm(BVEXTRACT, width, c[0][0], c[1], c[2]);

          if (extract == stpMgr->CreateZeroConst(width) || extract == stpMgr->CreateMaxConst(width))
          {
            ASTNode other;
            if (c[0].Degree() == 2 )
              other = c[0][1];
            else
            {
             ASTVec otherChildren;
             for (unsigned i = 1; i < c[0].Degree(); i++)
                otherChildren.push_back(c[0][i]);

              other = nf->CreateTerm(BVXOR, c[0].GetValueWidth(), otherChildren);
            }

            c = nf->CreateTerm(BVEXTRACT, width , other, c[1],c[2]);
            
            if (extract == stpMgr->CreateMaxConst(width))
            {
                c = nf->CreateTerm(BVNOT, width, c);
            }
          }
       }

      if ( 
        c.GetKind() == BVPLUS
        && c.Degree() == 2
        && c[1].GetKind() == BVUMINUS
        && c[1][0].GetKind() == BVPLUS
        && shareCount[c[1][0].GetNodeNum()] <= 1
       )
       {

        for (size_t matching =0 ; matching < c[1][0].Degree(); matching++)
          if (c[1][0][matching] == c[0])
          {
            ASTVec others;
            for (size_t i =0 ; i < c[1][0].Degree(); i++)
              if (i != matching)
                others.push_back(c[1][0][i]);

            if (others.size() == 1)
              c = nf->CreateTerm(BVUMINUS, c.GetValueWidth(), others[0]);
            else
              c = nf->CreateTerm(BVUMINUS, c.GetValueWidth(), nf->CreateTerm(BVPLUS, c.GetValueWidth() ,  others));
            break;
          }
        }

      /*
         (BVSGT
          7570:0x00000000
          457798:(BVPLUS
            7820:0xFFFFFFD7
            [457708])))

         These three comparison-splitting rules are the pass's one deliberate
         exception to never increasing the node count: they add one node (two
         comparisons and a connective replace one comparison), but eliminate
         a plus from under the comparison, which is a large win on the
         difficulty score (a comparison costs 6*width, a plus 11*width). The
         single-use guard on the plus is what secures that win: if the plus
         survived for another use, the extra comparison would be a pure loss.
      */
      if (
        c.GetKind() == BVSGT
        && c[0].GetKind() == BVCONST
        && c[1].GetKind() == BVPLUS
        && c[1].Degree() ==2
        && c[1][0].GetKind() == BVCONST
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
          const auto width = c[0].GetValueWidth();
          auto lhs = nf->CreateTerm(BVPLUS, width , c[0], nf->CreateTerm(BVUMINUS, width, c[1][0]));
          auto part1 = nf->CreateNode(BVSGT, lhs, c[1][1]);
          
          auto part2 =  nf->CreateTerm(BVPLUS, width , nf->CreateSignedMinConst(width), nf->CreateTerm(BVUMINUS, width, c[1][0]));
          part2 = nf->CreateNode(BVSGE, c[1][1], part2);
          auto comp =   nf->CreateTerm(BVPLUS, width , nf->CreateSignedMinConst(width), c[0]);

          Kind k;
          assert(comp.isConstant());

          if (CONSTANTBV::BitVector_Lexicompare(comp.GetBVConst(), c[1][0].GetBVConst()) >= 0)
          {
              k = stp::OR;
          }
          else
              k = stp::AND;

          c = nf->CreateNode(k, part1, part2);
       }

          /*
          96866:(BVGT 
              71834:0x00007F73786CE05A
              96864:(BVPLUS 
                37566:0x00007F73786CE020
                96860:(...))))
          */
       if (
          c.GetKind() == BVGT
          && c[1].GetKind() == BVPLUS
          && c[1].Degree() == 2
          && c[0].isConstant()
          && c[1][0].isConstant()
          && shareCount[c[1].GetNodeNum()] <= 1
          )
          {
            auto replacement = nf->CreateTerm(BVPLUS, c[0].GetValueWidth(), c[0], nf->CreateTerm(BVUMINUS, c[0].GetValueWidth(), c[1][0]));
            replacement = nf->CreateNode(BVGT, replacement, c[1][1]);
            auto replacement2 =  nf->CreateNode(BVGE, c[1][1], nf->CreateTerm(BVUMINUS, c[0].GetValueWidth(), c[1][0]));

            Kind k;
            if (CONSTANTBV::BitVector_Lexicompare(c[0].GetBVConst(), c[1][0].GetBVConst()) >= 0)
            {
                k = stp::OR;
            }
            else
                k = stp::AND;
    
            c = nf->CreateNode(k, replacement, replacement2);
          }       

/*
  134790:(BVGT 
    134788:(BVPLUS 
      5894:0xFFFFFFFC
      [...])
    9490:0x00000004)
*/
       if (
          c.GetKind() == BVGT
          && c[0].GetKind() == BVPLUS
          && c[0].Degree() == 2
          && c[0][0].isConstant()
          && c[1].isConstant()
          && shareCount[c[0].GetNodeNum()] <= 1
          )
          {
            auto replacement = nf->CreateTerm(BVPLUS, c[1].GetValueWidth(), c[1], nf->CreateTerm(BVUMINUS, c[1].GetValueWidth(), c[0][0]));
            replacement = nf->CreateNode(BVGT, c[0][1], replacement);
            auto replacement2 =  nf->CreateNode(BVLT,  c[0][1], nf->CreateTerm(BVUMINUS, c[1].GetValueWidth(), c[0][0]));

            Kind k;
            if (CONSTANTBV::BitVector_Lexicompare(c[1].GetBVConst(), c[0][0].GetBVConst()) >= 0)
            {
                k = stp::AND;
            }
            else
                k = stp::OR;
    
            c = nf->CreateNode(k, replacement, replacement2);
          }    



/*
        1146098:(BVAND 
          1021514:0xFFFF80861DA6915D
          1146090:(ITE 
            [1136200]
            35090:0xFFFFFFFFFFFFFFFE
            7186:0xFFFFFFFFFFFFFFFF))))))
            */
      if (
        c.GetKind() == BVAND
        && c.Degree() == 2
        && c[0].GetKind() == BVCONST
        && c[1].GetKind() == ITE
        && c[1][1].GetKind() == BVCONST
        && c[1][2].GetKind() == BVCONST
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
          const auto width  =  c.GetValueWidth();
          const auto and1 =  nf->CreateTerm(BVAND, width, c[0], c[1][1]);
          const auto and2 =  nf->CreateTerm(BVAND, width, c[0], c[1][2]);
          c = nf->CreateTerm(ITE, width, c[1][0], and1, and2);
       }

/*
        1047428:(BVCONCAT 
          6652:0x00000000
          1047426:(ITE 
            [788876]
            6652:0x00000000
            7390:0x00000001)))
*/
      if ( 
        c.GetKind() == BVCONCAT
        && c[0].GetKind() == BVCONST
        && c[1].GetKind() == ITE
        && c[1][1].GetKind() == BVCONST
        && c[1][2].GetKind() == BVCONST
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
          const auto width  =  c.GetValueWidth();
          const auto concat1 =  nf->CreateTerm(BVCONCAT, width, c[0], c[1][1]);
          const auto concat2 =  nf->CreateTerm(BVCONCAT, width, c[0], c[1][2]);
          c = nf->CreateTerm(ITE, width, c[1][0], concat1, concat2);
       }

        /*
        1148183:(NOT 1148182:(EQ 
            6780:0x0000000000000000
            1148180:(BVPLUS 
              1138136:(BVUMINUS 
                [1138134])
              1148176:(ITE 
                [1138038]
                89066:0x00007F79E2596EA3
                34042:0x00007F79E2596EA2))))
        */
      /*
        0 = (a + b)  -->  (bvuminus a) = b.

        The single-use guard on the plus keeps this non-increasing: the plus
        dies and one bvuminus is born. The node factory then often folds the
        bvuminus away: a bvuminus operand cancels, two bvuminuses cancel
        across the equality, and a single-use ITE of constants absorbs it (the
        rule above), which is what the examples show. e.g.

        1149196:(EQ
          6780:0x0000000000000000
          1149194:(BVPLUS
            1149154:(ITE
              1149092:(EQ
                3678:file_file_smt2_1287
                1090576:0x2B)
              118964:0x00007F79E2596EA5
              118918:0x00007F79E2596EA4)
            1149190:(ITE
              [1149092]
              1024228:0xFFFF80861DA6915B
              1145390:0xFFFF80861DA6915C)))
      */
      if (
        c.GetKind() == EQ
        && c[0].GetKind() == BVCONST
        && c[0] == nf->CreateZeroConst(c[0].GetValueWidth())
        && c[1].GetKind() == BVPLUS
        && c[1].Degree() == 2
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
        const auto uminus =
            nf->CreateTerm(BVUMINUS, c[0].GetValueWidth(), c[1][0]);
        c = nf->CreateNode(EQ, uminus, c[1][1]);
       }

   /*
        10160120:(EQ 
        8577822:0x1
        10160116:(BVPLUS 
          2774038:w_49432
          10160114:(BVUMINUS 
            2774032:w_49431)))
            */
      if ( 
        c.GetKind() == EQ
        && c[0].GetKind() == BVCONST
        && c[1].GetKind() == BVPLUS
        && c[1].Degree() == 2
        && c[1][1].GetKind() == BVUMINUS
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
          c = nf->CreateNode(EQ, c[1][0], nf->CreateTerm(BVPLUS, c[0].GetValueWidth(), c[0], c[1][1][0]));
       }


    /*
    (BVSGT 
    9086:0x00
    71160:(ITE 
      [51070]
      9492:0xFF
      9086:0x00))
      */
      if ( 
        (c.GetKind() == BVSGT || c.GetKind() == BVGT)
        && c[0].GetKind() == BVCONST
        && c[1].GetKind() == ITE
        && c[1][1].GetKind() == BVCONST
        && c[1][2].GetKind() == BVCONST
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
          const auto ite1 = nf->CreateNode(c.GetKind(), c[0], c[1][1]);
          const auto ite2 = nf->CreateNode(c.GetKind(), c[0], c[1][2]);
          c = nf->CreateNode(ITE, c[1][0], ite1, ite2);
       }
      
/*
        136180:(BVPLUS 
          136158:(BVPLUS 
            120364:0x00000036
            [126288])
          136178:(BVPLUS 
            108086:0x00000096
        */
    if (c.GetKind() == BVPLUS
        && c.Degree() == 2
        && c[0].GetKind() == BVPLUS
        && c[0].Degree() == 2
        && c[0][0].GetKind() == BVCONST

        && c[1].GetKind() == BVPLUS
        && c[1].Degree() == 2
        && c[1][0].GetKind() == BVCONST

        && shareCount[c[0].GetNodeNum()] <= 1
        && shareCount[c[1].GetNodeNum()] <= 1

        )
        {
          const auto width = c[0].GetValueWidth();
          const auto consts = nf->CreateTerm(BVPLUS, width, c[0][0], c[1][0]);
          c = nf->CreateTerm(BVPLUS, width, nf->CreateTerm(BVPLUS, width, consts, c[0][1]), c[1][1]);
        }
/*
  126266:(EQ 
    120632:(BVPLUS 
      102336:0xFFFFFFDA
      [5110])
    126264:(BVPLUS 
      6494:0x00000002
      126234:(BVCONCAT 
      */
    if (c.GetKind() == EQ
        && c[0].GetKind() == BVPLUS
        && c[0].Degree() == 2
        && c[0][0].GetKind() == BVCONST
        
        && c[1].GetKind() == BVPLUS
        && c[1].Degree() == 2
        && c[1][0].GetKind() == BVCONST
        
        && shareCount[c[0].GetNodeNum()] <= 1
        && shareCount[c[1].GetNodeNum()] <= 1
       
        )
        {
          const auto width = c[0].GetValueWidth();
          //todo maybe move it so it has the least zeroes or ones?
          const auto consts = nf->CreateTerm(BVPLUS, width, c[0][0], nf->CreateTerm(BVUMINUS, width, c[1][0]));
          c = nf->CreateNode(EQ, nf->CreateTerm(BVPLUS, width, consts, c[0][1]), c[1][1]);
        }

/*
  (c1 * x) = c0        -->  x = (c1^-1 * c0),        for odd c1.
  (c1 * x) = (c2 * y)  -->  x = ((c1^-1 * c2) * y),  for odd c1.

  Multiplication by an odd constant is a bijection mod 2^w, so multiplying
  both sides by the inverse preserves the equality. The multiplication on
  the c1 side disappears outright.
*/
    if (c.GetKind() == EQ)
      for (unsigned i = 0; i < 2; i++)
      {
        const ASTNode& mult = c[i];
        const ASTNode& other = c[1 - i];

        if (mult.GetKind() != BVMULT || mult.Degree() != 2 ||
            mult[0].GetKind() != BVCONST ||
            !CONSTANTBV::BitVector_bit_test(mult[0].GetBVConst(), 0) ||
            shareCount[mult.GetNodeNum()] > 1)
          continue;

        const bool otherIsConst = other.GetKind() == BVCONST;
        // The other side's multiplication dies too (it's rebuilt with a
        // different constant), so it must also be unshared.
        const bool otherIsMult =
            other.GetKind() == BVMULT && other.Degree() == 2 &&
            other[0].GetKind() == BVCONST &&
            shareCount[other.GetNodeNum()] <= 1;

        if (!otherIsConst && !otherIsMult)
          continue;

        const auto width = mult.GetValueWidth();
        SubstitutionMap subMap(stpMgr);
        Simplifier simplifier(stpMgr, &subMap);
        const ASTNode inverse = simplifier.MultiplicativeInverse(mult[0]);

        ASTNode rhs;
        if (otherIsConst)
          rhs = nf->CreateTerm(BVMULT, width, inverse, other);
        else
          rhs = nf->CreateTerm(
              BVMULT, width,
              nf->CreateTerm(BVMULT, width, inverse, other[0]), other[1]);

        c = nf->CreateNode(EQ, mult[1], rhs);
        break;
      }

/*
  (a + x + y) = (a + z)  -->  (x + y) = z

  Addition is cancellative mod 2^w, so addends common to both sides drop
  with no overflow condition. Each match cancels one occurrence per side.
*/
    if (c.GetKind() == EQ
        && c[0].GetKind() == BVPLUS
        && c[1].GetKind() == BVPLUS
        && shareCount[c[0].GetNodeNum()] <= 1
        && shareCount[c[1].GetNodeNum()] <= 1)
    {
      const ASTChildren ch0 = c[0].GetChildren();
      const ASTChildren ch1 = c[1].GetChildren();
      ASTVec v0(ch0.begin(), ch0.end());
      ASTVec v1(ch1.begin(), ch1.end());
      bool cancelled = false;

      for (auto it = v0.begin(); it != v0.end();)
      {
        const auto match = std::find(v1.begin(), v1.end(), *it);
        if (match != v1.end())
        {
          v1.erase(match);
          it = v0.erase(it);
          cancelled = true;
        }
        else
          ++it;
      }

      if (cancelled)
      {
        const auto width = c[0].GetValueWidth();
        auto rebuild = [&](const ASTVec& v) {
          if (v.empty())
            return nf->CreateZeroConst(width);
          if (v.size() == 1)
            return v[0];
          return nf->CreateTerm(BVPLUS, width, v);
        };
        c = nf->CreateNode(EQ, rebuild(v0), rebuild(v1));
      }
    }

/*
  (a * b) + (a * d)  -->  a * (b + d)

  Multiplication distributes over addition, so a shared factor pulls out
  and two multiplications become one.
*/
    if (c.GetKind() == BVPLUS
        && c.Degree() == 2
        && c[0].GetKind() == BVMULT
        && c[0].Degree() == 2
        && c[1].GetKind() == BVMULT
        && c[1].Degree() == 2
        && shareCount[c[0].GetNodeNum()] <= 1
        && shareCount[c[1].GetNodeNum()] <= 1)
    {
      bool fired = false;
      for (unsigned i = 0; i < 2 && !fired; i++)
        for (unsigned j = 0; j < 2 && !fired; j++)
          if (c[0][i] == c[1][j])
          {
            const auto width = c.GetValueWidth();
            const auto sum =
                nf->CreateTerm(BVPLUS, width, c[0][1 - i], c[1][1 - j]);
            c = nf->CreateTerm(BVMULT, width, c[0][i], sum);
            fired = true;
          }
    }

/*
(EQ
  62:(BVMULT
    48:t
    60:(BVPLUS
      42:s
      58:...)
  76:(BVMULT
    42:s
    74:(BVPLUS
      48:t
      72:...))
  */
    if (c.GetKind() == EQ
        && c[0].GetKind() == BVMULT
        && c[0].Degree() ==2
        && c[0][1].GetKind() == BVPLUS
        && c[0][1].Degree() ==2

        && c[1].GetKind() == BVMULT
        && c[1].Degree() ==2
        && c[1][1].GetKind() == BVPLUS
        && c[1][1].Degree() ==2

        && shareCount[c[0].GetNodeNum()] <= 1
        && shareCount[c[1].GetNodeNum()] <= 1

        && c[0][0] == c[1][1][0]
        && c[1][0] == c[0][1][0]

        )
        {
          const auto width = c[0].GetValueWidth();
          const auto left = nf->CreateTerm(BVMULT, width, c[0][0], c[0][1][1]);
          const auto right = nf->CreateTerm(BVMULT, width, c[1][0], c[1][1][1]);
          c = nf->CreateNode(EQ, left,right);
        }

/*
  An if-then-else with an if-then-else one level down that chooses the same
  value: the two multiplexers become one, selected by a connective. With the
  inner one on the else side,

    ITE(c, t, ITE(d, t, b))  -->  ITE(c OR d,     t, b)
    ITE(c, t, ITE(d, a, t))  -->  ITE(c OR NOT d, t, a)

  and on the then side, where the outer's else branch is what repeats,

    ITE(c, ITE(d, a, e), e)  -->  ITE(c AND d,     a, e)
    ITE(c, ITE(d, e, b), e)  -->  ITE(c AND NOT d, b, e)

  Bit-blasting a w-bit multiplexer costs 3w AND gates and the connective costs
  one, so this trades the whole width for a single gate. The two negated forms
  additionally build a NOT, which is a complemented edge in the AIG and so
  costs nothing there -- the pass's only rules that add an AST node without
  adding bit-blasted difficulty.

  All four need the inner multiplexer to die with the rewrite. Where it is
  shared it stays, the merged node is built beside it, and the rewrite is a
  straight loss -- hence the share count. Symbolic execution emits these:
  a branch that leaves part of the state alone reaches the same value under
  several guards.
*/
      if (
        c.GetKind() == ITE
        && c[2].GetKind() == ITE
        && (c[2][1] == c[1] || c[2][2] == c[1])
        && shareCount[c[2].GetNodeNum()] <= 1
       )
       {
          // Which branch of the inner if-then-else repeats the outer's then.
          const bool repeatedOnThen = (c[2][1] == c[1]);

          const auto inner =
              repeatedOnThen ? c[2][0] : nf->CreateNode(NOT, c[2][0]);
          const auto cond = nf->CreateNode(OR, c[0], inner);
          const auto other = repeatedOnThen ? c[2][2] : c[2][1];

          if (c.GetType() == BOOLEAN_TYPE)
            c = nf->CreateNode(ITE, cond, c[1], other);
          else
            c = nf->CreateArrayTerm(ITE, c.GetIndexWidth(), c.GetValueWidth(),
                                    cond, c[1], other);
       }

      if (
        c.GetKind() == ITE
        && c[1].GetKind() == ITE
        && (c[1][1] == c[2] || c[1][2] == c[2])
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
          // Which branch of the inner if-then-else repeats the outer's else.
          const bool repeatedOnThen = (c[1][1] == c[2]);

          const auto inner =
              repeatedOnThen ? nf->CreateNode(NOT, c[1][0]) : c[1][0];
          const auto cond = nf->CreateNode(AND, c[0], inner);
          const auto other = repeatedOnThen ? c[1][2] : c[1][1];

          if (c.GetType() == BOOLEAN_TYPE)
            c = nf->CreateNode(ITE, cond, other, c[2]);
          else
            c = nf->CreateArrayTerm(ITE, c.GetIndexWidth(), c.GetValueWidth(),
                                    cond, other, c[2]);
       }

    return c;
  }

  // A leaf, or a node already rewritten: answered without a frame, exactly
  // as the recursive version answered it without a call.
  bool Rewriting::alreadyKnown(const ASTNode& n, ASTNode& answer)
  {
    if (n.Degree() == 0)
    {
      answer = n;
      return true;
    }

    const auto it = fromTo.find(n.GetNodeNum());
    if (it != fromTo.end())
    {
      answer = it->second;
      return true;
    }
    return false;
  }

  // One node's progress through its children. `phase` says what a value
  // arriving from below is: the recursive rewrite() had two call sites per
  // child -- the child itself, and again on whatever the rules made of it
  // -- and a frame has to know which one it is waiting for.
  struct Rewriting::Frame
  {
    ASTNode n;
    ASTChildren children;
    ASTVec newChildren; // copy on write: empty until a child changes.
    bool changed = false;
    unsigned i = 0; // the child being worked on

    ASTNode begin; // that child as it was before anything ran on it
    ASTNode start; // and as it was after rewriting, before the rules

    enum Phase
    {
      Fresh,
      AwaitingChild,
      AwaitingTransformed
    };
    Phase phase = Fresh;

    Frame(const ASTNode& n_) : n(n_), children(n_.GetChildren()) {}
  };

  ASTNode Rewriting::rewrite(const ASTNode& n)
  {
    ASTNode result;
    if (alreadyKnown(n, result))
      return result;

    // A deque, so descending into a child never moves the frames above it:
    // `current` stays valid across a push.
    std::deque<Frame> stack;
    stack.emplace_back(n);

    // Copy on write.
    auto fill = [](Frame& f, const ASTNode& find)
    {
      f.newChildren.reserve(f.children.size());
      const auto findIt =
          std::find(f.children.begin(), f.children.end(), find);
      assert(findIt != f.children.end());
      f.newChildren.insert(f.newChildren.end(), f.children.begin(), findIt);
      f.changed = true;
    };

    // The tail of the recursive version's loop body: `c` is the child in
    // its final form.
    auto finishChild = [&fill](Frame& f, const ASTNode& c)
    {
      // TODO should probably update the sharecount.
      if (f.begin != c && !f.changed)
        fill(f, f.begin);
      if (f.changed)
        f.newChildren.push_back(c);
      f.i++;
    };

    // With the child rewritten, run the rules over it. A rule that fires
    // sends its result back through the walk, which is the second of the
    // two call sites; true means this frame has descended for that.
    auto afterRewrite = [&](Frame& f, const ASTNode& rewritten) -> bool
    {
      f.start = rewritten;
      const ASTNode c = applyRules(rewritten);

      if (f.start == c)
      {
        finishChild(f, c);
        return false;
      }

      ASTNode known;
      if (alreadyKnown(c, known))
      {
        removed++;
        finishChild(f, known);
        return false;
      }

      f.phase = Frame::AwaitingTransformed;
      stack.emplace_back(c);
      return true;
    };

    while (true)
    {
      Frame& current = stack.back();
      bool descended = false;

      // Take delivery of the child this frame descended for.
      if (current.phase == Frame::AwaitingChild)
      {
        current.phase = Frame::Fresh;
        descended = afterRewrite(current, result);
      }
      else if (current.phase == Frame::AwaitingTransformed)
      {
        current.phase = Frame::Fresh;
        removed++;
        finishChild(current, result);
      }

      while (!descended && current.i < current.children.size())
      {
        current.begin = current.children[current.i];

        ASTNode known;
        if (alreadyKnown(current.begin, known))
        {
          descended = afterRewrite(current, known);
          continue;
        }

        current.phase = Frame::AwaitingChild;
        stack.emplace_back(current.begin);
        descended = true;
      }

      if (descended)
        continue;

      Frame& done = stack.back();
      result = done.n;

      if (done.newChildren.size() > 0)
      {
        assert(done.newChildren.size() == done.children.size());

        if (done.n.GetType() == BOOLEAN_TYPE)
          result = nf->CreateNode(done.n.GetKind(), done.newChildren);
        else
          result = nf->CreateArrayTerm(done.n.GetKind(), done.n.GetIndexWidth(),
                                       done.n.GetValueWidth(),
                                       done.newChildren);
      }

      //TODO is this right? We've replaced the children, but never this node?
      fromTo.insert({done.n.GetNodeNum(), result});

      stack.pop_back();
      if (stack.empty())
        return result;
    }
  }
}
