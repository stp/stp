/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: October, 2026
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

#include "stp/Simplifier/GraphRulePasses.h"
#include "stp/Util/DagWalk.h"
#include "stp/Simplifier/Simplifier.h"
#include "stp/Simplifier/SubstitutionMap.h"
#include <algorithm>
#include <cassert>
#include <iostream>
#include <map>
#include <tuple>
#include <unordered_map>
#include <vector>

namespace stp
{
  // ------------------------------------------------------------ rewriting
  //
  // A copy of the rules in Rewriting.cpp, reading the graph's parent counts
  // through unshared() where that pass reads its share count. Kept in step
  // by hand while both exist.

  // Operators whose every output bit depends only on the operands' bit at
  // the same position. BVOR is listed for the hashing factory's sake: the
  // simplifying one spells it NOT(AND(NOT, NOT)) and so never builds one.
  static bool isBitwise(const Kind k)
  {
    return k == BVNOT || k == BVAND || k == BVOR || k == BVXOR;
  }

  // Every sharing-aware rule, in order, applied to one node. Each rule
  // sees what the rules before it produced. Nothing here descends into
  // the DAG: the caller decides what to do with a node that changed.
  ASTNode GraphRewriting::applyRules(const ASTNode& given)
  {
     ASTNode c = given;

     if (
        c.GetKind() == EQ 
        && c[0].GetKind() == BVCONST 
        && c[1].GetKind() == BVPLUS  
        && c[1][0].GetKind() == BVCONST  
        && c[1].Degree() > 2
        && unshared(c[1])
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
         && unshared(c[0])
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
        && unshared(c[1])
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
        && unshared(c[0])
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
        && unshared(c[0])
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
        && unshared(c[1][0])
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
        && unshared(c[1])
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
          && unshared(c[1])
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
          && unshared(c[0])
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
        && unshared(c[1])
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
        && unshared(c[1])
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
        && unshared(c[1])
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
        && unshared(c[1])
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
        && unshared(c[1])
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

        && unshared(c[0])
        && unshared(c[1])

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
        
        && unshared(c[0])
        && unshared(c[1])
       
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
            !unshared(mult))
          continue;

        const bool otherIsConst = other.GetKind() == BVCONST;
        // The other side's multiplication dies too (it's rebuilt with a
        // different constant), so it must also be unshared.
        const bool otherIsMult =
            other.GetKind() == BVMULT && other.Degree() == 2 &&
            other[0].GetKind() == BVCONST &&
            unshared(other);

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
        && unshared(c[0])
        && unshared(c[1]))
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
        && unshared(c[0])
        && unshared(c[1]))
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

        && unshared(c[0])
        && unshared(c[1])

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
        && unshared(c[2])
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
        && unshared(c[1])
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

/*
  A branch of an if-then-else knows its own condition, so a test the
  condition decides can go. The SimplifyingNodeFactory already takes every
  such test that costs nothing to remove -- a branch of a nested
  multiplexer, or a conjunction that collapses to a constant or to its one
  surviving conjunct. What is left for here is the case that rebuilds:

    ITE(c, OR(c1, x, y), d)  -->  ITE(c, OR(x, y), d)   when c refutes c1

  where the disjunction has three or more children, so dropping one builds a
  node the branch did not contain. That is a loss unless the disjunction died
  with it, which is what the share count decides.
*/
    if (c.GetKind() == ITE)
      for (unsigned branch = 1; branch <= 2; branch++)
      {
        if (c.GetKind() != ITE)
          continue;

        const ASTNode inner = c[branch];
        if ((inner.GetKind() != AND && inner.GetKind() != OR) ||
            inner.Degree() < 3 || !unshared(inner))
          continue;

        const ASTNode cond = c[0];
        const ASTNode known = (branch == 1) ? cond : nf->CreateNode(NOT, cond);
        const bool isAnd = (inner.GetKind() == AND);

        // Whether `known` and `cond` can hold together. Delegated to the
        // factory: conjoining them reaches every contradiction AND already
        // folds, at the price of building the conjunction.
        auto refutes = [&](const ASTNode& test) {
          return nf->CreateNode(AND, known, test) == stpMgr->ASTFalse;
        };

        ASTVec kept;
        bool annihilated = false;
        for (const ASTNode& child : inner.GetChildren())
        {
          // A decided child is either the node's annihilator, which settles
          // the branch, or its identity, which just goes.
          if (refutes(isAnd ? child : nf->CreateNode(NOT, child)))
          {
            annihilated = true;
            break;
          }
          if (!refutes(isAnd ? nf->CreateNode(NOT, child) : child))
            kept.push_back(child);
        }

        if (!annihilated && kept.size() == inner.Degree())
          continue;

        // The collapsing cases are the factory's, but its test is the cheap
        // syntactic one, so a branch it could not fold still lands here.
        ASTNode replacement;
        if (annihilated)
          replacement = isAnd ? stpMgr->ASTFalse : stpMgr->ASTTrue;
        else if (kept.empty())
          replacement = isAnd ? stpMgr->ASTTrue : stpMgr->ASTFalse;
        else if (kept.size() == 1)
          replacement = kept[0];
        else
          replacement = nf->CreateNode(inner.GetKind(), kept);
        const ASTNode thenBranch = (branch == 1) ? replacement : c[1];
        const ASTNode elseBranch = (branch == 1) ? c[2] : replacement;

        if (c.GetType() == BOOLEAN_TYPE)
          c = nf->CreateNode(ITE, cond, thenBranch, elseBranch);
        else
          c = nf->CreateArrayTerm(ITE, c.GetIndexWidth(), c.GetValueWidth(),
                                  cond, thenBranch, elseBranch);
      }

    /*
      A bitwise operation computes each output bit from the operands' bit
      at that position alone, so an extract of one is the same operation
      over the extracts of its operands:

        extract(a & b, hi, lo)  ==  extract(a, hi, lo) & extract(b, hi, lo)

      Pushing the extract inwards narrows the operation to the bits that
      are actually read. The bit-blaster does not do this for itself --
      BVEXTRACT blasts its child whole and selects afterwards, with a
      comment saying the unread bits could be skipped but that memoisation
      makes it awkward -- so the word level is where the width has to come
      off.

      The guard is the usual one, and here it is what makes the rewrite
      worth doing at all rather than what makes it safe: the operation
      dies only if nothing else reads it. Node count can still rise, by
      one per operand beyond the first, which is why this is off by
      default and measured rather than assumed. What the extra extracts
      buy is a chance to go further down: an extract meeting a constant
      folds, meeting a concat or another extract composes, and meeting a
      term with a width-narrowing rule of its own exposes that rule.
    */
    if (
      c.GetKind() == BVEXTRACT
      && stpMgr->UserFlags.extract_through_bitwise
      && isBitwise(c[0].GetKind())
      && unshared(c[0])
     )
     {
        const auto width = c.GetValueWidth();
        ASTVec kids;
        kids.reserve(c[0].Degree());
        for (const ASTNode& operand : c[0])
          kids.push_back(
              nf->CreateTerm(BVEXTRACT, width, operand, c[1], c[2]));

        narrowedBitwise++;
        c = nf->CreateTerm(c[0].GetKind(), width, kids);
     }

    return c;
  }

  ASTNode GraphRewriting::topLevel(ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::Rewriting);
    narrowedBitwise = 0;
    const ASTNode result = run(n);
    stats();
    stpMgr->GetRunTimes()->stop(RunTimes::Rewriting);
    return result;
  }

  void GraphRewriting::topLevel(MutableGraph& graph)
  {
    stpMgr->GetRunTimes()->start(RunTimes::Rewriting);
    narrowedBitwise = 0;
    run(graph);
    stats();
    stpMgr->GetRunTimes()->stop(RunTimes::Rewriting);
    stpMgr->ASTNodeStats("After Sharing-aware rewriting: ", graph.root());
  }

  void GraphRewriting::stats()
  {
    if (!stpMgr->UserFlags.stats_flag)
      return;
    std::cerr << "{Rewriting} rules fired:" << fired << std::endl;
    std::cerr << "{Rewriting} bitwise operations narrowed by an extract:"
              << narrowedBitwise << std::endl;
  }

  // ------------------------------------------------------------ flattening

  bool GraphFlatten::flattenable(Kind k)
  {
    return k == OR || k == AND || k == XOR || k == BVXOR || k == BVOR ||
           k == BVAND || k == BVPLUS || k == BVMULT;
  }

  // Duplicates among the entries merged in are dropped for the idempotent
  // kinds, as the factory would drop them.
  static bool idempotent(Kind k)
  {
    return k == AND || k == OR || k == BVAND || k == BVOR;
  }

  ASTNode GraphFlatten::applyRules(const ASTNode& c)
  {
    const Kind k = c.GetKind();
    if (!flattenable(k))
      return c;
    const bool top = (k == AND) && g->isRootNode(c);

    ASTVec kept;
    std::vector<ASTNode> pending; // merged-in entries, placed in turn
    ankerl::unordered_dense::set<uint64_t> seen;
    unsigned merged = 0;
    auto place = [&](const ASTNode& e) {
      if (e.GetKind() != k || !(top || unshared(e)))
      {
        kept.push_back(e);
        return;
      }
      merged++;
      for (const ASTNode& grandchild : e)
      {
        if (idempotent(k) && !seen.insert(grandchild.GetNodeNum()).second)
          continue;
        pending.push_back(grandchild);
      }
    };
    for (const ASTNode& e : c)
      place(e);
    for (size_t i = 0; i < pending.size(); i++)
      place(ASTNode(pending[i])); // place may grow pending
    if (merged == 0)
      return c;

    (top ? topRemoved : removed) += merged;
    if (c.GetType() == BOOLEAN_TYPE)
      return nf->CreateNode(k, kept);
    return nf->CreateTerm(k, c.GetValueWidth(), kept);
  }

  ASTNode GraphFlatten::topLevel(ASTNode& n)
  {
    stpMgr->GetRunTimes()->start(RunTimes::Flatten);
    removed = 0;
    topRemoved = 0;
    const ASTNode result = run(n);
    stats();
    stpMgr->GetRunTimes()->stop(RunTimes::Flatten);
    return result;
  }

  void GraphFlatten::topLevel(MutableGraph& graph)
  {
    stpMgr->GetRunTimes()->start(RunTimes::Flatten);
    removed = 0;
    topRemoved = 0;
    run(graph);
    stats();
    stpMgr->GetRunTimes()->stop(RunTimes::Flatten);
    stpMgr->ASTNodeStats("After Sharing-aware Flattening: ", graph.root());
  }

  void GraphFlatten::stats()
  {
    if (!stpMgr->UserFlags.stats_flag)
      return;
    std::cerr << "{Flatten} Internal nodes removed:" << removed << std::endl;
    std::cerr << "{Flatten} Top nodes removed:" << topRemoved << std::endl;
  }

  // -------------------------------------------------------- common factor
  //
  // A copy of the extraction in CommonFactor.cpp, reading the graph's
  // parent counts through unshared() where that pass reads its reference
  // maps.

bool GraphCommonFactor::productOf(const ASTNode& addend, Addend& out) const
{
  const bool negated = addend.GetKind() == BVUMINUS;

  // The negation dies with the product it wraps, so both have to.
  if (negated && !unshared(addend))
    return false;

  const ASTNode& product = negated ? addend[0] : addend;
  if (product.GetKind() != BVMULT || !unshared(product))
    return false;

  out.negated = negated;
  out.product = product;
  return true;
}

// The addend with one occurrence of the factor taken out of its product,
// keeping the negation the addend arrived with.
ASTNode GraphCommonFactor::without(const Addend& a, const ASTNode& factor,
                              unsigned width)
{
  ASTVec kept;
  kept.reserve(a.product.Degree() - 1);

  bool dropped = false;
  for (const ASTNode& operand : a.product)
  {
    if (!dropped && operand == factor)
    {
      dropped = true;
      continue;
    }
    kept.push_back(operand);
  }
  assert(dropped);

  ASTNode result =
      kept.size() == 1 ? kept[0] : nf->CreateTerm(BVMULT, width, kept);

  if (a.negated)
    result = nf->CreateTerm(BVUMINUS, width, result);

  return result;
}

ASTNode GraphCommonFactor::sumOf(const ASTVec& addends, unsigned width)
{
  assert(!addends.empty());
  if (addends.size() == 1)
    return addends[0];
  return nf->CreateTerm(BVPLUS, width, addends);
}

bool GraphCommonFactor::extractOne(ASTVec& addends, unsigned width)
{
  // Two products at least, or there is nothing an operand can be shared
  // between. Most sums fail this, and it is the whole cost of them.
  size_t candidates = 0;
  for (const ASTNode& a : addends)
    if (a.GetKind() == BVMULT ||
        (a.GetKind() == BVUMINUS && a[0].GetKind() == BVMULT))
      candidates++;

  if (candidates < 2)
    return false;

  std::vector<Addend> products;
  products.reserve(addends.size());

  size_t reducible = 0;
  for (const ASTNode& a : addends)
  {
    Addend p;
    if (productOf(a, p))
      reducible++;
    products.push_back(p);
  }

  // The share guard may have ruled enough of them out.
  if (reducible < 2)
    return false;

  // How many of the products each operand appears in. Ordered by node
  // number, so the operand the scan below settles on doesn't depend on the
  // order the addends arrived in.
  std::map<uint64_t, uint32_t> tally;
  std::map<uint64_t, ASTNode> byNum;

  for (const Addend& p : products)
  {
    if (p.product.IsNull())
      continue;

    // An operand a product repeats is still one operand of it to give up.
    ankerl::unordered_dense::set<uint64_t> counted;
    for (const ASTNode& operand : p.product)
      if (counted.insert(operand.GetNodeNum()).second)
      {
        tally[operand.GetNodeNum()]++;
        byNum.insert({operand.GetNodeNum(), operand});
      }
  }

  uint32_t best = 1;
  uint64_t chosen = 0;
  for (const auto& entry : tally)
    if (entry.second > best)
    {
      best = entry.second;
      chosen = entry.first;
    }

  // One product holding an operand is the operand it already multiplies by:
  // taking it out builds the same multiplication somewhere else.
  if (best < 2)
    return false;

  const ASTNode factor = byNum.find(chosen)->second;

  ASTVec inner, kept;
  inner.reserve(best);
  kept.reserve(addends.size() - best + 1);

  for (size_t i = 0; i < addends.size(); i++)
  {
    const Addend& p = products[i];
    const bool holds =
        !p.product.IsNull() &&
        std::find(p.product.begin(), p.product.end(), factor) !=
            p.product.end();

    if (holds)
      inner.push_back(without(p, factor, width));
    else
      kept.push_back(addends[i]);
  }
  assert(inner.size() == static_cast<size_t>(best));

  // The remainders can share a factor of their own: the two operands the
  // products of (x*y*a + x*y*b) have in common come out one after the
  // other, and the second is only visible once the first is gone.
  extract(inner, width);

  kept.push_back(nf->CreateTerm(BVMULT, width, factor, sumOf(inner, width)));
  addends.swap(kept);

  saved += best - 1;
  return true;
}

bool GraphCommonFactor::extract(ASTVec& addends, unsigned width)
{
  bool changed = false;

  // Each round replaces the products holding the factor -- two of them at
  // least, each costing a multiplication -- with one multiplication, so
  // what the round counts strictly falls and the loop ends.
  while (extractOne(addends, width))
    changed = true;

  return changed;
}

ASTNode GraphCommonFactor::applyRules(const ASTNode& c)
{
  if (c.GetKind() != BVPLUS)
    return c;
  ASTVec addends(c.begin(), c.end());
  if (!extract(addends, c.GetValueWidth()))
    return c;
  return sumOf(addends, c.GetValueWidth());
}

ASTNode GraphCommonFactor::topLevel(const ASTNode& n)
{
  stpMgr->GetRunTimes()->start(RunTimes::CommonFactor);
  saved = 0;
  const ASTNode result = run(n);
  stats();
  stpMgr->GetRunTimes()->stop(RunTimes::CommonFactor);
  return result;
}

void GraphCommonFactor::topLevel(MutableGraph& graph)
{
  stpMgr->GetRunTimes()->start(RunTimes::CommonFactor);
  saved = 0;
  run(graph);
  stats();
  stpMgr->GetRunTimes()->stop(RunTimes::CommonFactor);
  stpMgr->ASTNodeStats("After Common Factor Extraction: ", graph.root());
}

void GraphCommonFactor::stats()
{
  if (stpMgr->UserFlags.stats_flag)
    std::cerr << "{CommonFactor} Multiplications saved:" << saved << std::endl;
}

// ------------------------------------------------------------ merge same
//
// A copy of MergeSame.h's rules over the root conjunction.

void GraphMergeSame::merge(ASTVec& conjuncts, unsigned firstIndex,
                           unsigned secondIndex)
{
  const auto& first = conjuncts[firstIndex];
  const auto& second = conjuncts[secondIndex];
  assert(second.GetKind() == OR && second.Degree() == 2);
  if (first.GetKind() != OR || first.Degree() != 2)
    return;
  ASTNode newN;
  if (first[0] == second[0])
    newN = nf->CreateNode(OR, first[0], nf->CreateNode(AND, first[1], second[1]));
  else if (first[1] == second[0])
    newN = nf->CreateNode(OR, first[1], nf->CreateNode(AND, first[0], second[1]));
  else if (first[1] == second[1])
    newN = nf->CreateNode(OR, first[1], nf->CreateNode(AND, first[0], second[0]));
  else if (first[0] == second[1])
    newN = nf->CreateNode(OR, first[0], nf->CreateNode(AND, first[1], second[0]));
  else
    return;
  replaced++;
  conjuncts[firstIndex] = newN;
  conjuncts[secondIndex] = stpMgr->ASTTrue;
}

ASTNode GraphMergeSame::applyRules(const ASTNode& n)
{
  if (n.GetKind() != AND || !g->isRootNode(n))
    return n;
  const unsigned before = replaced;
  // Node number to index in the children vector.
  std::unordered_map<uint64_t, unsigned> seen;
  ASTVec conjuncts = FlattenKind(AND, n.GetChildren());
  for (unsigned i = 0; i < conjuncts.size(); i++)
  {
    auto& c = conjuncts[i];
    // Convert AND to OR.
    if (c.GetKind() == NOT && c[0].GetKind() == AND)
    {
      ASTVec children;
      for (const auto& child : c[0].GetChildren())
        children.push_back(nf->CreateNode(NOT, child));
      c = nf->CreateNode(OR, children);
      replaced++;
    }
    // (AND (OR a b) .... (OR a c )) => (OR a (AND b c))
    if (c.GetKind() == OR && c.Degree() == 2)
    {
      if (seen.find(c[0].GetNodeNum()) != seen.end())
        merge(conjuncts, seen[c[0].GetNodeNum()], i);
      else if (seen.find(c[1].GetNodeNum()) != seen.end())
        merge(conjuncts, seen[c[1].GetNodeNum()], i);
      else
      {
        seen[c[0].GetNodeNum()] = i;
        seen[c[1].GetNodeNum()] = i;
      }
    }
    // (AND (OR -a -b) .... (OR a b )) => (XOR a b ))
    if (c.GetKind() == OR && c.Degree() == 2)
    {
      const auto not0 = nf->CreateNode(NOT, c[0]);
      const auto not1 = nf->CreateNode(NOT, c[1]);
      if (seen.find(not0.GetNodeNum()) != seen.end() &&
          seen.find(not1.GetNodeNum()) != seen.end())
      {
        const auto i0 = seen[not0.GetNodeNum()];
        const auto i1 = seen[not1.GetNodeNum()];
        if (i0 == i1 && conjuncts[i0].GetKind() == OR &&
            conjuncts[i0].Degree() == 2 && conjuncts[i0][0] == not0 &&
            conjuncts[i0][1] == not1 && i0 != i && not0 != not1)
        {
          conjuncts[i0] = nf->CreateNode(XOR, c[0], c[1]);
          conjuncts[i] = stpMgr->ASTTrue;
          replaced++;
        }
      }
    }
  }
  if (replaced == before)
    return n;
  return nf->CreateNode(AND, conjuncts);
}

ASTNode GraphMergeSame::topLevel(ASTNode& n)
{
  stpMgr->GetRunTimes()->start(RunTimes::MergeSame);
  replaced = 0;
  const ASTNode result = run(n);
  if (stpMgr->UserFlags.stats_flag)
    std::cerr << "{MergeSame} replaced:" << replaced << std::endl;
  stpMgr->GetRunTimes()->stop(RunTimes::MergeSame);
  return result;
}

void GraphMergeSame::topLevel(MutableGraph& graph)
{
  stpMgr->GetRunTimes()->start(RunTimes::MergeSame);
  replaced = 0;
  run(graph);
  if (stpMgr->UserFlags.stats_flag)
    std::cerr << "{MergeSame} replaced:" << replaced << std::endl;
  stpMgr->GetRunTimes()->stop(RunTimes::MergeSame);
  stpMgr->ASTNodeStats("After Merge Same: ", graph.root());
}

// --------------------------------------------------------- pure literals
//
// FindPureLiterals::build over the current formula, iterative.

void GraphFindPureLiterals::build(const ASTNode& root, Polarities& out)
{
  std::vector<std::pair<ASTNode, polarity_type>> stack;
  stack.push_back({root, truePolarity});
  while (!stack.empty())
  {
    const ASTNode n = stack.back().first;
    const polarity_type polarity = stack.back().second;
    stack.pop_back();
    if (n.isConstant())
      continue;
    auto it = out.find(n);
    if (it != out.end())
    {
      if ((polarity | it->second) == it->second)
        continue; // already traversed with this polarity
      it->second |= polarity;
    }
    else
      out.insert({n, polarity});
    switch (n.GetKind())
    {
      case AND:
      case OR:
        for (const ASTNode& c : n)
          stack.push_back({c, polarity});
        break;
      case NOT:
        stack.push_back({n[0], polarity == bothPolarity
                                   ? bothPolarity
                                   : (polarity == truePolarity ? falsePolarity
                                                               : truePolarity)});
        break;
      case ITE:
        stack.push_back({n[0], bothPolarity});
        stack.push_back({n[1], polarity});
        stack.push_back({n[2], polarity});
        break;
      default:
        for (const ASTNode& c : n)
          stack.push_back({c, bothPolarity});
        break;
    }
  }
}

unsigned GraphFindPureLiterals::topLevel(MutableGraph& graph, Simplifier* simp)
{
  bm->GetRunTimes()->start(RunTimes::PureLiterals);
  // Setting a literal narrows a node's values, never widens them: the
  // memo above stays a sound over-approximation.
  MutableGraph::DomainRecompute recompute(graph, false);
  Polarities polarities;
  build(graph.root(), polarities);
  // Deterministic order: the substitutions fold the formula as they go.
  std::vector<std::pair<ASTNode, polarity_type>> pure;
  for (const auto& e : polarities)
    if (e.first.GetKind() == SYMBOL && e.first.GetType() == BOOLEAN_TYPE &&
        e.second != bothPolarity)
      pure.push_back(e);
  std::sort(pure.begin(), pure.end(),
            [](const std::pair<ASTNode, polarity_type>& a,
               const std::pair<ASTNode, polarity_type>& b) {
              return a.first.GetNodeNum() < b.first.GetNodeNum();
            });
  unsigned set = 0;
  for (const auto& e : pure)
  {
    const ASTNode value = e.second == truePolarity ? bm->ASTTrue : bm->ASTFalse;
    // The definition first: a refusal (a protected symbol) leaves the
    // formula as it is.
    if (!simp->UpdateSubstitutionMap(e.first, value))
      continue;
    graph.substitute(e.first, value);
    set++;
  }
  bm->GetRunTimes()->stop(RunTimes::PureLiterals);
  bm->ASTNodeStats("After Pure Literals. ", graph.root());
  return set;
}

ASTNode GraphFindPureLiterals::topLevel(const ASTNode& n, Simplifier* simp)
{
  MutableGraph graph(*bm);
  graph.import(n);
  topLevel(graph, simp);
  return graph.exportRoot();
}

// -------------------------------------------------------- split extracts
//
// SplitExtracts::topLevel's range logic over the graph's parents.

void GraphSplitExtracts::topLevel(MutableGraph& graph, Simplifier* simp)
{
  assert(bm.UserFlags.enable_split_extracts);
  bm.GetRunTimes()->start(RunTimes::SplitExtracts);
  // A symbol becomes fresh pieces with the full range: the domains above
  // a split are recomputed.
  MutableGraph::DomainRecompute recompute(graph, true);
  introduced = 0;
  extractsFound = 0;

  // The bit-vector symbols of the current formula, once each, in a
  // deterministic order.
  std::vector<ASTNode> symbols;
  {
    ASTNodeSet seen;
    walkPreOrder(graph.root(), [&](const ASTNode& x) {
      if (!seen.insert(x).second)
        return false;
      if (x.GetKind() == SYMBOL && x.GetValueWidth() > 0)
        symbols.push_back(x);
      return x.Degree() > 0;
    });
  }
  std::sort(symbols.begin(), symbols.end(),
            [](const ASTNode& a, const ASTNode& b) {
              return a.GetNodeNum() < b.GetNodeNum();
            });

  NodeFactory* const nf = &graph.factory();
  std::vector<ASTNode> parents;
  for (const ASTNode& symbol : symbols)
  {
    parents.clear();
    graph.parents(symbol, parents);
    if (parents.size() < 2)
      continue; // Don't want to split if there's just one.
    // (high, low) of each extract; a use that is not an extract covers
    // every bit and so blocks all splitting.
    std::vector<std::tuple<ASTNode, uint64_t, uint64_t>> ranges;
    for (const ASTNode& p : parents)
    {
      if (p.GetKind() == BVEXTRACT && p[0] == symbol)
      {
        ranges.push_back(std::make_tuple(p, p[1].GetUnsignedConst(),
                                         p[2].GetUnsignedConst()));
        extractsFound++;
      }
      else
        ranges.push_back(std::make_tuple(ASTNode(), UINT64_MAX, 0));
    }
    std::sort(ranges.begin(), ranges.end(), [](const auto& p0, const auto& p1) {
      return std::get<2>(p0) < std::get<2>(p1);
    });
    // An extract is split out iff its range overlaps no other use.
    std::vector<std::pair<uint64_t, uint64_t>> toSplit; // (high, low)
    uint64_t highest = 0;
    for (unsigned i = 0; i < ranges.size(); i++)
    {
      const auto high = std::get<1>(ranges[i]);
      const auto low = std::get<2>(ranges[i]);
      bool replace = true;
      if (i + 1 != ranges.size() && std::get<2>(ranges[i + 1]) <= high)
        replace = false;
      if (i != 0)
      {
        if (low <= highest)
          replace = false;
        highest = std::max(high, highest);
      }
      else
        highest = high;
      if (replace && !std::get<0>(ranges[i]).IsNull())
        toSplit.push_back({high, low});
    }
    if (toSplit.empty())
      continue;

    // Rename the symbol piecewise: a fresh variable for each split range
    // and for each gap between them. The one substitution both rewrites
    // the formula (a split extract over the concat simplifies to its fresh
    // variable as the holder is re-keyed) and, recorded as a definition,
    // rebuilds the symbol's value during model construction.
    const uint64_t width = symbol.GetValueWidth();
    ASTNode concatenated;
    const auto append = [&](const ASTNode& piece) {
      if (concatenated.IsNull())
        concatenated = piece;
      else
        concatenated = nf->CreateTerm(
            BVCONCAT, concatenated.GetValueWidth() + piece.GetValueWidth(),
            piece, concatenated);
    };
    uint64_t nextBit = 0;
    for (const auto& range : toSplit)
    {
      if (range.second > nextBit)
        append(bm.CreateFreshVariable(0, range.second - nextBit, "_STP"));
      append(bm.CreateFreshVariable(0, range.first - range.second + 1, "_STP"));
      nextBit = range.first + 1;
    }
    if (nextBit < width)
      append(bm.CreateFreshVariable(0, width - nextBit, "_STP"));
    assert(concatenated.GetValueWidth() == width);
    // Fails if the extensionality context protects the symbol.
    if (!simp->UpdateSubstitutionMapFewChecks(symbol, concatenated))
      continue;
    graph.substitute(symbol, concatenated);
    introduced += toSplit.size();
  }

  bm.GetRunTimes()->stop(RunTimes::SplitExtracts);
  if (bm.UserFlags.stats_flag)
  {
    std::cerr << "{Split Extracts} Extracts over variables found: "
              << extractsFound << std::endl;
    std::cerr << "{Split Extracts} variables introduced: " << introduced
              << std::endl;
  }
  bm.ASTNodeStats("After Split Extracts. ", graph.root());
}

ASTNode GraphSplitExtracts::topLevel(const ASTNode& n, Simplifier* simp)
{
  // A symbol this pass defines must not already be a key of the map;
  // after applying any pending substitutions none in the formula is.
  const ASTNode pending = simp->applySubstitutionMapAtTopLevel(n);
  MutableGraph graph(bm);
  graph.import(pending);
  topLevel(graph, simp);
  return graph.exportRoot();
}
}
