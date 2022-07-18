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

  Some rules in here don't need to be sharing aware and can be moved into the node factory
*/



#include "stp/Simplifier/Rewriting.h"
#include <list>

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
  void Rewriting::buildShareCount(const ASTNode& n)
  {
    if (n.Degree() == 0)
      return;

    if (shareCount[n.GetNodeNum()]++ > 0) // 0 first time, 1 second time.
      return;
  
    for (const auto& c: n.GetChildren())
        buildShareCount(c);
  }

  // true if popCount == 1.
  bool singleOne(const ASTNode& n)
  {
      unsigned found = 0;
      assert(n.GetKind() == BVCONST);
      for (unsigned i = 0; i < n.GetValueWidth(); i++)
        if (CONSTANTBV::BitVector_bit_test(n.GetBVConst(),i))
          found++;
      return (found == 1);
  }


  ASTNode Rewriting::rewrite(const ASTNode& n)
  {
    if (n.Degree() == 0)
      return n;

    if (fromTo.find(n.GetNodeNum()) != fromTo.end())
      return fromTo[n.GetNodeNum()];

    ASTNode result =n;

    const ASTVec& children = n.GetChildren();
    ASTVec newChildren;
    newChildren.reserve(children.size());

    //TODO should use the copy-on-write code.

    for (auto c: children)
    {
     c = rewrite(c);

     const ASTNode start = c;

     if (
        c.GetKind() == EQ 
        && c[0].GetKind() == BVCONST 
        && c[1].GetKind() == BVPLUS  
        && c[1].Degree() == 2
        && c[1][0].GetKind() == BVCONST  
        )
     {
          // combine constants on the lhs. Note because the plus is two arity, we don't consider sharing.
          const auto width  =  c[0].GetValueWidth();
          auto lhs = nf->CreateTerm(BVUMINUS, width, c[1][0]);
          lhs = nf->CreateTerm(BVPLUS, width, lhs, c[0]);
          c = nf->CreateNode(EQ, lhs, c[1][1]);             
     }

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

     if (c.GetKind() == stp::BVCONCAT 
         && c[0].GetKind() == BVCONCAT
         && c[1].GetKind() == BVCONST 
         && c[0][1].GetKind() == BVCONST 
         )
     {
        // combine the concats with constants

          const auto width  =  c.GetValueWidth();
          const auto constants  =  nf->CreateTerm(BVCONCAT, c[0][1].GetValueWidth() + c[1].GetValueWidth() , c[0][1], c[1]);
          c = nf->CreateTerm(BVCONCAT, width, c[0][0], constants);
     }

     if (c.GetKind() == stp::BVCONCAT 
         && c[1].GetKind() == BVCONCAT
         && c[0].GetKind() == BVCONST 
         && c[1][0].GetKind() == BVCONST 
         )
     {
        // combine the concats with constants

          const auto width  =  c.GetValueWidth();
          const auto constants  =  nf->CreateTerm(BVCONCAT, c[0].GetValueWidth() + c[1][0].GetValueWidth() , c[0], c[1][0]);
          c = nf->CreateTerm(BVCONCAT, width, constants, c[1][1]);
     }

    if (c.GetKind() == BVEXTRACT
        && c[0].GetKind() == BVMULT
        && c[0].Degree() == 2
        && c[0][0].GetKind() == BVCONST 
        && singleOne(c[0][0])
         )
       {
        // Push the extract through the multiplcation when the multiplication is the same as a left shift
       
         // Position of the single one.
          unsigned position = 0;
          while (!CONSTANTBV::BitVector_bit_test(c[0][0].GetBVConst(),position))
            position++;

          const auto zero = stpMgr->CreateZeroConst(position);
          const auto concat =  nf->CreateTerm(BVCONCAT, c[0].GetValueWidth() + position, c[0][1], zero );
          c = nf->CreateTerm(BVEXTRACT, c.GetValueWidth(), concat, c[1], c[2] );
       }

      if (c.GetKind() == BVPLUS
        && c.Degree() == 2
        && c[0].GetKind() == BVCONST
        && c[1].GetKind() == ITE
        && c[1][1].GetKind() == BVCONST
        && c[1][2].GetKind() == BVCONST
        && shareCount[c.GetNodeNum()] <= 1
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
        && c[0].GetKind() == BVNOT
       )
       {
          // pull up bvnot
           const auto width = c.GetValueWidth();
           const auto extract = nf->CreateTerm(BVEXTRACT, width, c[0][0], c[1], c[2]);
           c = nf->CreateTerm(BVNOT, width, extract);
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

        for (int matching =0 ; matching < c[1][0].Degree(); matching++)
          if (c[1][0][matching] == c[0])
          {
            ASTVec others;
            for (int i =0 ; i < c[1][0].Degree(); i++)
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
      (EQ 
          7446:0b0
          14748:(BVEXTRACT 
            14712:(BVPLUS 
              14710:0xFFFFFFAB
              8816:(BVCONCAT 
                7538:0x000000
                1252:x7169))
            8110:0x0000001F
            8110:0x0000001F)))
      */
      if ( 
        c.GetKind() == EQ
        && c[0].GetKind() == BVCONST
        && c[0].GetValueWidth() ==1
        && c[1].GetKind() == BVEXTRACT
        && c[1][1].GetUnsignedConst() == c[1][0].GetValueWidth() -1
       )
       {
          if (c[0] == stpMgr->CreateZeroConst(1))
            c = nf->CreateNode(BVSGE, c[1][0], nf->CreateZeroConst(c[1][0].GetValueWidth()));
          else
            c = nf->CreateNode(BVSLT, c[1][0], nf->CreateZeroConst(c[1][0].GetValueWidth()));

       }

      /*
         (BVSGT 
          7570:0x00000000
          457798:(BVPLUS 
            7820:0xFFFFFFD7
            [457708])))
      */
      if ( 
        c.GetKind() == BVSGT
        && c[0].GetKind() == BVCONST
        && c[1].GetKind() == BVPLUS
        && c[1].Degree() ==2
        && c[1][0].GetKind() == BVCONST
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

          //std::cerr << "before" << c;
          c = nf->CreateNode(k, part1, part2);
          //std::cerr << "after" << c;
       }

          /*
          96866:(BVGT 
              71834:0x00007F73786CE05A
              96864:(BVPLUS 
                37566:0x00007F73786CE020
                96860:(BVCONCAT 
                  428:0x00000000000000
                  54:file_file_smt2_101))))
          */
       if (
          c.GetKind() == BVGT
          && c[1].GetKind() == BVPLUS 
          && c[1].Degree() == 2
          && c[0].isConstant() 
          && c[1][0].isConstant()
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
        1352830:(BVGT 
          1280904:0x00000055
          8816:(BVCONCAT 
            7538:0x000000
            1252:x7169))
      */
      if ( 
        c.GetKind() == BVGT
        && c[0].GetKind() == BVCONST
        && c[1].GetKind() == BVCONCAT
        && c[1][0].GetKind() == BVCONST
       )
       {
           auto extract = nf->CreateTerm(BVEXTRACT, 
                                              c[1][0].GetValueWidth(), 
                                              c[0], 
                                              stpMgr->CreateBVConst(32, c[0].GetValueWidth() -1), 
                                              stpMgr->CreateBVConst(32, c[1][1].GetValueWidth()));
          const auto eq = nf->CreateNode(EQ, extract, c[1][0]);
          if (eq == stpMgr->ASTTrue)
          {
           auto extract = nf->CreateTerm(BVEXTRACT, 
                                              c[1][1].GetValueWidth(), 
                                              c[0], 
                                              stpMgr->CreateBVConst(32, c[1][1].GetValueWidth() -1), 
                                              stpMgr->CreateBVConst(32, 0) );
          c = nf->CreateNode(BVGT, extract, c[1][1]);
          }
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
      if ( 
        c.GetKind() == EQ
        && c[0].GetKind() == BVCONST
        && c[0] == nf->CreateZeroConst(c[0].GetValueWidth())
        && c[1].GetKind() == BVPLUS
        && c[1].Degree() == 2
        && c[1][0].GetKind() == BVUMINUS
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
        c = nf->CreateNode(EQ, c[1][0][0], c[1][1]);
       }
      
      if ( 
        c.GetKind() == EQ
        && c[0].GetKind() == BVCONST
        && c[0] == nf->CreateZeroConst(c[0].GetValueWidth())
        && c[1].GetKind() == BVPLUS
        && c[1].Degree() == 2
        && c[1][1].GetKind() == BVUMINUS
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
        c = nf->CreateNode(EQ, c[1][1][0], c[1][0]);
       }

/*
1085202:(EQ 
    6528:0b0
    1085200:(BVAND 
    */
      if ( 
        c.GetKind() == EQ
        && c[0].GetKind() == BVCONST
        && c[0].GetValueWidth() ==1
        && c[0] == nf->CreateZeroConst(c[0].GetValueWidth())
        && c[1].GetKind() == BVAND
        && shareCount[c[1].GetNodeNum()] <= 1
       )
       {
          ASTVec children;
          for (const auto& node : c[1])
            children.push_back(nf->CreateNode(EQ, c[0],node));
          c = nf->CreateNode(OR, children);
       }
/*
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
        && c[0].GetKind()  == BVCONST
        && c[0] == nf->CreateZeroConst(c[0].GetValueWidth())

        && c[1].GetKind() == BVPLUS
        && c[1].Degree() == 2
        && c[1][0].GetKind() == ITE
        && c[1][0][1].GetKind() == BVCONST
        && c[1][0][2].GetKind() == BVCONST
        && shareCount[c[0].GetNodeNum()] <= 1
       )
       {
          const auto uminus = nf->CreateTerm(BVUMINUS, c[0].GetValueWidth(), c[1][0]);
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
  2180186:(XOR 
    363814:var_5736
    (OR 
          363815:(NOT 363814:var_5736)
          378221:(NOT 378220:var_8137))))
      */
      if ( 
        c.GetKind() == XOR
        && c.Degree() ==2
        && c[1].GetKind() == OR
        && c[1].Degree() ==2
        && c[1][0].GetKind() == NOT
        && c[1][0][0] == c[0]
        )
        {
          c = nf->CreateNode(OR, nf->CreateNode(NOT, c[1][1]), c[1][0]);
        }

       if (start != c)
       {
          c = rewrite(c);
          removed++;
       }
       // todo should probably update the sharecount.
       newChildren.push_back(c);
    }    

    if (n.GetType() == BOOLEAN_TYPE)
      result = nf->CreateNode(n.GetKind(), newChildren);
    else
      result = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(),n.GetValueWidth(), newChildren);

    fromTo.insert({n.GetNodeNum(),result});
    return result;
  }
}
