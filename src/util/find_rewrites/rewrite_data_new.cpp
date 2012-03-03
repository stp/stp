if (n.GetKind() == BVPLUS )
{
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVUMINUS,width,n[1][0]));//107 -> 107 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[1].GetKind() == BVOR && n[1].Degree() ==2 && n[1][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(SBVMOD,width,n[1][1],children[1][0])));//33 -> 33 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[1].GetKind() == BVPLUS && n[1].Degree() ==2 )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVPLUS,width,bm->CreateTerm(BVNEG,width,n[1][0]),bm->CreateTerm(BVNEG,width,n[1][1]))));//233 -> 176 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[1].GetKind() == BVSX && n[1][0].GetKind() == BVEXTRACT && n[1][0][1] == bm->CreateBVConst(32, width-1) && n[1][0][2] == bm->CreateBVConst(32, width-1) && n[1][1] == bm->CreateBVConst(32, width) )    set(result,  bm->CreateTerm(BVCONCAT,width,bm->CreateTerm(BVSX,width-1,bm->CreateBVConst(2,0)),bm->CreateTerm(BVNEG,width,children[1][0])));//21 -> 21 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[1].GetKind() == BVXOR && n[1].Degree() ==2 && n[1][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(BVUMINUS,width,bm->CreateTerm(BVXOR,width,one,n[1][1])));//107 -> 107 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[1].GetKind() == SBVMOD && n[1][1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVOR,width,children[1][1],n[1][0])));//21 -> 21 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1)))    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVPLUS,width,bm->CreateTerm(BVNEG,width,n[1]),bm->CreateTerm(BVNEG,width,n[2]))));//237 -> 176 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7))&& n[1].GetKind() == BVMULT && n[1].Degree() ==2 && n[1][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,2)))    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVMULT,width,bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)),n[1][1])));//99 -> 99 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7))&& n[1].GetKind() == BVMULT && n[1].Degree() ==2 && n[1][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVMULT,width,bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,2)),n[1][1])));//121 -> 45 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7))&& n[1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVPLUS,width,one,n[1][0])));//107 -> 107 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7))&& n[1].GetKind() == SBVMOD && n[1][1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(BVOR,width,children[1][1],bm->CreateTerm(BVNEG,width,n[1][0])));//21 -> 21 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0].GetKind() == BVNEG && n[1].GetKind() == BVUMINUS )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVPLUS,width,n[0][0],n[1][0])));//237 -> 176 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[0].GetKind() == BVUMINUS && n[1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVPLUS,width,n[0][0],n[1][0])));//237 -> 176 | 0 ms
if ( width >= 3 && n.GetKind() == BVPLUS && n.Degree() ==2 && n[1].GetKind() == BVUMINUS )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVPLUS,width,n[1][0],bm->CreateTerm(BVNEG,width,n[0]))));//237 -> 176 | 0 ms
}
if (n.GetKind() == BVSRSHIFT )
{
if ( width >= 3 && n.GetKind() == BVSRSHIFT && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6))&& n[1].GetKind() == BVUMINUS )    set(result,  bm->CreateTerm(BVSRSHIFT,width,children[0],n[1][0]));//66 -> 36 | 0 ms
if ( width >= 3 && n.GetKind() == BVSRSHIFT && n[0].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVSRSHIFT,width,n[0][0],n[1])));//224 -> 224 | 0 ms
if ( width >= 3 && n.GetKind() == BVSRSHIFT && n[1].GetKind() == BVNEG && n[1][0] == n[0] )    set(result,  bm->CreateTerm(BVSX,width,bm->CreateTerm(BVEXTRACT,width-1 +1 - (width-1),n[0],bm->CreateBVConst(32,width-1),bm->CreateBVConst(32,width-1)), bm->CreateBVConst(32, width )));//216 -> 33 | 0 ms
}
if (n.GetKind() == BVCONCAT )
{
if ( width >= 3 && n.GetKind() == BVCONCAT && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,0))&& n[1].GetKind() == BVEXTRACT && n[1][1] == bm->CreateZeroConst(32) && n[1][2] == bm->CreateZeroConst(32) )    set(result,  bm->CreateTerm(BVUMINUS,width,bm->CreateTerm(SBVMOD,width,n[1][0],bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))));//21 -> 21 | 0 ms
if ( width >= 3 && n.GetKind() == BVCONCAT && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,0))&& n[1].GetKind() == BVNEG && n[1][0].GetKind() == BVEXTRACT && n[1][0][1] == bm->CreateZeroConst(32) && n[1][0][2] == bm->CreateZeroConst(32) )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVOR,width,bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)),n[1][0][0])));//21 -> 21 | 0 ms
if ( width >= 3 && n.GetKind() == BVCONCAT && n[0].GetKind() == BVNEG && n[0][0].GetKind() == BVEXTRACT && n[0][0][1] == bm->CreateBVConst(32, width-1) && n[0][0][2] == bm->CreateOneConst(32) && n[1] == bm->CreateZeroConst(1) )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVOR,width,one,n[0][0][0])));//45 -> 45 | 0 ms
}
if (n.GetKind() == ITE )
{
if ( width >= 3 && n.GetKind() == ITE && n[0].GetKind() == EQ && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,0))&& n[1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[2] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,0)))    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVSRSHIFT,width,bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)),n[0][1])));//36 -> 36 | 0 ms
if ( width >= 3 && n.GetKind() == ITE && n[0].GetKind() == EQ && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,0))&& n[1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6))&& n[2] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7)))    set(result,  bm->CreateTerm(BVSRSHIFT,width,children[1],n[0][1]));//36 -> 36 | 0 ms
if ( width >= 3 && n.GetKind() == ITE && n[0].GetKind() == EQ && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7))&& n[1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[2] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,0)))    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVSRSHIFT,width,bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)),bm->CreateTerm(BVNEG,width,n[0][1]))));//36 -> 36 | 0 ms
if ( width >= 3 && n.GetKind() == ITE && n[0].GetKind() == EQ && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7))&& n[1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6))&& n[2] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7)))    set(result,  bm->CreateTerm(BVSRSHIFT,width,children[1],bm->CreateTerm(BVNEG,width,n[0][1])));//36 -> 36 | 0 ms
}
if (n.GetKind() == BVDIV )
{
if ( width >= 3 && n.GetKind() == BVDIV && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1)))    set(result,  bm->CreateTerm(ITE,width,bm->CreateNode(BVGT,bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)),bm->CreateTerm(BVNEG,width,n[1])),zero,one));//51 -> 35 | 0 ms
}
if (n.GetKind() == SBVDIV )
{
if ( width >= 3 && n.GetKind() == SBVDIV && n[0].GetKind() == BVNEG && n[1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,0)))    set(result,  bm->CreateTerm(BVUMINUS,width,bm->CreateTerm(SBVDIV,width,n[0][0],zero)));//33 -> 33 | 0 ms
}
if (n.GetKind() == BVMOD )
{
if ( width >= 3 && n.GetKind() == BVMOD && n[0].GetKind() == BVUMINUS && n[1].GetKind() == BVNEG && n[1][0] == n[0][0] )    set(result,  bm->CreateTerm(SBVREM,width,one,children[1]));//80 -> 80 | 0 ms
}
if (n.GetKind() == SBVMOD )
{
if ( width >= 3 && n.GetKind() == SBVMOD && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVUMINUS,width,bm->CreateTerm(SBVREM,width,n[1][0],children[1])));//187 -> 187 | 0 ms
if ( width >= 3 && n.GetKind() == SBVMOD && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7)))    set(result,  bm->CreateTerm(SBVMOD,width,bm->CreateTerm(BVNEG,width,n[1]),n[1]));//204 -> 204 | 0 ms
if ( width >= 3 && n.GetKind() == SBVMOD && n[0].GetKind() == BVPLUS && n[0].Degree() ==2 && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7))&& n[1].GetKind() == BVUMINUS && n[1][0] == n[0][1] )    set(result,  bm->CreateTerm(SBVMOD,width,bm->CreateTerm(BVNEG,width,n[0][1]),children[1]));//1848 -> 272 | 0 ms
if ( width >= 3 && n.GetKind() == SBVMOD && n[0].GetKind() == BVUMINUS && n[1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(SBVMOD,width,n[0][0],children[1]));//33 -> 33 | 0 ms
}
if (n.GetKind() == BVAND )
{
if ( width >= 3 && n.GetKind() == BVAND && n.Degree() ==2 && n[0].GetKind() == BVNEG && n[1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVOR,width,n[0][0],n[1][0])));//79 -> 79 | 0 ms
}
if (n.GetKind() == BVUMINUS )
{
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == BVOR && n[0].Degree() ==2 && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1)))    set(result,  bm->CreateTerm(BVOR,width,one,bm->CreateTerm(BVNEG,width,n[0][1])));//45 -> 45 | 0 ms
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == BVXOR && n[0].Degree() ==2 && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(BVPLUS,width,one,bm->CreateTerm(BVXOR,width,one,n[0][1])));//107 -> 107 | 0 ms
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == ITE && n[0][0].GetKind() == BVGT && n[0][0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6))&& n[0][1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,0))&& n[0][2] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1)))    set(result,  bm->CreateTerm(ITE,width,children[0][0],zero,max));//47 -> 47 | 0 ms
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == SBVDIV && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1)))    set(result,  bm->CreateTerm(SBVDIV,width,max,n[0][1]));//155 -> 155 | 0 ms
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == SBVDIV && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7)))    set(result,  bm->CreateTerm(SBVDIV,width,one,n[0][1]));//155 -> 155 | 0 ms
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == SBVMOD && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1)))    set(result,  bm->CreateTerm(SBVREM,width,bm->CreateTerm(BVNEG,width,n[0][1]),n[0][1]));//244 -> 244 | 0 ms
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == SBVMOD && n[0][0].GetKind() == BVNEG && n[0][1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVOR,width,children[0][1],n[0][0][0])));//21 -> 21 | 0 ms
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == SBVREM && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1)))    set(result,  bm->CreateTerm(SBVREM,width,max,n[0][1]));//92 -> 92 | 0 ms
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == SBVREM && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7)))    set(result,  bm->CreateTerm(SBVREM,width,one,n[0][1]));//80 -> 80 | 0 ms
if ( width >= 3 && n.GetKind() == BVUMINUS && n[0].GetKind() == SBVREM && n[0][0].GetKind() == BVNEG && n[0][1] == n[0][0][0] )    set(result,  bm->CreateTerm(SBVMOD,width,one,n[0][0][0]));//187 -> 187 | 0 ms
}
if (n.GetKind() == SBVREM )
{
if ( width >= 3 && n.GetKind() == SBVREM && n[0].GetKind() == BVUMINUS && n[1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(BVUMINUS,width,bm->CreateTerm(SBVREM,width,n[0][0],children[1])));//55 -> 39 | 0 ms
}
if (n.GetKind() == BVNEG )
{
if ( width >= 3 && n.GetKind() == BVNEG && n[0].GetKind() == BVAND && n[0].Degree() ==2 && n[0][1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVOR,width,n[0][1][0],bm->CreateTerm(BVNEG,width,n[0][0])));//79 -> 79 | 0 ms
if ( width >= 3 && n.GetKind() == BVNEG && n[0].GetKind() == BVCONCAT && n[0][0].GetKind() == BVEXTRACT && n[0][0][1] == bm->CreateBVConst(32, width-1) && n[0][0][2] == bm->CreateOneConst(32) && n[0][1] == bm->CreateZeroConst(1) )    set(result,  bm->CreateTerm(BVUMINUS,width,bm->CreateTerm(BVOR,width,one,n[0][0][0])));//45 -> 45 | 0 ms
if ( width >= 3 && n.GetKind() == BVNEG && n[0].GetKind() == BVMULT && n[0].Degree() ==2 && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,2))&& n[0][1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVPLUS,width,one,bm->CreateTerm(BVMULT,width,children[0][0],n[0][1][0])));//45 -> 45 | 0 ms
if ( width >= 3 && n.GetKind() == BVNEG && n[0].GetKind() == BVOR && n[0].Degree() ==2 && n[0][1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVAND,width,n[0][1][0],bm->CreateTerm(BVNEG,width,n[0][0])));//79 -> 79 | 0 ms
if ( width >= 3 && n.GetKind() == BVNEG && n[0].GetKind() == BVPLUS && n[0].Degree() ==2 && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6))&& n[0][1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVPLUS,width,bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,2)),n[0][1][0]));//103 -> 103 | 0 ms
if ( width >= 3 && n.GetKind() == BVNEG && n[0].GetKind() == BVXOR && n[0].Degree() ==2 && n[0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(BVXOR,width,one,n[0][1]));//49 -> 49 | 0 ms
if ( width >= 3 && n.GetKind() == BVNEG && n[0].GetKind() == BVXOR && n[0].Degree() ==2 )    set(result,  bm->CreateTerm(BVXOR,width,n[0][0],bm->CreateTerm(BVNEG,width,n[0][1])));//89 -> 89 | 0 ms
if ( width >= 3 && n.GetKind() == BVNEG && n[0].GetKind() == ITE && n[0][0].GetKind() == BVGT && n[0][0][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6))&& n[0][1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,0))&& n[0][2] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1)))    set(result,  bm->CreateTerm(ITE,width,children[0][0],max,children[0][0][0]));//35 -> 35 | 0 ms
if ( width >= 3 && n.GetKind() == BVNEG && n[0].GetKind() == SBVMOD && n[0][1] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)))    set(result,  bm->CreateTerm(SBVMOD,width,bm->CreateTerm(BVNEG,width,n[0][0]),children[0][1]));//33 -> 33 | 0 ms
}
if (n.GetKind() == BVXOR )
{
if ( width >= 3 && n.GetKind() == BVXOR && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,1))&& n[1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVXOR,width,bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6)),n[1][0]));//49 -> 49 | 0 ms
if ( width >= 3 && n.GetKind() == BVXOR && n.Degree() ==2 && n[0].GetKind() == BVNEG && n[1].GetKind() == BVPLUS && n[1].Degree() ==2 && n[1][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7)))    set(result,  bm->CreateTerm(BVXOR,width,n[0][0],bm->CreateTerm(BVUMINUS,width,n[1][1])));//150 -> 150 | 0 ms
if ( width >= 3 && n.GetKind() == BVXOR && n.Degree() ==2 && n[0].GetKind() == BVNEG && n[1].GetKind() == BVUMINUS )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVXOR,width,n[0][0],children[1])));//150 -> 150 | 0 ms
if ( width >= 3 && n.GetKind() == BVXOR && n.Degree() ==2 && n[0].GetKind() == BVUMINUS && n[1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVXOR,width,n[1][0],children[0])));//150 -> 150 | 0 ms
if ( width >= 3 && n.GetKind() == BVXOR && n.Degree() ==2 && n[1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVXOR,width,n[1][0],n[0])));//89 -> 89 | 0 ms
if ( width >= 3 && n.GetKind() == BVXOR && n.Degree() ==2 && n[1].GetKind() == BVPLUS && n[1].Degree() ==2 && n[1][0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,7)))    set(result,  bm->CreateTerm(BVXOR,width,bm->CreateTerm(BVNEG,width,n[0]),bm->CreateTerm(BVUMINUS,width,n[1][1])));//150 -> 150 | 0 ms
}
if (n.GetKind() == BVOR )
{
if ( width >= 3 && n.GetKind() == BVOR && n.Degree() ==2 && n[0] == bm->CreateTerm(BVSX,width,bm->CreateBVConst(3,6))&& n[1].GetKind() == BVUMINUS )    set(result,  bm->CreateTerm(BVOR,width,children[0],n[1][0]));//21 -> 21 | 0 ms
if ( width >= 3 && n.GetKind() == BVOR && n.Degree() ==2 && n[0].GetKind() == BVNEG && n[1].GetKind() == BVNEG )    set(result,  bm->CreateTerm(BVNEG,width,bm->CreateTerm(BVAND,width,n[0][0],n[1][0])));//79 -> 79 | 0 ms
}
