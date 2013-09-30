#add_custom_target(ASTKind_header ALL DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/ASTKind.h)
include_directories(${CMAKE_CURRENT_SOURCE_DIR})
#http://www.eecs.berkeley.edu/~alanmi/abc/

add_library(abc OBJECT
    aig/aig/aigCheck.c
    aig/aig/aigDfs.c
    aig/aig/aigFanout.c
    aig/aig/aigMan.c
    aig/aig/aigMem.c
    aig/aig/aigMffc.c
    aig/aig/aigObj.c
    aig/aig/aigOper.c
    aig/aig/aigOrder.c
    aig/aig/aigPart.c
    aig/aig/aigRepr.c
    aig/aig/aigRet.c
    aig/aig/aigScl.c
    aig/aig/aigSeq.c
    aig/aig/aigShow.c
    aig/aig/aigTable.c
    aig/aig/aigTime.c
    aig/aig/aigTiming.c
    aig/aig/aigTruth.c
    aig/aig/aigTsim.c
    aig/aig/aigUtil.c
    aig/aig/aigWin.c

    aig/cnf/cnfCore.c
    aig/cnf/cnfCut.c
    aig/cnf/cnfData.c
    aig/cnf/cnfMan.c
    aig/cnf/cnfMap.c
    aig/cnf/cnfPost.c
    aig/cnf/cnfUtil.c
    aig/cnf/cnfWrite.c

    aig/dar/darBalance.c
    aig/dar/darCore.c
    aig/dar/darCut.c
    aig/dar/darData.c
    aig/dar/darLib.c
    aig/dar/darMan.c
    aig/dar/darPrec.c
    aig/dar/darRefact.c
    aig/dar/darScript.c

    aig/kit/kitAig.c
    aig/kit/kitGraph.c
    aig/kit/kitIsop.c
    aig/kit/kitSop.c
    aig/kit/kitTruth.c
)

#add_dependencies(AST ASTKind_header)
