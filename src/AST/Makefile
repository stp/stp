include ../../scripts/Makefile.common

#SRCS = AST.cpp ASTKind.cpp  ASTUtil.cpp BitBlast.cpp SimpBool.cpp  ToCNF.cpp DPLLMgr.cpp ToSAT.cpp Transform.cpp
SRCS = AST.cpp ASTKind.cpp  ASTUtil.cpp BitBlast.cpp SimpBool.cpp  ToCNF.cpp ToSAT.cpp Transform.cpp AbstractionRefinement.cpp printer/AssortedPrinters.cpp printer/SMTLIBPrinter.cpp  printer/dotPrinter.cpp  printer/CPrinter.cpp printer/PLPrinter.cpp printer/LispPrinter.cpp
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -I../sat/mtl -I../sat/core

#Make the ast library for use by other modules
libast.a:	$(OBJS)
	-rm -rf $@
	$(AR) rc libast.a $(OBJS)
	$(RANLIB) libast.a

ASTKind.o:	ASTKind.kinds
	$(CXX) $(CXXFLAGS)   -c -o ASTKind.o ASTKind.cpp

# ASTKind.h and ASTKind.cpp are automatically generated
ASTKind.h ASTKind.cpp:	ASTKind.kinds genkinds.pl
	./genkinds.pl

# cnftest:	cnftest.o ToCNF.o AST.o ASTUtil.o ASTKind.o BitBlast.o AST.h
#	$(CC) $(LDFLAGS) ToCNF.o BitBlast.o ASTKind.o  ASTUtil.o AST.o  cnftest.o  -o cnftest 

# bbtest: $(OBJS)
#	$(CC) $(LDFLAGS) BitBlast.o ASTKind.o  ASTUtil.o AST.o  bbtest.o -o bbtest 

# asttest: $(OBJS)
#	$(CC) $(LDFLAGS) ASTKind.o  ASTUtil.o AST.o asttest.o  -lstdc++ -o asttest

clean:
	rm -rf *.o *~ bbtest asttest cnftest *.a  ASTKind.h ASTKind.cpp .#*
	rm -rf printer/*.o

depend:
	makedepend -Y -- $(CFLAGS) -- $(SRCS)
# DO NOT DELETE

AST.o: AST.h ../AST/ASTUtil.h ASTKind.h ../sat/core/Solver.h
AST.o: ../sat/core/SolverTypes.h   ../sat/mtl/Heap.h
AST.o: ../sat/core/SolverTypes.h 
asttest.o: AST.h ../AST/ASTUtil.h ../AST/ASTKind.h ../sat/core/Solver.h
asttest.o: ../sat/core/SolverTypes.h  
asttest.o: ../sat/mtl/Heap.h ../sat/core/SolverTypes.h 
ASTUtil.o: ASTUtil.h
bbtest.o: AST.h ../AST/ASTUtil.h ../AST/ASTKind.h ../sat/core/Solver.h
bbtest.o: ../sat/core/SolverTypes.h  
bbtest.o: ../sat/mtl/Heap.h ../sat/core/SolverTypes.h 
BitBlast.o: AST.h ../AST/ASTUtil.h ../AST/ASTKind.h ../sat/core/Solver.h
BitBlast.o: ../sat/core/SolverTypes.h  
BitBlast.o: ../sat/mtl/Heap.h ../sat/core/SolverTypes.h 
cnftest.o: AST.h ../AST/ASTUtil.h ../AST/ASTKind.h ../sat/core/Solver.h
cnftest.o: ../sat/core/SolverTypes.h  
cnftest.o: ../sat/mtl/Heap.h ../sat/core/SolverTypes.h 
ToCNF.o: AST.h ../AST/ASTUtil.h ../AST/ASTKind.h ../sat/core/Solver.h
ToCNF.o: ../sat/core/SolverTypes.h   ../sat/mtl/Heap.h
ToCNF.o: ../sat/core/SolverTypes.h 
ToSAT.o: AST.h ../AST/ASTUtil.h ../AST/ASTKind.h ../sat/core/Solver.h
ToSAT.o: ../sat/core/SolverTypes.h   ../sat/mtl/Heap.h
ToSAT.o: ../sat/core/SolverTypes.h 
Transform.o : AST.h ../AST/ASTUtil.h ../AST/ASTKind.h
#DPLLMgr.o: AST.h ../AST/ASTUtil.h ../AST/ASTKind.h ../sat/core/Solver.h
#DPLLMgr.o: ../sat/core/SolverTypes.h   ../sat/mtl/Heap.h
#DPLLMgr.o: ../sat/core/SolverTypes.h 
