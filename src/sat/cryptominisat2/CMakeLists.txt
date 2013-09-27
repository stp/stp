include_directories(mtl)
include_directories(MTRand)

add_library(cryptominisat2 OBJECT
ClauseAllocator.cpp
ClauseCleaner.cpp
FailedVarSearcher.cpp
FindUndef.cpp
Gaussian.cpp
Logger.cpp
MatrixFinder.cpp
OnlyNonLearntBins.cpp
PackedRow.cpp
PartFinder.cpp
PartHandler.cpp
RestartTypeChooser.cpp
Solver.cpp
StateSaver.cpp
Subsumer.cpp
UselessBinRemover.cpp
VarReplacer.cpp
XorFinder.cpp
XorSubsumer.cpp
)

# Gross: Don't link dynamic library with static
# or link static with static
#target_link_libraries(cryptominisat2
#    ${Boost_LIBRARIES}
#)
