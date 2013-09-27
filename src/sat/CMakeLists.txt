add_subdirectory(cryptominisat2)

include_directories(cryptominisat2/mtl)

# FIXME: This is a mess.
#
#

add_library(minisat2
    simp/SimpSolver.cc
    core/Solver.cc
    core_prop/Solver_prop.cc
    utils/System.cc
)

add_library(sat
    CryptoMinisat.cpp
    MinisatCore.cpp
    MinisatCore_prop.cpp
    SimplifyingMinisat.cpp
)
