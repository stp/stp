add_subdirectory(cryptominisat2)

include_directories(cryptominisat2/mtl)

# FIXME: This is a mess.
#
#

add_library(minisat2 OBJECT
    simp/SimpSolver.cc
    core/Solver.cc
    core_prop/Solver_prop.cc
#    utils/Options.cc
    utils/System.cc
)

add_library(sat
    CryptoMinisat.cpp
    MinisatCore.cpp
    MinisatCore_prop.cpp
    SimplifyingMinisat.cpp
    $<TARGET_OBJECTS:minisat2>
    $<TARGET_OBJECTS:cryptominisat2>
)
