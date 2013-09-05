add_subdirectory(cryptominisat2)

include_directories(cryptominisat2/mtl)

add_library(minisat2
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
)

target_link_libraries(sat
#     core/lib_release.a
#     core_prop/lib_release.a
#     simp/lib_release.a
#     utils/lib_release.a
    cryptominisat2
    minisat2
)
#add_dependencies(simplifier ASTKind_header)