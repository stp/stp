add_subdirectory(cryptominisat2)
add_subdirectory(minisat)

add_library(sat OBJECT
    CryptoMinisat.cpp
    MinisatCore.cpp
    MinisatCore_prop.cpp
    SimplifyingMinisat.cpp
)

