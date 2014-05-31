add_subdirectory(cryptominisat2)
add_subdirectory(minisat)
add_subdirectory(cryptominisat4)

add_library(sat OBJECT
    CryptoMinisat.cpp
    CryptoMinisat4.cpp
    MinisatCore.cpp
    MinisatCore_prop.cpp
    SimplifyingMinisat.cpp
)

