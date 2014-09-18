add_subdirectory(cryptominisat2)
add_subdirectory(minisat)

set(sat_lib_to_add
    CryptoMinisat.cpp
    MinisatCore.cpp
    MinisatCore_prop.cpp
    SimplifyingMinisat.cpp
)

if (USE_CRYPTOMINISAT4)
    set(sat_lib_to_add ${sat_lib_to_add} CryptoMinisat4.cpp)
endif()

add_library(sat OBJECT ${sat_lib_to_add})

