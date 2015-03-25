add_subdirectory(cryptominisat2)

set(sat_lib_to_add
    CryptoMinisat.cpp
    MinisatCore.cpp
    SimplifyingMinisat.cpp
)

if (USE_CRYPTOMINISAT4)
    set(sat_lib_to_add ${sat_lib_to_add} CryptoMinisat4.cpp)
endif()

add_library(sat OBJECT ${sat_lib_to_add})

