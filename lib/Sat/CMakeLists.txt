add_subdirectory(cryptominisat2)

set(sat_lib_to_add
    CryptoMinisat.cpp
    MinisatCore.cpp
    SimplifyingMinisat.cpp
)

if(HAVE_FLAG_CPP03 AND HAVE_FLAG_STD_CPP11)
  set_source_files_properties(MinisatCore.cpp PROPERTIES COMPILE_FLAGS -std=c++03)
  set_source_files_properties(SimplifyingMinisat.cpp PROPERTIES COMPILE_FLAGS -std=c++03)
endif()

if (USE_CRYPTOMINISAT4)
    set(sat_lib_to_add ${sat_lib_to_add} CryptoMinisat4.cpp)
endif()

add_library(sat OBJECT ${sat_lib_to_add})

