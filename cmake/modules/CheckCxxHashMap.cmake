# -----------------------------------------------------------------------------
# Determines which header contains the C++ hash_map aka unordered_map, and sets
# the variables HASH_MAP_H, HASH_MAP_CLASS, and HASH_MAP_NAMESPACE accordingly.
#
# This file closely mirrors CheckCxxHashSet.cmake, so be sure to update both.
# -----------------------------------------------------------------------------

set(HAVE_HASH_MAP )

macro(check_cxx_hashmap)
  message(STATUS "Checking for C++ hash_map implementation...")
  
  check_std_unordered_map()
  if(NOT HAVE_HASH_MAP)
    check_tr1_unordered_map()
  endif()
  if(NOT HAVE_HASH_MAP)
    check_gnu_ext_hash_map()
  endif()
  if(NOT HAVE_HASH_MAP)
    check_std_ext_hash_map()
  endif()
  if(NOT HAVE_HASH_MAP)
    check_global_hash_map()
  endif()
  
  if(HAVE_HASH_MAP)
    message(STATUS "C++ hash_map found as ${HASH_MAP_NAMESPACE}::${HASH_MAP_CLASS} in ${HASH_MAP_H}")
  else()
    message(FATAL_ERROR "C++ hash_map not found")
  endif()
endmacro()

# -----------------------------------------------------------------------------

include(CheckCXXSourceCompiles)

macro(check_std_unordered_map)
  set(CMAKE_REQURED_FLAGS "-std=c++0x")
  check_cxx_source_compiles("
    #include <unordered_map>
    int main() {
      std::unordered_map<int, int> t;
    }"
    HAVE_HASH_MAP
  )
  set(CMAKE_REQUIRED_FLAGS )
  
  if(HAVE_HASH_MAP)
    set(HASH_MAP_H "<unordered_map>")
    set(HASH_MAP_CLASS "unordered_map")
    set(HASH_MAP_NAMESPACE "std")
  endif()
endmacro()

macro(check_tr1_unordered_map)
  set(CMAKE_REQURED_FLAGS "-std=c++0x")
  check_cxx_source_compiles("
    #include <tr1/unordered_map>
    int main() {
      std::tr1::unordered_map<int, int> t;
    }"
    HAVE_HASH_MAP
  )
  set(CMAKE_REQUIRED_FLAGS )
  
  if(HAVE_HASH_MAP)
    set(HASH_MAP_H "<tr/unordered_map>")
    set(HASH_MAP_CLASS "unordered_map")
    set(HASH_MAP_NAMESPACE "std::tr1")
  endif()
endmacro()

macro(check_gnu_ext_hash_map)
  check_cxx_source_compiles("
    #include <ext/hash_map>
    int main() {
      __gnu_cxx::hash_map<int, int> t;
    }"
    HAVE_HASH_MAP
  )
  
  if(HAVE_HASH_MAP)
    set(HASH_MAP_H "<ext/hash_map>")
    set(HASH_MAP_CLASS "hash_map")
    set(HASH_MAP_NAMESPACE "__gnu_cxx")
  endif()
endmacro()

macro(check_std_ext_hash_map)
  check_cxx_source_compiles("
    #include <ext/hash_map>
    int main() {
      std::hash_map<int, int> t;
    }"
    HAVE_HASH_MAP
  )
  
  if(HAVE_HASH_MAP)
    set(HASH_MAP_H "<ext/hash_map>")
    set(HASH_MAP_CLASS "hash_map")
    set(HASH_MAP_NAMESPACE "std")
  endif()
endmacro()

macro(check_global_hash_map)
  check_cxx_source_compiles("
    #include <ext/hash_map>
    int main() {
      hash_map<int, int> t;
    }"
    HAVE_HASH_MAP
  )
  
  if(HAVE_HASH_MAP)
    set(HASH_MAP_H "<ext/hash_map>")
    set(HASH_MAP_CLASS "hash_map")
    set(HASH_MAP_NAMESPACE "")
  endif()
endmacro()
