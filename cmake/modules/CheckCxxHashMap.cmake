# -----------------------------------------------------------------------------
# Determines which header contains the C++ hash_map aka unordered_map, and sets
# the variables HASH_MAP_H, HASH_MAP_CLASS, and HASH_MAP_NAMESPACE accordingly.
#
# This file closely mirrors CheckCxxHashSet.cmake, so be sure to update both.
# -----------------------------------------------------------------------------

macro(check_cxx_hashmap)
  message(STATUS "Checking for C++ hash_map implementation...")

  check_std_unordered_map()
  if(NOT HASH_MAP_H)
    check_tr1_unordered_map()
  endif()
  if(NOT HASH_MAP_H)
    check_gnu_ext_hash_map()
  endif()
  if(NOT HASH_MAP_H)
    check_std_ext_hash_map()
  endif()
  if(NOT HASH_MAP_H)
    check_global_hash_map()
  endif()

  if(HASH_MAP_H)
    message(STATUS "C++ hash_map found as ${HASH_MAP_NAMESPACE}::${HASH_MAP_CLASS} in ${HASH_MAP_H}")
  else()
    message(FATAL_ERROR "C++ hash_map not found")
  endif()
endmacro()

# -----------------------------------------------------------------------------

include(CheckCXXSourceCompiles)

macro(check_std_unordered_map)
  check_cxx_source_compiles("
    #include <unordered_map>
    int main() {
      std::unordered_map<int, int> t;
    }"
    HAVE_HASH_MAP_STD
  )

  if(HAVE_HASH_MAP_STD)
    set(HASH_MAP_H "<unordered_map>")
    set(HASH_MAP_CLASS "unordered_map")
    set(HASH_MAP_NAMESPACE "std")
  endif()
endmacro()

macro(check_tr1_unordered_map)
  check_cxx_source_compiles("
    #include <tr1/unordered_map>
    int main() {
      std::tr1::unordered_map<int, int> t;
    }"
    HAVE_HASH_MAP_TR1
  )

  if(HAVE_HASH_MAP_TR1)
    set(HASH_MAP_H "<tr1/unordered_map>")
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
    HAVE_HASH_MAP_GNU_EXT
  )

  if(HAVE_HASH_MAP_GNU_EXT)
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
    HAVE_HASH_MAP_STD_EXT
  )

  if(HAVE_HASH_MAP_STD_EXT)
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
    HAVE_HASH_MAP_GLOBAL
  )

  if(HAVE_HASH_MAP_GLOBAL)
    set(HASH_MAP_H "<ext/hash_map>")
    set(HASH_MAP_CLASS "hash_map")
    set(HASH_MAP_NAMESPACE "")
  endif()
endmacro()
