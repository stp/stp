# -----------------------------------------------------------------------------
# Determines which header contains the C++ hash_set aka unordered_set, and sets
# the variables HASH_SET_H, HASH_SET_CLASS, and HASH_SET_NAMESPACE accordingly.
#
# This file closely mirrors CheckCxxHashMap.cmake, so be sure to update both.
# -----------------------------------------------------------------------------

macro(check_cxx_hashset)
  message(STATUS "Checking for C++ hash_set implementation...")

  check_std_unordered_set()
  if(NOT HASH_SET_H)
    check_tr1_unordered_set()
  endif()
  if(NOT HASH_SET_H)
    check_gnu_ext_hash_set()
  endif()
  if(NOT HASH_SET_H)
    check_std_ext_hash_set()
  endif()
  if(NOT HASH_SET_H)
    check_global_hash_set()
  endif()

  if(HASH_SET_H)
    message(STATUS "C++ hash_set found as ${HASH_SET_NAMESPACE}::${HASH_SET_CLASS} in ${HASH_SET_H}")
  else()
    message(FATAL_ERROR "C++ hash_set not found")
  endif()
endmacro()

# -----------------------------------------------------------------------------

include(CheckCXXSourceCompiles)

macro(check_std_unordered_set)
  check_cxx_source_compiles("
    #include <unordered_set>
    int main() {
      std::unordered_set<int> t;
    }"
    HAVE_HASH_SET_STD
  )

  if(HAVE_HASH_SET_STD)
    set(HASH_SET_H "<unordered_set>")
    set(HASH_SET_CLASS "unordered_set")
    set(HASH_SET_NAMESPACE "std")
  endif()
endmacro()

macro(check_tr1_unordered_set)
  check_cxx_source_compiles("
    #include <tr1/unordered_set>
    int main() {
      std::tr1::unordered_set<int> t;
    }"
    HAVE_HASH_SET_TR1
  )

  if(HAVE_HASH_SET_TR1)
    set(HASH_SET_H "<tr1/unordered_set>")
    set(HASH_SET_CLASS "unordered_set")
    set(HASH_SET_NAMESPACE "std::tr1")
  endif()
endmacro()

macro(check_gnu_ext_hash_set)
  check_cxx_source_compiles("
    #include <ext/hash_set>
    int main() {
      __gnu_cxx::hash_set<int> t;
    }"
    HAVE_HASH_SET_GNU_EXT
  )

  if(HAVE_HASH_SET_GNU_EXT)
    set(HASH_SET_H "<ext/hash_set>")
    set(HASH_SET_CLASS "hash_set")
    set(HASH_SET_NAMESPACE "__gnu_cxx")
  endif()
endmacro()

macro(check_std_ext_hash_set)
  check_cxx_source_compiles("
    #include <ext/hash_set>
    int main() {
      std::hash_set<int> t;
    }"
    HAVE_HASH_SET_STD_EXT
  )

  if(HAVE_HASH_SET_STD_EXT)
    set(HASH_SET_H "<ext/hash_set>")
    set(HASH_SET_CLASS "hash_set")
    set(HASH_SET_NAMESPACE "std")
  endif()
endmacro()

macro(check_global_hash_set)
  check_cxx_source_compiles("
    #include <ext/hash_set>
    int main() {
      hash_set<int> t;
    }"
    HAVE_HASH_SET_GLOBAL
  )

  if(HAVE_HASH_SET_GLOBAL)
    set(HASH_SET_H "<ext/hash_set>")
    set(HASH_SET_CLASS "hash_set")
    set(HASH_SET_NAMESPACE "")
  endif()
endmacro()
