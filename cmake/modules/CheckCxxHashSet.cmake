# -----------------------------------------------------------------------------
# Determines which header contains the C++ hash_set aka unordered_set, and sets
# the variables HASH_SET_H, HASH_SET_CLASS, and HASH_SET_NAMESPACE accordingly.
#
# This file closely mirrors CheckCxxHashMap.cmake, so be sure to update both.
# -----------------------------------------------------------------------------

set(HAVE_HASH_SET )

macro(check_cxx_hashset)
  message(STATUS "Checking for C++ hash_set implementation...")

  check_std_unordered_set()
  if(NOT HAVE_HASH_SET)
    check_tr1_unordered_set()
  endif()
  if(NOT HAVE_HASH_SET)
    check_gnu_ext_hash_set()
  endif()
  if(NOT HAVE_HASH_SET)
    check_std_ext_hash_set()
  endif()
  if(NOT HAVE_HASH_SET)
    check_global_hash_set()
  endif()

  if(HAVE_HASH_SET)
    message(STATUS "C++ hash_set found as ${HASH_SET_NAMESPACE}::${HASH_SET_CLASS} in ${HASH_SET_H}")
  else()
    message(FATAL_ERROR "C++ hash_set not found")
  endif()
endmacro()

# -----------------------------------------------------------------------------

include(CheckCXXSourceCompiles)

macro(check_std_unordered_set)
  set(CMAKE_REQUIRED_FLAGS "-std=c++0x")
  check_cxx_source_compiles("
    #include <unordered_set>
    int main() {
      std::unordered_set<int> t;
    }"
    HAVE_HASH_SET
  )
  unset(CMAKE_REQUIRED_FLAGS)

  if(HAVE_HASH_SET)
    set(HASH_SET_H "<unordered_set>")
    set(HASH_SET_CLASS "unordered_set")
    set(HASH_SET_NAMESPACE "std")
  endif()
endmacro()

macro(check_tr1_unordered_set)
  set(CMAKE_REQUIRED_FLAGS "-std=c++0x")
  check_cxx_source_compiles("
    #include <tr1/unordered_set>
    int main() {
      std::tr1::unordered_set<int> t;
    }"
    HAVE_HASH_SET
  )
  unset(CMAKE_REQUIRED_FLAGS)

  if(HAVE_HASH_SET)
    set(HASH_SET_H "<tr/unordered_set>")
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
    HAVE_HASH_SET
  )

  if(HAVE_HASH_SET)
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
    HAVE_HASH_SET
  )

  if(HAVE_HASH_SET)
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
    HAVE_HASH_SET
  )

  if(HAVE_HASH_SET)
    set(HASH_SET_H "<ext/hash_set>")
    set(HASH_SET_CLASS "hash_set")
    set(HASH_SET_NAMESPACE "")
  endif()
endmacro()
