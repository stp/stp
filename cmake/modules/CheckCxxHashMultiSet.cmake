# -----------------------------------------------------------------------------
# Determines which header contains the C++ hash_multiset aka unordered_multiset
# and sets the variables HASH_MULTISET_H, HASH_MULTISET_CLASS, and
# HASH_MULTISET_NAMESPACE accordingly.
#
# This file closely mirrors CheckCxxHashMap.cmake, so be sure to update both.
# -----------------------------------------------------------------------------

macro(check_cxx_hashmultiset)
  message(STATUS "Checking for C++ hash_multiset implementation...")

  check_std_unordered_multiset()
  if(NOT HASH_MULTISET_H)
    check_tr1_unordered_multiset()
  endif()
  if(NOT HASH_MULTISET_H)
    check_gnu_ext_hash_multiset()
  endif()
  if(NOT HASH_MULTISET_H)
    check_std_ext_hash_multiset()
  endif()
  if(NOT HASH_MULTISET_H)
    check_global_hash_multiset()
  endif()

  if(HASH_MULTISET_H)
    message(STATUS "C++ hash_multiset found as ${HASH_MULTISET_NAMESPACE}::${HASH_MULTISET_CLASS} in ${HASH_MULTISET_H}")
  else()
    message(FATAL_ERROR "C++ hash_multiset not found")
  endif()
endmacro()

# -----------------------------------------------------------------------------

include(CheckCXXSourceCompiles)

macro(check_std_unordered_multiset)
  check_cxx_source_compiles("
    #include <unordered_set>
    int main() {
      std::unordered_multiset<int> t;
    }"
    HAVE_HASH_MULTISET_STD
  )

  if(HAVE_HASH_MULTISET_STD)
    set(HASH_MULTISET_H "<unordered_set>")
    set(HASH_MULTISET_CLASS "unordered_multiset")
    set(HASH_MULTISET_NAMESPACE "std")
  endif()
endmacro()

macro(check_tr1_unordered_multiset)
  check_cxx_source_compiles("
    #include <tr1/unordered_set>
    int main() {
      std::tr1::unordered_multiset<int> t;
    }"
    HAVE_HASH_MULTISET_TR1
  )

  if(HAVE_HASH_MULTISET_TR1)
    set(HASH_MULTISET_H "<tr1/unordered_set>")
    set(HASH_MULTISET_CLASS "unordered_multiset")
    set(HASH_MULTISET_NAMESPACE "std::tr1")
  endif()
endmacro()

macro(check_gnu_ext_hash_multiset)
  check_cxx_source_compiles("
    #include <ext/hash_set>
    int main() {
      __gnu_cxx::hash_multiset<int> t;
    }"
    HAVE_HASH_MULTISET_GNU_EXT
  )

  if(HAVE_HASH_MULTISET_GNU_EXT)
    set(HASH_MULTISET_H "<ext/hash_set>")
    set(HASH_MULTISET_CLASS "hash_multiset")
    set(HASH_MULTISET_NAMESPACE "__gnu_cxx")
  endif()
endmacro()

macro(check_std_ext_hash_multiset)
  check_cxx_source_compiles("
    #include <ext/hash_set>
    int main() {
      std::hash_multiset<int> t;
    }"
    HAVE_HASH_MULTISET_STD_EXT
  )

  if(HAVE_HASH_MULTISET_STD_EXT)
    set(HASH_MULTISET_H "<ext/hash_set>")
    set(HASH_MULTISET_CLASS "hash_multiset")
    set(HASH_MULTISET_NAMESPACE "std")
  endif()
endmacro()

macro(check_global_hash_multiset)
  check_cxx_source_compiles("
    #include <ext/hash_set>
    int main() {
      hash_multiset<int> t;
    }"
    HAVE_HASH_MULTISET_GLOBAL
  )

  if(HAVE_HASH_MULTISET_GLOBAL)
    set(HASH_MULTISET_H "<ext/hash_set>")
    set(HASH_MULTISET_CLASS "hash_multiset")
    set(HASH_MULTISET_NAMESPACE "")
  endif()
endmacro()
