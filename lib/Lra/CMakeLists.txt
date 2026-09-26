# Private exact-number substrate. Nothing in this directory is installed,
# exported, or aliased as a public STP component.  The enabled libstp embeds
# the separate product object closure declared below; the static archives stay
# independently linkable review/test boundaries and never enter an export set.
# The repository root carries solver-backend definitions and include paths as
# directory properties.  This private arithmetic closure deliberately starts
# with an empty directory interface and adds only its own files below.
set_property(DIRECTORY PROPERTY COMPILE_DEFINITIONS "")
# Whether assertions are live is a whole-project decision, not a component
# one.  The empty interface above is about solver backends and include paths;
# it also dropped the root's -DNDEBUG, which left this directory's asserts
# firing in a Release build that had asked for none -- so a caller who leaked
# a Real Expr got SIGABRT out of libstp where the same bit-vector mistake is
# the leak c_interface.h documents.  Re-apply the project's choice.
if(NOT ENABLE_ASSERTIONS)
    set_property(DIRECTORY APPEND PROPERTY COMPILE_DEFINITIONS NDEBUG)
endif()
set_property(DIRECTORY PROPERTY INCLUDE_DIRECTORIES "")
set_property(DIRECTORY PROPERTY LINK_LIBRARIES "")

# Only the tests link the static archives below, so they are EXCLUDE_FROM_ALL:
# a build without tests compiles none of them, and a test that links one
# builds it.

# ExactRational.cpp calls six to eight BudgetAccess entry points per exact
# rational operation -- requireActive, limits, record, valueCreated,
# valueDestroyed, observeValue.  Each is a thread-local load, a switch and a
# saturating increment, but they are defined in NumberBudget.cpp, the targets
# carry hidden visibility, and there is no link-time optimisation, so not one
# of them can be inlined.  Against the operation counts a QF_LRA solve reaches
# -- tens of millions of arithmetic operations and twice as many copies -- that
# call overhead dominated the profile.
#
# Compiling the two files as a single translation unit changes nothing
# observable and lets the compiler see through the calls.  Grouped unity mode
# is used rather than a hand-written wrapper so the source lists stay honest,
# and rather than plain unity mode so it applies to these two files only: every
# other source of stp_lra_product_objects, including the C translation units
# that carry per-source allocation-interception flags, still compiles alone.
function(stp_lra_group_number_substrate target)
  set_target_properties(${target} PROPERTIES
    UNITY_BUILD ON
    UNITY_BUILD_MODE GROUP
  )
  set_source_files_properties(ExactRational.cpp NumberBudget.cpp
    TARGET_DIRECTORY ${target}
    PROPERTIES UNITY_GROUP "stp_lra_number_substrate"
  )
endfunction()

# STP takes ankerl::unordered_dense from a pinned FetchContent source
# directory rather than a vendored path below lib/. AST.h includes that
# header, so isolated LRA targets that consume the common AST need the same
# header-only prerequisite without acquiring any additional link edge.

# STP's side of the IMath seam: the allocation hooks that IMath's two
# translation units were force-included with, and which account every
# arbitrary-precision allocation against the current query's budget. IMath
# itself is built by cmake/FindIMath.cmake.
add_library(stp_lra_imath STATIC EXCLUDE_FROM_ALL ImathAllocHooks.c)
target_link_libraries(stp_lra_imath PUBLIC IMath)

set_target_properties(stp_lra_imath PROPERTIES
  C_STANDARD 99
  C_STANDARD_REQUIRED ON
  C_EXTENSIONS OFF
  POSITION_INDEPENDENT_CODE ON
  C_VISIBILITY_PRESET hidden
  VISIBILITY_INLINES_HIDDEN ON
)

set_property(TARGET stp_lra_imath PROPERTY INCLUDE_DIRECTORIES
  "${CMAKE_CURRENT_SOURCE_DIR}"
)
if(ENABLE_TESTING)
  target_compile_definitions(stp_lra_imath PRIVATE
    STP_LRA_TEST_FAULT_INJECTION
  )
endif()

if(MSVC)
  target_compile_options(stp_lra_imath PRIVATE /W4)
else()
  target_compile_options(stp_lra_imath PRIVATE
    -Wall -Wextra -Wpedantic
    $<$<BOOL:${WERROR}>:-Werror>
  )
endif()

add_library(stp_lra_exact STATIC EXCLUDE_FROM_ALL
  ExactRational.cpp
  NumberBudget.cpp
)
set_target_properties(stp_lra_exact PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
  POSITION_INDEPENDENT_CODE ON
  CXX_VISIBILITY_PRESET hidden
  VISIBILITY_INLINES_HIDDEN ON
)
set_property(TARGET stp_lra_exact PROPERTY INCLUDE_DIRECTORIES
  "${CMAKE_CURRENT_SOURCE_DIR}"
)
set_property(TARGET stp_lra_exact PROPERTY COMPILE_DEFINITIONS "")
if(ENABLE_TESTING)
  target_compile_definitions(stp_lra_exact PRIVATE
    STP_LRA_TEST_FAULT_INJECTION
  )
endif()
stp_lra_group_number_substrate(stp_lra_exact)

# PUBLIC: ExactRational.h includes <imrat.h>, so IMath's headers are a usage
# requirement of this target, not just an implementation detail of it.
target_link_libraries(stp_lra_exact PUBLIC stp_lra_imath)

# Exact source frontend.  It may depend on the number substrate and common
# AST types only: it deliberately has no SATSolver header/symbol and no
# ExactLraCore consumer edge.
add_library(stp_lra_frontend STATIC EXCLUDE_FROM_ALL
  ASTRealConst.cpp
  LraFrontend.cpp
  LraAtomRegistry.cpp
)
set_target_properties(stp_lra_frontend PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
  POSITION_INDEPENDENT_CODE ON
  CXX_VISIBILITY_PRESET hidden
  VISIBILITY_INLINES_HIDDEN ON
)
set_property(TARGET stp_lra_frontend PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/include"
  "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_BINARY_DIR}/include"
  "${CMAKE_CURRENT_SOURCE_DIR}"
)
set_property(TARGET stp_lra_frontend PROPERTY COMPILE_DEFINITIONS "")
if(ENABLE_TESTING)
  target_compile_definitions(stp_lra_frontend PRIVATE
    STP_LRA_TEST_FAULT_INJECTION
  )
endif()
target_include_directories(stp_lra_frontend SYSTEM PUBLIC
  "${STP_UNORDERED_DENSE_INCLUDE_DIR}"
)
target_link_libraries(stp_lra_frontend PUBLIC stp_lra_exact)
add_dependencies(stp_lra_frontend ASTKind_header)
if(MSVC)
  target_compile_options(stp_lra_frontend PRIVATE /W4)
else()
  target_compile_options(stp_lra_frontend PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
    $<$<BOOL:${WERROR}>:-Werror>
  )
endif()

# Self-contained LRA implementation closure for libstp. A private
# static-library dependency would leak into the exported link interface when
# libstp itself is static.  Compiling the same reviewed sources as hidden
# objects makes both shared and static libstp contain the implementation while
# preserving stp_lra_frontend and its number archives as independent review
# and test targets.  The repository root adds these objects to stp only after
# this subdirectory has been configured.
add_library(stp_lra_product_objects OBJECT
  ASTRealConst.cpp
  LraBudgetRefusal.cpp
  LraFrontend.cpp
  LraAtomRegistry.cpp
  RealModel.cpp
  FloatSimplex.cpp
  FloatBasis.cpp
  LraSolveContext.cpp
  LraCandidateAdapter.cpp
  LraCoordinator.cpp
  LraPresolve.cpp
  LraHighs.cpp
  LraHighsCuts.cpp
  LraRelu.cpp
  LraBooleanBounds.cpp
  LraReluCases.cpp
  LraRelaxation.cpp
  LraReluLp.cpp
  LraReluBranch.cpp
  LraReconstruction.cpp
  LraReplay.cpp
  ExactLraCore.cpp
  ExactLraRegistration.cpp
  ExactConflictVerifier.cpp
  ExactModelVerifier.cpp
  Storage/StorageFailure.cpp
  Storage/LraIds.cpp
  Storage/DenseMembership.cpp
  DeltaRational.cpp
  VariableStore.cpp
  BoundStore.cpp
  ExactSimplex.cpp
  ExactRational.cpp
  NumberBudget.cpp
  ImathAllocHooks.c
)
target_link_libraries(stp_lra_product_objects PRIVATE IMath)
if(ENABLE_HIGHS)
  target_link_libraries(stp_lra_product_objects PRIVATE HiGHS)
endif()
set_target_properties(stp_lra_product_objects PROPERTIES
  C_STANDARD 99
  C_STANDARD_REQUIRED ON
  C_EXTENSIONS OFF
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
  POSITION_INDEPENDENT_CODE ON
  C_VISIBILITY_PRESET hidden
  CXX_VISIBILITY_PRESET hidden
  VISIBILITY_INLINES_HIDDEN ON
)
set_property(TARGET stp_lra_product_objects PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/include"
  "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_BINARY_DIR}/include"
  "${CMAKE_CURRENT_SOURCE_DIR}"
)
set_property(TARGET stp_lra_product_objects PROPERTY COMPILE_DEFINITIONS "")
if(ENABLE_HIGHS)
  target_compile_definitions(stp_lra_product_objects PRIVATE STP_HAVE_HIGHS)
  if(ENABLE_HIGHS_CUT_LOG)
    target_compile_definitions(stp_lra_product_objects PRIVATE STP_HAVE_HIGHS_CUT_LOG)
  endif()
endif()
if(ENABLE_TESTING)
  target_compile_definitions(stp_lra_product_objects PRIVATE
    STP_LRA_TEST_FAULT_INJECTION
  )
endif()
stp_lra_group_number_substrate(stp_lra_product_objects)
target_include_directories(stp_lra_product_objects SYSTEM PRIVATE
  "${STP_UNORDERED_DENSE_INCLUDE_DIR}"
)
add_dependencies(stp_lra_product_objects ASTKind_header)
if(MSVC)
  target_compile_options(stp_lra_product_objects PRIVATE /W4)
else()
  target_compile_options(stp_lra_product_objects PRIVATE
    -Wall -Wextra -Wpedantic
    $<$<COMPILE_LANGUAGE:CXX>:-Wconversion>
    $<$<COMPILE_LANGUAGE:CXX>:-Wsign-conversion>
    $<$<AND:$<COMPILE_LANGUAGE:CXX>,$<BOOL:${WERROR}>>:-Werror>
  )
endif()

# Private storage/identity substrate for the future exact-LRA core.  This
# target is intentionally absent from libstp, install, export, and package
# graphs.  It cannot produce a solver result.
add_library(stp_lra_storage STATIC EXCLUDE_FROM_ALL
  Storage/StorageFailure.cpp
  Storage/LraIds.cpp
  Storage/DenseMembership.cpp
)
set_target_properties(stp_lra_storage PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
  POSITION_INDEPENDENT_CODE ON
  CXX_VISIBILITY_PRESET hidden
  VISIBILITY_INLINES_HIDDEN ON
)
set_property(TARGET stp_lra_storage PROPERTY INCLUDE_DIRECTORIES
  "${CMAKE_CURRENT_SOURCE_DIR}"
)
set_property(TARGET stp_lra_storage PROPERTY COMPILE_DEFINITIONS "")
if(ENABLE_TESTING)
  target_compile_definitions(stp_lra_storage PRIVATE
    STP_LRA_TEST_FAULT_INJECTION
  )
endif()
target_link_libraries(stp_lra_storage PUBLIC stp_lra_exact)
if(MSVC)
  target_compile_options(stp_lra_storage PRIVATE /W4)
else()
  target_compile_options(stp_lra_storage PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
    $<$<BOOL:${WERROR}>:-Werror>
  )
endif()
if(MSVC)
  target_compile_options(stp_lra_exact PRIVATE /W4)
else()
  target_compile_options(stp_lra_exact PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
    $<$<BOOL:${WERROR}>:-Werror>
  )
endif()

# Private SAT-agnostic exact-LRA producer.  It is deliberately not linked by
# libstp and is absent from every install/export/package rule.
add_library(stp_lra_core STATIC EXCLUDE_FROM_ALL
  ExactLraCore.cpp
  ExactLraRegistration.cpp
  ExactConflictVerifier.cpp
  ExactModelVerifier.cpp
  DeltaRational.cpp
  VariableStore.cpp
  BoundStore.cpp
  ExactSimplex.cpp
)
set_target_properties(stp_lra_core PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
  POSITION_INDEPENDENT_CODE ON
  CXX_VISIBILITY_PRESET hidden
  VISIBILITY_INLINES_HIDDEN ON
)
set_property(TARGET stp_lra_core PROPERTY INCLUDE_DIRECTORIES
  "${CMAKE_CURRENT_SOURCE_DIR}"
)
set_property(TARGET stp_lra_core PROPERTY COMPILE_DEFINITIONS "")
if(ENABLE_TESTING)
  target_compile_definitions(stp_lra_core PRIVATE
    STP_LRA_TEST_FAULT_INJECTION
  )
endif()
target_link_libraries(stp_lra_core PUBLIC stp_lra_storage)
# stp's AST headers use ankerl::unordered_dense; the core's clients reach
# them through its public include path.
target_include_directories(stp_lra_core SYSTEM PUBLIC
  "${STP_UNORDERED_DENSE_INCLUDE_DIR}"
)

# Private registry/core/SAT adapter and coordinator.  It consumes only the
# common STP SATSolver interface and is deliberately absent from
# install/export/package rules.  The existing outer solve owner remains the
# only code allowed to invoke SAT search.
add_library(stp_lra_integration STATIC EXCLUDE_FROM_ALL
  RealModel.cpp
  FloatSimplex.cpp
  FloatBasis.cpp
  LraSolveContext.cpp
  LraCandidateAdapter.cpp
  LraCoordinator.cpp
  LraBudgetRefusal.cpp
)
set_target_properties(stp_lra_integration PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
  POSITION_INDEPENDENT_CODE ON
  CXX_VISIBILITY_PRESET hidden
  VISIBILITY_INLINES_HIDDEN ON
)
set_property(TARGET stp_lra_integration PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/include"
  "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_BINARY_DIR}/include"
  "${CMAKE_CURRENT_SOURCE_DIR}"
)
set_property(TARGET stp_lra_integration PROPERTY COMPILE_DEFINITIONS "")
if(ENABLE_TESTING)
  target_compile_definitions(stp_lra_integration PRIVATE
    STP_LRA_TEST_FAULT_INJECTION
  )
endif()
target_include_directories(stp_lra_integration SYSTEM PUBLIC
  "${STP_UNORDERED_DENSE_INCLUDE_DIR}"
)
# PUBLIC: the focused tests link this target and include LraFrontend.h and the
# core headers through it, so both are usage requirements.
target_link_libraries(stp_lra_integration PUBLIC
  stp_lra_frontend
  stp_lra_core
)
add_dependencies(stp_lra_integration ASTKind_header)
if(MSVC)
  target_compile_options(stp_lra_integration PRIVATE /W4)
else()
  target_compile_options(stp_lra_integration PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
    $<$<BOOL:${WERROR}>:-Werror>
  )
endif()
if(MSVC)
  target_compile_options(stp_lra_core PRIVATE /W4)
else()
  target_compile_options(stp_lra_core PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
    $<$<BOOL:${WERROR}>:-Werror>
  )
endif()
