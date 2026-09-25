set_property(DIRECTORY PROPERTY COMPILE_DEFINITIONS "")
set_property(DIRECTORY PROPERTY INCLUDE_DIRECTORIES "")
set_property(DIRECTORY PROPERTY LINK_LIBRARIES "")

add_executable(stp_lra_imath_smoke imath_smoke.c)
target_link_libraries(stp_lra_imath_smoke PRIVATE stp_lra_imath)
set_property(TARGET stp_lra_imath_smoke PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/lib/Lra"
)
set_property(TARGET stp_lra_imath_smoke PROPERTY COMPILE_DEFINITIONS "")
set_target_properties(stp_lra_imath_smoke PROPERTIES
  C_STANDARD 99
  C_STANDARD_REQUIRED ON
  C_EXTENSIONS OFF
)
add_test(NAME lra_imath_smoke COMMAND stp_lra_imath_smoke)
set_tests_properties(lra_imath_smoke PROPERTIES LABELS "lra;imath")

find_package(Threads REQUIRED)
add_executable(stp_lra_exact_tests exact_rational_tests.cpp)
target_link_libraries(stp_lra_exact_tests PRIVATE
  stp_lra_exact
  Threads::Threads
)
set_property(TARGET stp_lra_exact_tests PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/lib/Lra"
)
set_property(TARGET stp_lra_exact_tests PROPERTY COMPILE_DEFINITIONS
  STP_LRA_TEST_FAULT_INJECTION)
set_target_properties(stp_lra_exact_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_exact_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_exact_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()

# Exercise the independently reviewable frontend archive against an
# uninstalled static host assembled from the same STP object graph.  Public
# API smokes below still link the actual shared/static product library.
set(stp_lra_frontend_test_libraries
  stp_lra_focused_host
  # The host object graph owns model invalidation and same-candidate
  # entry points even when a focused test exercises only frontend behavior.
  # Supply their private definitions without exporting any new target.
  stp_lra_integration
)

# Registration order and public reset also exercise the solve/model path.
# Use the product objects without changing the independent frontend tests.
add_executable(stp_lra_real_symbol_tests real_symbol_tests.cpp
  $<TARGET_OBJECTS:stp_lra_product_objects>)
target_link_libraries(stp_lra_real_symbol_tests PRIVATE
  stp_lra_focused_host IMath Threads::Threads)
target_include_directories(stp_lra_real_symbol_tests PRIVATE
  "${PROJECT_SOURCE_DIR}/include" "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_BINARY_DIR}/include" "${STP_UNORDERED_DENSE_INCLUDE_DIR}")
target_include_directories(stp_lra_real_symbol_tests SYSTEM PRIVATE "${ABC_INCLUDE_DIR}")
target_compile_definitions(stp_lra_real_symbol_tests PRIVATE
  ${backend_define} SIZEOF_VOID_P=${SIZEOF_VOID_P}
  SIZEOF_LONG=${SIZEOF_LONG} SIZEOF_INT=${SIZEOF_INT})
if(WIN32)
  if(SIZEOF_VOID_P EQUAL 8)
    target_compile_definitions(stp_lra_real_symbol_tests PRIVATE NT64 WIN32_NO_DLL)
  endif()
elseif(SIZEOF_VOID_P EQUAL 8)
  target_compile_definitions(stp_lra_real_symbol_tests PRIVATE LIN64)
else()
  target_compile_definitions(stp_lra_real_symbol_tests PRIVATE LIN)
endif()
set_target_properties(stp_lra_real_symbol_tests PROPERTIES
  CXX_STANDARD 17 CXX_STANDARD_REQUIRED ON CXX_EXTENSIONS OFF)
add_test(NAME lra_real_symbol_membership COMMAND stp_lra_real_symbol_tests)
set_tests_properties(lra_real_symbol_membership PROPERTIES
  LABELS "lra;frontend;model;reset")

# Deterministic cancellation at public preparation boundaries.
add_executable(stp_lra_preparation_deadline_tests preparation_deadline_tests.cpp
  $<TARGET_OBJECTS:stp_lra_product_objects>)
target_link_libraries(stp_lra_preparation_deadline_tests PRIVATE
  stp_lra_focused_host IMath Threads::Threads)
target_include_directories(stp_lra_preparation_deadline_tests PRIVATE
  "${PROJECT_SOURCE_DIR}/include" "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_SOURCE_DIR}/lib/Lra"
  "${PROJECT_BINARY_DIR}/include" "${STP_UNORDERED_DENSE_INCLUDE_DIR}")
target_include_directories(stp_lra_preparation_deadline_tests SYSTEM PRIVATE "${ABC_INCLUDE_DIR}")
target_compile_definitions(stp_lra_preparation_deadline_tests PRIVATE
  ${backend_define} SIZEOF_VOID_P=${SIZEOF_VOID_P}
  SIZEOF_LONG=${SIZEOF_LONG} SIZEOF_INT=${SIZEOF_INT})
if(WIN32)
  if(SIZEOF_VOID_P EQUAL 8)
    target_compile_definitions(stp_lra_preparation_deadline_tests PRIVATE NT64 WIN32_NO_DLL)
  endif()
elseif(SIZEOF_VOID_P EQUAL 8)
  target_compile_definitions(stp_lra_preparation_deadline_tests PRIVATE LIN64)
else()
  target_compile_definitions(stp_lra_preparation_deadline_tests PRIVATE LIN)
endif()
set_target_properties(stp_lra_preparation_deadline_tests PROPERTIES
  CXX_STANDARD 17 CXX_STANDARD_REQUIRED ON CXX_EXTENSIONS OFF)
add_test(NAME lra_preparation_deadline COMMAND stp_lra_preparation_deadline_tests)
set_tests_properties(lra_preparation_deadline PROPERTIES
  LABELS "lra;frontend;model;deadline")

add_executable(stp_lra_registry_adapter_tests
  registry_adapter_tests.cpp
  "${PROJECT_SOURCE_DIR}/lib/Lra/LraBudgetRefusal.cpp")
target_link_libraries(stp_lra_registry_adapter_tests PRIVATE
  stp_lra_focused_host
  stp_lra_integration
)
set_property(TARGET stp_lra_registry_adapter_tests
  PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/include"
  "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_SOURCE_DIR}/lib/Lra"
  "${PROJECT_BINARY_DIR}/include"
)
target_include_directories(stp_lra_registry_adapter_tests SYSTEM PRIVATE
  "${ABC_INCLUDE_DIR}"
)
set_property(TARGET stp_lra_registry_adapter_tests
  PROPERTY COMPILE_DEFINITIONS
  "STP_LRA_TEST_FAULT_INJECTION"
)
set_target_properties(stp_lra_registry_adapter_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_registry_adapter_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_registry_adapter_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()
add_test(NAME lra_registry_adapter
  COMMAND stp_lra_registry_adapter_tests)
set_tests_properties(lra_registry_adapter PROPERTIES
  LABELS "lra;registry;core-map;sat-adapter;clause;model-stage;fault"
)

add_executable(stp_lra_backend_adapter_tests
  backend_adapter_tests.cpp)
target_link_libraries(stp_lra_backend_adapter_tests PRIVATE
  stp_lra_focused_host
  stp_lra_integration
)
set_property(TARGET stp_lra_backend_adapter_tests
  PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/include"
  "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_SOURCE_DIR}/lib/Lra"
  "${PROJECT_BINARY_DIR}/include"
)
target_include_directories(stp_lra_backend_adapter_tests SYSTEM PRIVATE
  "${ABC_INCLUDE_DIR}"
)
set(backend_label "configured-common-backend")
set(backend_define "")
if(USE_CADICAL)
  set(backend_label "cadical")
  set(backend_define "USE_CADICAL")
elseif(USE_RISS)
  set(backend_label "riss")
  set(backend_define "USE_RISS")
elseif(USE_MINISAT)
  set(backend_label "minisat-control")
  set(backend_define "USE_MINISAT")
endif()
set_property(TARGET stp_lra_backend_adapter_tests
  PROPERTY COMPILE_DEFINITIONS
  "STP_LRA_TEST_FAULT_INJECTION;${backend_define};STP_BACKEND_LABEL=\"${backend_label}\";SIZEOF_VOID_P=${SIZEOF_VOID_P};SIZEOF_LONG=${SIZEOF_LONG};SIZEOF_INT=${SIZEOF_INT}"
)
if(WIN32)
  if(SIZEOF_VOID_P EQUAL 8)
    target_compile_definitions(stp_lra_backend_adapter_tests PRIVATE
      NT64 WIN32_NO_DLL)
  endif()
elseif(SIZEOF_VOID_P EQUAL 8)
  target_compile_definitions(stp_lra_backend_adapter_tests PRIVATE LIN64)
else()
  target_compile_definitions(stp_lra_backend_adapter_tests PRIVATE LIN)
endif()
set_target_properties(stp_lra_backend_adapter_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_backend_adapter_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_backend_adapter_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()
add_test(NAME lra_configured_backend_adapter
  COMMAND stp_lra_backend_adapter_tests)
set_tests_properties(lra_configured_backend_adapter PROPERTIES
  LABELS "lra;backend;clause;resolve;model-stage"
)

if(STP_EXECUTABLE_AVAILABLE)
  add_test(NAME lra_dyadic_arithmetic
    COMMAND "${PYTHON_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/dyadic_arithmetic_runner.py"
      "$<TARGET_FILE:stp_lra_exact_tests>")
  set_tests_properties(lra_dyadic_arithmetic PROPERTIES LABELS "lra;arithmetic;differential" TIMEOUT 90)
  add_test(NAME lra_semantic_context_matrix
    COMMAND "${PYTHON_EXECUTABLE}"
            "${CMAKE_CURRENT_SOURCE_DIR}/semantic_runner.py"
            "$<TARGET_FILE:stp-bin>" "${backend_label}")
  set_tests_properties(lra_semantic_context_matrix PROPERTIES
    LABELS "lra;semantic;coordinator;model;context;combine;backend"
    TIMEOUT 3600
  )
endif()

add_executable(stp_lra_combination_api_tests
  combination_api_tests.cpp)
target_link_libraries(stp_lra_combination_api_tests PRIVATE
  stp Threads::Threads)
set_property(TARGET stp_lra_combination_api_tests
  PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_BINARY_DIR}/include"
  "${PROJECT_SOURCE_DIR}/include"
)
set_target_properties(stp_lra_combination_api_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
add_test(NAME lra_combination_api
  COMMAND stp_lra_combination_api_tests)
set_tests_properties(lra_combination_api PROPERTIES
  LABELS "lra;api;combine;array;legacy;context;concurrency"
  TIMEOUT 3600
)

add_executable(stp_lra_real_capability_api_tests
  real_capability_api_tests.cpp)
target_link_libraries(stp_lra_real_capability_api_tests PRIVATE
  stp Threads::Threads)
set_property(TARGET stp_lra_real_capability_api_tests
  PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_BINARY_DIR}/include"
  "${PROJECT_SOURCE_DIR}/include"
)
set_target_properties(stp_lra_real_capability_api_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
add_test(NAME lra_real_capability_api
  COMMAND stp_lra_real_capability_api_tests)
set_tests_properties(lra_real_capability_api PROPERTIES
  LABELS "lra;api;ite"
  TIMEOUT 3600
)

add_executable(stp_lra_coordinator_fault_tests
  coordinator_fault_tests.cpp)
target_link_libraries(stp_lra_coordinator_fault_tests PRIVATE
  stp_lra_focused_host
  stp_lra_integration
)
set_property(TARGET stp_lra_coordinator_fault_tests
  PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/include"
  "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_SOURCE_DIR}/lib/Lra"
  "${PROJECT_BINARY_DIR}/include"
)
target_include_directories(stp_lra_coordinator_fault_tests SYSTEM PRIVATE
  "${ABC_INCLUDE_DIR}"
)
set_property(TARGET stp_lra_coordinator_fault_tests
  PROPERTY COMPILE_DEFINITIONS
  "STP_LRA_TEST_FAULT_INJECTION;${backend_define};SIZEOF_VOID_P=${SIZEOF_VOID_P};SIZEOF_LONG=${SIZEOF_LONG};SIZEOF_INT=${SIZEOF_INT}"
)
if(USE_CADICAL)
  target_link_libraries(stp_lra_coordinator_fault_tests PRIVATE CaDiCaL)
  if(CADICAL_HAS_DECISION_POLARITY)
    target_compile_definitions(stp_lra_coordinator_fault_tests PRIVATE
      STP_CADICAL_HAS_DECISION_POLARITY)
  endif()
endif()
if(WIN32)
  if(SIZEOF_VOID_P EQUAL 8)
    target_compile_definitions(stp_lra_coordinator_fault_tests PRIVATE
      NT64 WIN32_NO_DLL)
  endif()
elseif(SIZEOF_VOID_P EQUAL 8)
  target_compile_definitions(stp_lra_coordinator_fault_tests PRIVATE
    LIN64)
else()
  target_compile_definitions(stp_lra_coordinator_fault_tests PRIVATE
    LIN)
endif()
set_target_properties(stp_lra_coordinator_fault_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_coordinator_fault_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_coordinator_fault_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()
add_test(NAME lra_coordinator_faults
  COMMAND stp_lra_coordinator_fault_tests)
set_tests_properties(lra_coordinator_faults PROPERTIES
  LABELS "lra;coordinator;fault;stale;model-stage;array"
)

add_executable(stp_lra_real_frontend_fault_tests
  real_frontend_fault_tests.cpp)
target_link_libraries(stp_lra_real_frontend_fault_tests PRIVATE
  ${stp_lra_frontend_test_libraries}
)
set_property(TARGET stp_lra_real_frontend_fault_tests PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/include"
  "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_SOURCE_DIR}/lib/Lra"
  "${PROJECT_BINARY_DIR}/include"
)
set_property(TARGET stp_lra_real_frontend_fault_tests PROPERTY COMPILE_DEFINITIONS
  "STP_LRA_TEST_FAULT_INJECTION"
)
set_target_properties(stp_lra_real_frontend_fault_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_real_frontend_fault_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_real_frontend_fault_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()
add_test(NAME lra_frontend_fault_resource
  COMMAND stp_lra_real_frontend_fault_tests)
set_tests_properties(lra_frontend_fault_resource PROPERTIES
  LABELS "lra;frontend;fault;resource"
)

add_test(NAME lra_exact_rational_unit
  COMMAND stp_lra_exact_tests unit
)
add_test(NAME lra_exact_rational_huge
  COMMAND stp_lra_exact_tests huge
)
add_test(NAME lra_exact_rational_fault
  COMMAND stp_lra_exact_tests fault
)
add_test(NAME lra_exact_rational_concurrency
  COMMAND stp_lra_exact_tests concurrency
)

add_executable(stp_lra_storage_identity_tests storage_identity_tests.cpp
  support/BoundActivityTrail.cpp)
target_link_libraries(stp_lra_storage_identity_tests PRIVATE
  stp_lra_storage
  Threads::Threads
)
set_property(TARGET stp_lra_storage_identity_tests PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/lib/Lra"
  "${PROJECT_SOURCE_DIR}/tests/lra"
)
set_property(TARGET stp_lra_storage_identity_tests PROPERTY COMPILE_DEFINITIONS
  STP_LRA_TEST_FAULT_INJECTION
)
set_target_properties(stp_lra_storage_identity_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_storage_identity_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_storage_identity_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()

foreach(mode ids arena trail fault concurrency)
  add_test(NAME lra_storage_identity_${mode}
    COMMAND stp_lra_storage_identity_tests ${mode}
  )
  set_tests_properties(lra_storage_identity_${mode} PROPERTIES
    LABELS "lra;storage;identity"
  )
endforeach()

add_executable(stp_lra_storage_containers_tests storage_containers_tests.cpp
  support/BoundActivityTrail.cpp)
target_link_libraries(stp_lra_storage_containers_tests PRIVATE
  stp_lra_core
  stp_lra_storage
  stp_lra_exact
  Threads::Threads
)
set_property(TARGET stp_lra_storage_containers_tests PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/lib/Lra"
  "${PROJECT_SOURCE_DIR}/tests/lra"
)
set_property(TARGET stp_lra_storage_containers_tests PROPERTY COMPILE_DEFINITIONS
  STP_LRA_TEST_FAULT_INJECTION
)
set_target_properties(stp_lra_storage_containers_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_storage_containers_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_storage_containers_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()

foreach(mode vector dense trail sort scope growth fault concurrency debug)
  add_test(NAME lra_storage_containers_${mode}
    COMMAND stp_lra_storage_containers_tests ${mode}
  )
  set_tests_properties(lra_storage_containers_${mode} PROPERTIES
    LABELS "lra;storage;containers"
  )
endforeach()

add_executable(stp_lra_core_tests exact_lra_core_tests.cpp)
target_link_libraries(stp_lra_core_tests PRIVATE
  stp_lra_core
  stp_lra_storage
  stp_lra_exact
  Threads::Threads
)
set_property(TARGET stp_lra_core_tests PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/lib/Lra"
)
set_property(TARGET stp_lra_core_tests PROPERTY COMPILE_DEFINITIONS
  STP_LRA_TEST_FAULT_INJECTION
)
set_target_properties(stp_lra_core_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_core_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_core_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()

foreach(mode semantic strict conflict interrupt resource lifecycle rolling huge differential concurrency early-conflict soi extension polarity conflict-recovery direct-bounds)
  add_test(NAME lra_core_${mode}
    COMMAND stp_lra_core_tests ${mode}
  )
  set_tests_properties(lra_core_${mode} PROPERTIES
    LABELS "lra;core"
  )
endforeach()

add_executable(stp_lra_core_fault_tests exact_lra_core_fault_tests.cpp)
target_link_libraries(stp_lra_core_fault_tests PRIVATE
  stp_lra_core
  stp_lra_storage
  stp_lra_exact
  Threads::Threads
)
set_property(TARGET stp_lra_core_fault_tests PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/lib/Lra"
)
set_property(TARGET stp_lra_core_fault_tests PROPERTY COMPILE_DEFINITIONS
  STP_LRA_TEST_FAULT_INJECTION
)
set_target_properties(stp_lra_core_fault_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_core_fault_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_core_fault_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()
foreach(mode cpp imath)
  add_test(NAME lra_core_fault_${mode}
    COMMAND stp_lra_core_fault_tests ${mode}
  )
  set_tests_properties(lra_core_fault_${mode} PROPERTIES
    LABELS "lra;core;fault"
  )
endforeach()
add_test(NAME lra_verifier_faults
  COMMAND stp_lra_core_fault_tests verifier
)
set_tests_properties(lra_verifier_faults PROPERTIES
  LABELS "lra;verifier;fault"
)

add_executable(stp_lra_ownership_amendment_tests
  exact_lra_ownership_amendment_tests.cpp
)
target_link_libraries(stp_lra_ownership_amendment_tests PRIVATE
  stp_lra_core
  stp_lra_storage
  stp_lra_exact
  Threads::Threads
)
set_property(TARGET stp_lra_ownership_amendment_tests
  PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/lib/Lra"
)
set_property(TARGET stp_lra_ownership_amendment_tests
  PROPERTY COMPILE_DEFINITIONS STP_LRA_TEST_FAULT_INJECTION
)
set_target_properties(stp_lra_ownership_amendment_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_ownership_amendment_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_ownership_amendment_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()
add_test(NAME lra_ownership_lifecycle
  COMMAND stp_lra_ownership_amendment_tests lifecycle
)
set_tests_properties(lra_ownership_lifecycle PROPERTIES
  LABELS "lra;ownership;lifecycle"
)
add_test(NAME lra_ownership_destruction_stress
  COMMAND stp_lra_ownership_amendment_tests stress 10000
)
set_tests_properties(lra_ownership_destruction_stress PROPERTIES
  LABELS "lra;ownership;stress"
  TIMEOUT 3600
)

foreach(verifier_target verifier corruption)
  add_executable(stp_lra_${verifier_target}_tests
    exact_lra_${verifier_target}_tests.cpp
  )
  target_link_libraries(stp_lra_${verifier_target}_tests PRIVATE
    stp_lra_core
    stp_lra_storage
    stp_lra_exact
    Threads::Threads
  )
  set_property(TARGET stp_lra_${verifier_target}_tests
    PROPERTY INCLUDE_DIRECTORIES
    "${PROJECT_SOURCE_DIR}/lib/Lra"
  )
  set_property(TARGET stp_lra_${verifier_target}_tests
    PROPERTY COMPILE_DEFINITIONS STP_LRA_TEST_FAULT_INJECTION
  )
  set_target_properties(stp_lra_${verifier_target}_tests PROPERTIES
    CXX_STANDARD 17
    CXX_STANDARD_REQUIRED ON
    CXX_EXTENSIONS OFF
  )
  if(MSVC)
    target_compile_options(stp_lra_${verifier_target}_tests PRIVATE /W4)
  else()
    target_compile_options(stp_lra_${verifier_target}_tests PRIVATE
      -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
    )
  endif()
  add_test(NAME lra_${verifier_target}
    COMMAND stp_lra_${verifier_target}_tests
  )
  set_tests_properties(lra_${verifier_target} PROPERTIES
    LABELS "lra;verifier"
  )
endforeach()

add_executable(stp_lra_real_frontend_tests real_frontend_tests.cpp)
target_link_libraries(stp_lra_real_frontend_tests PRIVATE
  ${stp_lra_frontend_test_libraries}
)
set_property(TARGET stp_lra_real_frontend_tests PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_SOURCE_DIR}/include"
  "${PROJECT_SOURCE_DIR}/lib"
  "${PROJECT_SOURCE_DIR}/lib/Lra"
  "${PROJECT_BINARY_DIR}/include"
)
set_property(TARGET stp_lra_real_frontend_tests PROPERTY COMPILE_DEFINITIONS "")
set_target_properties(stp_lra_real_frontend_tests PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
if(MSVC)
  target_compile_options(stp_lra_real_frontend_tests PRIVATE /W4)
else()
  target_compile_options(stp_lra_real_frontend_tests PRIVATE
    -Wall -Wextra -Wpedantic -Wconversion -Wsign-conversion
  )
endif()
foreach(mode unit deep normalization shared-dag equality lifetime validation metrics)
  add_test(NAME lra_frontend_${mode}
    COMMAND stp_lra_real_frontend_tests ${mode}
  )
  set_tests_properties(lra_frontend_${mode} PROPERTIES
    LABELS "lra;frontend"
  )
endforeach()
set_tests_properties(lra_frontend_shared-dag PROPERTIES TIMEOUT 30)
add_test(NAME lra_frontend_internal_print_barrier
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_CURRENT_SOURCE_DIR}/real_frontend_negative_runner.py"
    "$<TARGET_FILE:stp_lra_real_frontend_tests>")
set_tests_properties(lra_frontend_internal_print_barrier PROPERTIES
  LABELS "lra;frontend;negative;printer"
)

add_executable(stp_lra_real_c_api_smoke real_c_api_smoke.c)
target_link_libraries(stp_lra_real_c_api_smoke PRIVATE stp)
set_property(TARGET stp_lra_real_c_api_smoke PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_BINARY_DIR}/include"
  "${PROJECT_SOURCE_DIR}/include"
)
set_target_properties(stp_lra_real_c_api_smoke PROPERTIES
  C_STANDARD 99
  C_STANDARD_REQUIRED ON
  C_EXTENSIONS OFF
)
add_executable(stp_lra_real_c_api_undeleted_expr real_c_api_undeleted_expr.c)
target_link_libraries(stp_lra_real_c_api_undeleted_expr PRIVATE stp)
set_property(TARGET stp_lra_real_c_api_undeleted_expr PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_BINARY_DIR}/include"
  "${PROJECT_SOURCE_DIR}/include"
)
set_target_properties(stp_lra_real_c_api_undeleted_expr PROPERTIES
  C_STANDARD 99
  C_STANDARD_REQUIRED ON
  C_EXTENSIONS OFF
)
add_test(NAME lra_c_api_undeleted_expr
         COMMAND stp_lra_real_c_api_undeleted_expr)

add_test(NAME lra_c_api_smoke COMMAND stp_lra_real_c_api_smoke)
set_tests_properties(lra_c_api_smoke PROPERTIES
  LABELS "lra;api;model"
)

add_test(NAME lra_c_api_negative
  COMMAND "${PYTHON_EXECUTABLE}"
    "${CMAKE_CURRENT_SOURCE_DIR}/real_c_api_negative_runner.py"
    "$<TARGET_FILE:stp_lra_real_c_api_smoke>")
set_tests_properties(lra_c_api_negative PROPERTIES
  LABELS "lra;api;negative"
)

add_executable(stp_lra_real_cpp_api_smoke real_cpp_api_smoke.cpp)
target_link_libraries(stp_lra_real_cpp_api_smoke PRIVATE stp)
set_property(TARGET stp_lra_real_cpp_api_smoke PROPERTY INCLUDE_DIRECTORIES
  "${PROJECT_BINARY_DIR}/include"
  "${PROJECT_SOURCE_DIR}/include"
  "${PROJECT_SOURCE_DIR}/lib"
)
target_include_directories(stp_lra_real_cpp_api_smoke SYSTEM PRIVATE
  "${ABC_INCLUDE_DIR}"
)
set_target_properties(stp_lra_real_cpp_api_smoke PROPERTIES
  CXX_STANDARD 17
  CXX_STANDARD_REQUIRED ON
  CXX_EXTENSIONS OFF
)
target_compile_definitions(stp_lra_real_cpp_api_smoke PRIVATE
  ${backend_define}
  SIZEOF_VOID_P=${SIZEOF_VOID_P}
  SIZEOF_LONG=${SIZEOF_LONG}
  SIZEOF_INT=${SIZEOF_INT}
)
if(WIN32)
  if(SIZEOF_VOID_P EQUAL 8)
    target_compile_definitions(stp_lra_real_cpp_api_smoke PRIVATE
      NT64 WIN32_NO_DLL)
  endif()
elseif(SIZEOF_VOID_P EQUAL 8)
  target_compile_definitions(stp_lra_real_cpp_api_smoke PRIVATE LIN64)
else()
  target_compile_definitions(stp_lra_real_cpp_api_smoke PRIVATE LIN)
endif()
add_test(NAME lra_cpp_api_smoke COMMAND stp_lra_real_cpp_api_smoke)
set_tests_properties(lra_cpp_api_smoke PROPERTIES
  LABELS "lra;api;model;context"
)

if(ENABLE_PYTHON_INTERFACE)
  add_test(NAME lra_python_api_smoke
    COMMAND "${CMAKE_COMMAND}" -E env
      "PYTHONPATH=${PROJECT_BINARY_DIR}/bindings/python"
      "${PYTHON_EXECUTABLE}"
      "${CMAKE_CURRENT_SOURCE_DIR}/real_python_api_smoke.py"
  )
  set_tests_properties(lra_python_api_smoke PROPERTIES
    LABELS "lra;api;python;model;context"
  )
endif()
