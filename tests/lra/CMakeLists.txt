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

if(STP_EXECUTABLE_AVAILABLE)
  add_test(NAME lra_dyadic_arithmetic
    COMMAND "${PYTHON_EXECUTABLE}" "${CMAKE_CURRENT_SOURCE_DIR}/dyadic_arithmetic_runner.py"
      "$<TARGET_FILE:stp_lra_exact_tests>")
  set_tests_properties(lra_dyadic_arithmetic PROPERTIES LABELS "lra;arithmetic;differential" TIMEOUT 90)
endif()

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
