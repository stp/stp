configure_file(
  run-uf-public-header-consumer.cmake.in
  ${CMAKE_CURRENT_BINARY_DIR}/run-uf-public-header-consumer.cmake
  @ONLY
)

add_test(
  NAME uf-install-tree-public-header-consumer
  COMMAND ${CMAKE_COMMAND}
          -DSTP_TEST_CONFIG=$<CONFIG>
          -P ${CMAKE_CURRENT_BINARY_DIR}/run-uf-public-header-consumer.cmake
)
set_tests_properties(
  uf-install-tree-public-header-consumer
  PROPERTIES LABELS "api;install;uf" TIMEOUT 300
)
