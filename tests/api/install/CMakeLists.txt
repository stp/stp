configure_file(
  run-uf-public-header-consumer.cmake.in
  ${CMAKE_CURRENT_BINARY_DIR}/run-uf-public-header-consumer.cmake
  @ONLY
)

# One consumer, both exported STPTargets.cmake files. export() and
# install(EXPORT) write different content -- $<BUILD_INTERFACE:> survives in the
# first and is dropped from the second -- so passing against one says nothing
# about the other.
foreach(_stp_export IN ITEMS install-tree build-tree)
  add_test(
    NAME uf-${_stp_export}-public-header-consumer
    COMMAND ${CMAKE_COMMAND}
            -DSTP_TEST_CONFIG=$<CONFIG>
            -DSTP_CONSUMER_EXPORT=${_stp_export}
            -P ${CMAKE_CURRENT_BINARY_DIR}/run-uf-public-header-consumer.cmake
  )
  set_tests_properties(
    uf-${_stp_export}-public-header-consumer
    PROPERTIES LABELS "api;install;uf" TIMEOUT 300
  )
endforeach()
