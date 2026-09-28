configure_file(
  run-uf-public-header-consumer.cmake.in
  ${CMAKE_CURRENT_BINARY_DIR}/run-uf-public-header-consumer.cmake
  @ONLY
)

# One consumer, three ways of producing the package it consumes: DESTDIR
# staging, cmake --install --prefix, and the build tree. They fail differently
# -- $<BUILD_INTERFACE:> survives export() and is dropped by install(EXPORT),
# and an absolute install DESTINATION honours DESTDIR while ignoring --prefix
# -- so passing under one says little about the others.
foreach(_stp_export IN ITEMS install-tree install-prefix build-tree)
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
