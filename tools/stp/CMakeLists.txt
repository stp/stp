# -----------------------------------------------------------------------------
# Create binary
# -----------------------------------------------------------------------------
if (BUILD_STATIC_BIN)
    # FIXME: We should check if the linker supports these flags
    # FIXME: -Wl,--no-export-dynamic is a workaround for a bug in binutils
    # See http://sourceware.org/bugzilla/show_bug.cgi?id=13490
    # https://bugzilla.redhat.com/show_bug.cgi?id=642999
    set(CMAKE_EXE_LINKER_FLAGS "-static -Wl,--no-export-dynamic")
    set(CMAKE_EXE_LINKER_FLAGS "-pthread ${CMAKE_EXE_LINKER_FLAGS}")
endif()

if (Boost_FOUND)
    add_executable(stp
        main.cpp
        main_common.cpp
        STPProgramGlobals.cpp
        ${PROJECT_BINARY_DIR}/lib/Util/GitSHA1.cpp
    )
    if (BUILD_STATIC_BIN)
        set_target_properties(stp PROPERTIES LINK_SEARCH_END_STATIC 1)
        set_target_properties(stp PROPERTIES LINK_SEARCH_START_STATIC 0)
    endif()

    set_target_properties(stp PROPERTIES
      RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}
      VERSION ${CPACK_PACKAGE_VERSION}
    )
    target_link_libraries(stp libstp)
    install(TARGETS stp
        EXPORT ${STP_EXPORT_NAME}
        RUNTIME DESTINATION bin
    )
endif()
