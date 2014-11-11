# -----------------------------------------------------------------------------
# Create binary
# -----------------------------------------------------------------------------
if (BUILD_STATIC_BIN)
    # FIXME: We should check if the linker supports these flags
    # FIXME: -Wl,--no-export-dynamic is a workaround for a bug in binutils
    # See http://sourceware.org/bugzilla/show_bug.cgi?id=13490
    # https://bugzilla.redhat.com/show_bug.cgi?id=642999
    set(CMAKE_EXE_LINKER_FLAGS "-static -Wl,--no-export-dynamic")
endif()

add_executable(stp_simple
    main_simple.cpp
    ../stp/main_common.cpp
    ../stp/STPProgramGlobals.cpp
    ${PROJECT_BINARY_DIR}/lib/Util/GitSHA1.cpp
)

if (BUILD_STATIC_BIN)
    set_target_properties(stp_simple PROPERTIES LINK_SEARCH_END_STATIC 1)
    set_target_properties(stp_simple PROPERTIES LINK_SEARCH_START_STATIC 0)
endif()

set_target_properties(stp_simple PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})
target_link_libraries(stp_simple libstp)

install(TARGETS stp_simple
        EXPORT ${STP_EXPORT_NAME}
        RUNTIME DESTINATION bin
)
