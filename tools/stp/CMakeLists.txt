configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)

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

if (Boost_FOUND)
    add_executable(stp
        main.cpp
        main_common.cpp
        STPProgramGlobals.cpp
        ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
    )
endif()

add_executable(stp_simple
    main_simple.cpp
    main_common.cpp
    STPProgramGlobals.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
)

if (BUILD_STATIC_BIN)
    if (Boost_FOUND)
        set_target_properties(stp PROPERTIES LINK_SEARCH_END_STATIC 1)
        set_target_properties(stp PROPERTIES LINK_SEARCH_START_STATIC 0)
    endif()

    set_target_properties(stp_simple PROPERTIES LINK_SEARCH_END_STATIC 1)
    set_target_properties(stp_simple PROPERTIES LINK_SEARCH_START_STATIC 0)
endif()

if (Boost_FOUND)
    set_target_properties(stp PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})
    target_link_libraries(stp libstp)
    install(TARGETS stp
        EXPORT ${STP_EXPORT_NAME}
        RUNTIME DESTINATION bin
    )
endif()

set_target_properties(stp_simple PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})
target_link_libraries(stp_simple libstp)

install(TARGETS stp_simple
        EXPORT ${STP_EXPORT_NAME}
        RUNTIME DESTINATION bin
)