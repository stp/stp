include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
include_directories(${CMAKE_BINARY_DIR}/src/AST/)

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)

# -----------------------------------------------------------------------------
# Create binary
# -----------------------------------------------------------------------------
add_executable(stp
    main.cpp
    STPProgramGlobals.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
)

if (BUILD_STATIC_BIN)
    set_target_properties(stp PROPERTIES LINK_SEARCH_END_STATIC 1)
    set_target_properties(stp PROPERTIES LINK_SEARCH_START_STATIC 0)
endif()

set_target_properties(stp PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})

target_link_libraries(stp libstp)

install(TARGETS stp
        EXPORT ${STP_EXPORT_NAME}
        RUNTIME DESTINATION bin
       )
