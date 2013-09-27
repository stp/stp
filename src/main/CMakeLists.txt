include_directories(${CMAKE_SOURCE_DIR}/src/AST/)

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)

add_library(globalstp
    Globals.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
)
add_dependencies(globalstp ASTKind_header)

# -----------------------------------------------------------------------------
# Create binary
# -----------------------------------------------------------------------------
add_executable(stp
    main.cpp
)
set_target_properties(stp PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR})
target_link_libraries(stp ${stp_lib})
