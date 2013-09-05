include_directories(${CMAKE_CURRENT_BINARY_DIR}/../AST/)
add_library(stpmgr
    STP.cpp
    STPManager.cpp
)
target_link_libraries(stpmgr
    AST
)