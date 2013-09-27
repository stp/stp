include_directories(${CMAKE_SOURCE_DIR}/src/AST/)
add_library(stpmgr
    STP.cpp
    STPManager.cpp
)
target_link_libraries(stpmgr
    AST
)