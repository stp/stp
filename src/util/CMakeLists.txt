include_directories(${CMAKE_CURRENT_BINARY_DIR}/../AST/)
add_executable(measure
    measure.cpp
    Functions.cpp
)
target_link_libraries(measure
    stp
)

add_executable(apply
    apply.cpp
)
target_link_libraries(apply
    stp
)

add_executable(time_cbitp
    time_cbitp.cpp
)
target_link_libraries(time_cbitp
    stp
)

add_executable(test_cbitp
    test_cbitp.cpp
)
target_link_libraries(test_cbitp
    stp
)


