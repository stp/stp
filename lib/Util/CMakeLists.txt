configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)


# add_executable(measure
#     measure.cpp
#     Functions.cpp
# )
# target_link_libraries(measure
#     stp
# )

add_executable(rewrite_rule_gen
    rewrite_rule_gen.cpp
)
target_link_libraries(rewrite_rule_gen
    libstp
)


add_executable(time_constantbitprop
    time_cbitp.cpp
)
target_link_libraries(time_constantbitprop
    libstp
)


add_executable(test_constantbitprop
    test_cbitp.cpp
    Functions.cpp
)
target_link_libraries(test_constantbitprop
    libstp
)


