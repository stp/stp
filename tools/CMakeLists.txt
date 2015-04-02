add_subdirectory(stp)
add_subdirectory(stp_simple)
add_subdirectory(stp_constantbitprop)

# add_executable(measure
#     measure.cpp
#     Functions.cpp
# )
# target_link_libraries(measure
#     stp
# )

set(CMAKE_EXE_LINKER_FLAGS "-pthread ${CMAKE_EXE_LINKER_FLAGS}")
add_executable(rewrite_rule_gen
    rewrite_rule_gen.cpp
)
target_link_libraries(rewrite_rule_gen
    libstp
)


# add_executable(time_constantbitprop
#     time_cbitp.cpp
# )
# target_link_libraries(time_constantbitprop
#     libstp
# )
#
#
# add_executable(test_constantbitprop
#     test_cbitp.cpp
#     Functions.cpp
# )
# target_link_libraries(test_constantbitprop
#     libstp
# )
