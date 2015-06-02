add_subdirectory(stp)
add_subdirectory(stp_simple)

option(BUILD_EXTRA_TOOLS "Build extra tools" ON)
if (BUILD_EXTRA_TOOLS)
  add_subdirectory(stp_constantbitprop)
  add_subdirectory(rewrite_rule_gen)
endif()


# add_executable(measure
#     measure.cpp
#     Functions.cpp
# )
# target_link_libraries(measure
#     stp
# )
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
