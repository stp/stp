add_subdirectory(stp)
add_subdirectory(stp_simple)

option(BUILD_EXTRA_TOOLS "Build extra tools" ON)
if (BUILD_EXTRA_TOOLS)
  add_subdirectory(stp_constantbitprop)
  add_subdirectory(rewrite_rule_gen)
  # FIXME: Decide what to do with these
  add_subdirectory(time_constantbitprop)
  # These are broken
  # add_subdirectory(measure)
  # add_subdirectory(test_constantbitprop)
endif()
