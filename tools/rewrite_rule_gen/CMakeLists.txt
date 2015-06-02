set(CMAKE_EXE_LINKER_FLAGS "-pthread ${CMAKE_EXE_LINKER_FLAGS}")
add_executable(rewrite_rule_gen
    rewrite_rule_gen.cpp
)
target_link_libraries(rewrite_rule_gen
    libstp
)
