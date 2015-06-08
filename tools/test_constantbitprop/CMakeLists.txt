add_executable(test_constantbitprop
 test_cbitp.cpp
 ../measure/Functions.cpp
)
target_link_libraries(test_constantbitprop
 libstp
)
