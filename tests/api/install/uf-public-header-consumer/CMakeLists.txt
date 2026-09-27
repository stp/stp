cmake_minimum_required(VERSION 3.16)
project(stp_uf_public_header_consumer LANGUAGES C CXX)

find_package(STP CONFIG REQUIRED)
enable_testing()

add_executable(stp-uf-public-header-consumer main.cpp)
target_compile_features(stp-uf-public-header-consumer PRIVATE cxx_std_11)
# STP_C_INTERFACE_LIBRARY is what STPConfig.cmake names as the provider of the
# 2.x C API these programs are written against: libstp2 (the target stp2).
target_link_libraries(stp-uf-public-header-consumer PRIVATE ${STP_C_INTERFACE_LIBRARY})
add_test(NAME installed-stp-uf-cpp COMMAND stp-uf-public-header-consumer)

add_executable(stp-uf-c-api-consumer main.c)
target_link_libraries(stp-uf-c-api-consumer PRIVATE ${STP_C_INTERFACE_LIBRARY})
add_test(NAME installed-stp-uf-c COMMAND stp-uf-c-api-consumer)

# The 3.x API, which libstp itself carries: the stp target.
add_executable(stp-api3-c-consumer api3.c)
target_link_libraries(stp-api3-c-consumer PRIVATE stp)
add_test(NAME installed-stp-api3-c COMMAND stp-api3-c-consumer)

add_executable(stp-api3-cpp-consumer api3.cpp)
target_compile_features(stp-api3-cpp-consumer PRIVATE cxx_std_17)
target_link_libraries(stp-api3-cpp-consumer PRIVATE stp)
add_test(NAME installed-stp-api3-cpp COMMAND stp-api3-cpp-consumer)
