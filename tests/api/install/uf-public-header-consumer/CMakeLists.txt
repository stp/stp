cmake_minimum_required(VERSION 3.16)
project(stp_uf_public_header_consumer LANGUAGES C CXX)

find_package(STP CONFIG REQUIRED)
enable_testing()

add_executable(stp-uf-public-header-consumer main.cpp)
target_compile_features(stp-uf-public-header-consumer PRIVATE cxx_std_11)
target_link_libraries(stp-uf-public-header-consumer PRIVATE stp)
add_test(NAME installed-stp-uf-cpp COMMAND stp-uf-public-header-consumer)

add_executable(stp-uf-c-api-consumer main.c)
target_link_libraries(stp-uf-c-api-consumer PRIVATE stp)
add_test(NAME installed-stp-uf-c COMMAND stp-uf-c-api-consumer)
