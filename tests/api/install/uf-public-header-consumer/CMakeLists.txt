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
add_executable(stp-api-c-consumer api.c)
target_link_libraries(stp-api-c-consumer PRIVATE stp)
add_test(NAME installed-stp-api-c COMMAND stp-api-c-consumer)

add_executable(stp-api-cpp-consumer api.cpp)
target_compile_features(stp-api-cpp-consumer PRIVATE cxx_std_17)
target_link_libraries(stp-api-cpp-consumer PRIVATE stp)
add_test(NAME installed-stp-api-cpp COMMAND stp-api-cpp-consumer)

# Managers on several threads at once, one each.
find_package(Threads REQUIRED)
add_executable(stp-api-threads-consumer threads.cpp)
target_compile_features(stp-api-threads-consumer PRIVATE cxx_std_17)
target_link_libraries(stp-api-threads-consumer PRIVATE stp Threads::Threads)
add_test(NAME installed-stp-api-threads COMMAND stp-api-threads-consumer)
