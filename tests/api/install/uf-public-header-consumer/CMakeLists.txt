cmake_minimum_required(VERSION 3.16)
project(stp_uf_public_header_consumer LANGUAGES C CXX)

find_package(STP CONFIG REQUIRED)
enable_testing()

add_executable(stp-uf-public-header-consumer main.cpp)
target_compile_features(stp-uf-public-header-consumer PRIVATE cxx_std_11)
# STP_C_INTERFACE_LIBRARY is what STPConfig.cmake names as the provider of the
# 2.x C API these programs are written against: stp while libstp still carries
# it, stp2 for a package built with STP_LEGACY_C_INTERFACE=OFF.
target_link_libraries(stp-uf-public-header-consumer PRIVATE ${STP_C_INTERFACE_LIBRARY})
add_test(NAME installed-stp-uf-cpp COMMAND stp-uf-public-header-consumer)

add_executable(stp-uf-c-api-consumer main.c)
target_link_libraries(stp-uf-c-api-consumer PRIVATE ${STP_C_INTERFACE_LIBRARY})
add_test(NAME installed-stp-uf-c COMMAND stp-uf-c-api-consumer)
