add_library(util OBJECT
            ${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp
           )

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/GitSHA1.cpp.in" "${CMAKE_CURRENT_BINARY_DIR}/GitSHA1.cpp" @ONLY)
