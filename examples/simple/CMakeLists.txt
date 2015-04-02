project(SimpleSTPExample)
cmake_minimum_required(VERSION 2.8)

# See the CMake manual on the find_package() command in Config mode.
set(STP_DIR "" CACHE PATH "Try to use particular STP install (set this to folder where STPConfig.cmake is installed)")

find_package(STP REQUIRED)
message("Using STP rooted at ${STP_DIR}")

# -----------------------------------------------------------------------------
# Show some informative messages
# -----------------------------------------------------------------------------

message("STP include paths are: ${STP_INCLUDE_DIRS}")
message("STP Static Library target is: ${STP_STATIC_LIBRARY}")
message("STP Shared Library target is: ${STP_SHARED_LIBRARY}")
message("STP executable: ${STP_EXECUTABLE}")

# -----------------------------------------------------------------------------
# Pick which STP library to use
# -----------------------------------------------------------------------------
option(USE_STP_SHARED_LIBRARY "Try to build against STP's shared library" ON)

if(USE_STP_SHARED_LIBRARY)
  if(STP_SHARED_LIBRARY)
    set(LIB ${STP_SHARED_LIBRARY})
    message(STATUS "Using STP shared library ${STP_SHARED_LIBRARY}")
  else()
    message(FATAL_ERROR "STP shared library is not available")
  endif()
else()
  if(STP_STATIC_LIBRARY)
    set(LIB ${STP_STATIC_LIBRARY})
    message(STATUS "Using STP static library ${STP_STATIC_LIBRARY}")
  else()
    message(FATAL_ERROR "STP static library is not available")
  endif()
endif()

# Get full path to STP executable
get_target_property(STP_FULL_PATH ${STP_EXECUTABLE} LOCATION)
message("Full path to STP binary is ${STP_FULL_PATH}")

# -----------------------------------------------------------------------------
# Example program
# -----------------------------------------------------------------------------
include_directories(${STP_INCLUDE_DIRS})
add_executable(stp-example example.c)
target_link_libraries(stp-example ${LIB})
