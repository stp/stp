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
message("STP Libraries targets are: ${STP_LIBRARIES}")
message("STP executable: ${STP_EXECUTABLE}")

# Get full path to STP executable
get_target_property(STP_FULL_PATH ${STP_EXECUTABLE} LOCATION)
message("Full path to STP binary is ${STP_FULL_PATH}")

# -----------------------------------------------------------------------------
# Example program
# -----------------------------------------------------------------------------
include_directories(${STP_INCLUDE_DIRS})
add_executable(stp-example example.c)
target_link_libraries(stp-example ${STP_LIBRARIES})
