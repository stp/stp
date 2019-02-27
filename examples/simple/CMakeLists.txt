# AUTHORS: Dan Liew, Ryan Gvostes, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.

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
message("STP executable: ${STP_EXECUTABLE}")
message("STP version: ${STP_VERSION}")
message("STP major version: ${STP_VERSION_MAJOR}")
message("STP minor version: ${STP_VERSION_MINOR}")
message("STP patch version: ${STP_VERSION_PATCH}")

# Get full path to STP executable
get_target_property(STP_FULL_PATH ${STP_EXECUTABLE} LOCATION)
message("Full path to STP binary is ${STP_FULL_PATH}")

# -----------------------------------------------------------------------------
# Example program
# -----------------------------------------------------------------------------
include_directories(${STP_INCLUDE_DIRS})
add_executable(stp-example example.c)
target_link_libraries(stp-example stp)
