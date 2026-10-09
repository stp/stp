#********************************************************************
# AUTHORS: Andrew Teylu
#
# BEGIN DATE: October, 2026
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

# stp-p: STP's parallel decision solver (docs/parallel-solving.rst). Linux
# only, built with -DSTP_BUILD_PARALLEL=ON, on STP's public C++ API.
find_package(NlohmannJson REQUIRED)
add_library(stpp STATIC Cli.cpp Common.cpp Source.cpp Driver.cpp Portfolio.cpp
  Race.cpp Exchange.cpp BatchGroup.cpp)
target_compile_features(stpp PUBLIC cxx_std_17)
target_include_directories(stpp PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(stpp PUBLIC stp NlohmannJson PRIVATE CLI11)
# Every source reaches the 3.x API's generated headers through <stp/stp.hpp>.
add_dependencies(stpp stp_api_tables)
add_executable(stp-p Main.cpp)
# The allocator after stpp: Main.cpp itself allocates nothing, so a static
# allocator archive listed first would have no reference to satisfy yet and
# would be skipped, leaving every process on libc's malloc. After stpp, its
# references pull the allocator's definitions in, still ahead of libc.
target_link_libraries(stp-p PRIVATE stpp ${STP_ALLOCATOR_LIBRARY})
set_target_properties(stp-p PROPERTIES
  RUNTIME_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}"
  INSTALL_RPATH_USE_LINK_PATH TRUE)
install(TARGETS stp-p RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
if(ENABLE_TESTING)
  # The test driver (Drive.cpp): stp-p with the options only tests and
  # measurements use. Never installed.
  add_executable(stpp-drive Drive.cpp)
  target_link_libraries(stpp-drive PRIVATE stpp ${STP_ALLOCATOR_LIBRARY})
  set_target_properties(stpp-drive PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}")
endif()
