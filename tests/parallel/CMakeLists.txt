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

# stp-p's tests, label "parallel" (ctest -L parallel). Each starts its own
# processes on at most four CPUs, the size of a CI runner, and sizes itself
# down (or skips the group's checks) when fewer are allowed or the build's
# CaDiCaL has no clause import.

# AddSTPGTest for stp-p: a GoogleTest executable linking stpp, the tool's
# library, on the build's allocator (after stpp, as stp-p links it) unless
# NO_ALLOCATOR is given; its test is labelled "parallel".
function(AddSTPPGTest sourcefile timeout)
  cmake_parse_arguments(T "NO_ALLOCATOR" "" "" ${ARGN})
  get_filename_component(name ${sourcefile} NAME_WE)
  set(testname "stpp-${name}${UNIT_TEST_EXE_SUFFIX}")
  add_executable(${testname} ${sourcefile})
  set(allocator "")
  if(NOT T_NO_ALLOCATOR AND NOT USE_VALGRIND)
    set(allocator ${STP_ALLOCATOR_LIBRARY})
  endif()
  target_link_libraries(${testname} PRIVATE stpp ${allocator} ${GTEST_BOTH_LIBRARIES})
  add_test(NAME ${testname}-gtest COMMAND ${testname}
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
  set_tests_properties(${testname}-gtest PROPERTIES LABELS "parallel"
    TIMEOUT ${timeout})
endfunction()

# The clause rings and the import polls.
AddSTPPGTest(components.cpp 120)
# The race's and the group's report boundaries, from the inside: each
# compiles the tool's source it tests.
AddSTPPGTest(race_protocol.cpp 60)
AddSTPPGTest(group_protocol.cpp 60)
# Replaces operator new, so it is linked without the static allocator,
# which defines its own.
AddSTPPGTest(oom.cpp 60 NO_ALLOCATOR)
if(STP_ALLOCATOR_LIBRARY STREQUAL "mimalloc-static")
  AddSTPPGTest(allocator.cpp 20)
  target_compile_definitions(stpp-allocator${UNIT_TEST_EXE_SUFFIX} PRIVATE
    STP_P="$<TARGET_FILE:stp-p>")
  add_dependencies(stpp-allocator${UNIT_TEST_EXE_SUFFIX} stp-p)
endif()

# End to end: each script takes stp-p and the test driver (stpp-drive).
# An address, thread or memory sanitizer's shadow memory does not fit under
# stp-p's default address-space limit: in such a build the scripts run every
# stp-p and stpp-drive with --worker-memory-mib 0 (sanitizer.py).
set(STPP_SANITIZED 0)
if(SANITIZE OR CMAKE_CXX_FLAGS MATCHES "-fsanitize=([a-z,=-]*,)?(address|thread|memory)")
  set(STPP_SANITIZED 1)
endif()

foreach(name cli lifecycle portfolio hedge batch)
  add_test(NAME stpp-${name} COMMAND ${PYTHON_EXECUTABLE}
    ${CMAKE_CURRENT_SOURCE_DIR}/${name}.py $<TARGET_FILE:stp-p> $<TARGET_FILE:stpp-drive>)
endforeach()
add_test(NAME stpp-group COMMAND ${PYTHON_EXECUTABLE}
  ${CMAKE_CURRENT_SOURCE_DIR}/group.py $<TARGET_FILE:stp-p> $<TARGET_FILE:stpp-drive> 60)
set_tests_properties(stpp-cli stpp-lifecycle stpp-portfolio stpp-hedge stpp-batch
  stpp-group PROPERTIES LABELS "parallel" ENVIRONMENT "STPP_SANITIZED=${STPP_SANITIZED}")
set_tests_properties(stpp-cli stpp-lifecycle stpp-portfolio stpp-hedge
  PROPERTIES TIMEOUT 300)
set_tests_properties(stpp-batch stpp-group PROPERTIES TIMEOUT 600)
