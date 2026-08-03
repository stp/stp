# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos
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

set(PYTHON_INTERFACE_DIR ${PROJECT_BINARY_DIR}/bindings/python)
# The floating-point tests skip themselves when the feature is off; the
# library's floating-point entry points abort in that configuration.
if (ENABLE_FLOATING_POINT)
    set(STP_FLOATING_POINT_PYBOOL "True")
else()
    set(STP_FLOATING_POINT_PYBOOL "False")
endif()
configure_file(tests.py.in tests.py.in.g @ONLY)
configure_file(${CMAKE_CURRENT_BINARY_DIR}/tests.py.in.g
              ${CMAKE_CURRENT_BINARY_DIR}/tests.py)

# this test is way too slow TODO fix
add_custom_target(python-interface-tests
    DEPENDS stp
    COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_BINARY_DIR}/tests.py
    COMMENT "Running python-interface-tests"
)

# Make sure this test-suite runs when "check" is target
add_test (
  NAME python-interface-tests
  COMMAND ${PYTHON_EXECUTABLE} tests.py
  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
)

# Allocator behaviour of the ctypes interface. Unlike the stp binaries, which
# link an allocator statically, a process embedding libstp picks the allocator
# itself - so libstp must not carry one, and preloading one must reach it.
if (STP_ALLOCATOR_PRELOADABLE AND TARGET ${STP_ALLOCATOR_PRELOADABLE})
    set(STP_PRELOADABLE_ALLOCATOR "$<TARGET_FILE:${STP_ALLOCATOR_PRELOADABLE}>")
else()
    set(STP_PRELOADABLE_ALLOCATOR "")
endif()

configure_file(allocator_tests.py.in allocator_tests.py.in.g @ONLY)
# file(GENERATE) rather than a second configure_file: the allocator path is a
# generator expression and is only known at generate time.
file(GENERATE
     OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/allocator_tests.py
     INPUT ${CMAKE_CURRENT_BINARY_DIR}/allocator_tests.py.in.g)

add_test (
  NAME python-allocator-tests
  COMMAND ${PYTHON_EXECUTABLE} allocator_tests.py
  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
)

