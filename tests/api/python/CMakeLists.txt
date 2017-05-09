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

set(PYTHON_INTERFACE_DIR ${PROJECT_BINARY_DIR}/bindings/python)
configure_file(tests.py.in tests.py.in.g @ONLY)
file(GENERATE OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>/tests.py
              INPUT  ${CMAKE_CURRENT_BINARY_DIR}/tests.py.in.g)

add_custom_target(python-interface-tests
                  DEPENDS libstp
                  COMMAND ${PYTHON_EXECUTABLE}
                          ${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>/tests.py
                  COMMENT "Running python-interface-tests"
                 )

# Make sure this test-suite runs when "check" is target
add_dependencies(check python-interface-tests)
add_dependencies(python-interface-tests pre-check)
