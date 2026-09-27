# AUTHORS: Andrew Teylu
#
# BEGIN DATE: September, 2026
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

# -----------------------------------------------------------------------------
# The pytest suite of the 3.x Python API, run against the package assembled in
# <build>/bindings/python3 (PYTHONPATH). Registered only when the interpreter
# can import pytest; the suite itself lives in this source directory.
# -----------------------------------------------------------------------------

execute_process(
    COMMAND ${PYTHON_EXECUTABLE} -c "import pytest; print(pytest.__version__)"
    RESULT_VARIABLE _stp_py3_pytest_rc
    OUTPUT_VARIABLE _stp_py3_pytest_version
    OUTPUT_STRIP_TRAILING_WHITESPACE
    ERROR_QUIET)

if(NOT _stp_py3_pytest_rc EQUAL 0)
    message(STATUS "python3-api-tests: ${PYTHON_EXECUTABLE} cannot import pytest; the 3.x Python tests are not registered")
    return()
endif()
message(STATUS "python3-api-tests: pytest ${_stp_py3_pytest_version}")

add_test(
    NAME python3-api-tests
    COMMAND ${PYTHON_EXECUTABLE} -m pytest -q -p no:cacheprovider ${CMAKE_CURRENT_SOURCE_DIR}
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
set_tests_properties(python3-api-tests PROPERTIES
    ENVIRONMENT "PYTHONPATH=${STP_PY3_PYTHONPATH};PYTHONDONTWRITEBYTECODE=1"
    LABELS "python3;api3"
    TIMEOUT 900)
