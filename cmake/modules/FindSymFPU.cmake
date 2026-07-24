# AUTHORS: Andrew Teylu
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

# - Try to find SymFPU
# Once done this will define
#  SYMFPU_FOUND - System has SymFPU
#  SYMFPU_INCLUDE_DIRS - The SymFPU include directories
#  SYMFPU_DEFINITIONS - Compiler switches required for using SymFPU

set(SYMFPU_DEFINITIONS "")

message(STATUS "Finding SymFPU headers...")
message(STATUS "looking at:  ${SYMFPU_INCLUDE_DIRS}")
find_path(SYMFPU_INCLUDE_DIR symfpu/core/unpackedFloat.h
          HINTS ${SYMFPU_INCLUDE_DIRS}
          PATH_SUFFIXES symfpu)
message(STATUS "found: SYMFPU_INCLUDE_DIR: ${SYMFPU_INCLUDE_DIR}")

set(SYMFPU_INCLUDE_DIRS ${SYMFPU_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
# handle the QUIETLY and REQUIRED arguments and set SYMFPU_FOUND to TRUE
# if all listed variables are set
find_package_handle_standard_args(SymFPU DEFAULT_MSG SYMFPU_INCLUDE_DIR)
mark_as_advanced(SYMFPU_INCLUDE_DIR)

