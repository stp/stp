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

# - Try to find minisat
# Once done this will define
#  MINISAT_FOUND - System has minisat
#  MINISAT_INCLUDE_DIRS - The minisat include directories
#  MINISAT_LIBRARIES - The libraries needed to use minisat
#  MINISAT_DEFINITIONS - Compiler switches required for using minisat

set(MINISAT_DEFINITIONS "")

message(STATUS "Finding minisat headers...")
message(STATUS "looking at:  ${MINISAT_INCLUDE_DIRS}")
find_path(MINISAT_INCLUDE_DIR minisat/core/Solver.h
          HINTS ${MINISAT_INCLUDE_DIRS}
          PATH_SUFFIXES minisat minisat2 )
message(STATUS "found: MINISAT_INCLUDE_DIR: ${MINISAT_INCLUDE_DIR}")

message(STATUS "Finding minisat libs...")
message(STATUS "looking at:  ${MINISAT_LIBDIR}")
find_library(MINISAT_LIBRARY NAMES minisat minisat2
         HINTS ${MINISAT_LIBDIR} ${MINISAT_LIBDIR}/lib ${MINISAT_LIBRARY_DIRS} )
message(STATUS "found: MINISAT_LIBRARY: ${MINISAT_LIBRARY}")

set(MINISAT_LIBRARIES ${MINISAT_LIBRARY} )
set(MINISAT_INCLUDE_DIRS ${MINISAT_INCLUDE_DIR} )

include(FindPackageHandleStandardArgs)
# handle the QUIETLY and REQUIRED arguments and set MINISAT_FOUND to TRUE
# if all listed variables are set
find_package_handle_standard_args(minisat  DEFAULT_MSG
                                  MINISAT_LIBRARY MINISAT_INCLUDE_DIR)

mark_as_advanced(MINISAT_INCLUDE_DIR MINISAT_LIBRARY )
