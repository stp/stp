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

# - Try to find minisat
# Once done this will define
#  MINISAT_FOUND - System has minisat
#  MINISAT_INCLUDE_DIRS - The minisat include directories
#  MINISAT_LIBRARIES - The libraries needed to use minisat
#  MINISAT_DEFINITIONS - Compiler switches required for using minisat

set(MINISAT_DEFINITIONS "")

find_path(MINISAT_INCLUDE_DIR minisat/core/Solver.h
          HINTS ${MINISAT_INCLUDE_DIRS}
          PATH_SUFFIXES minisat minisat2 )

if (Minisat_USE_STATIC_LIBS)
  message(STATUS "Finding static minisat libs...")
  macro_push_required_vars(CMAKE_FIND_LIBRARY_SUFFIXES)

  if(UNIX AND WITH_MY_LIB_STATIC)
      set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
  endif(UNIX AND WITH_MY_LIB_STATIC)
  find_library(MINISAT_LIBRARY NAMES libminisat.a libminisat2.a
             HINTS ${MINISAT_LIBDIR} ${MINISAT_LIBRARY_DIRS} )
  macro_pop_required_vars(CMAKE_FIND_LIBRARY_SUFFIXES)
else()
  message(STATUS "Finding dynamic minisat libs...")
  message(STATUS "looking at:  ${MINISAT_LIBDIR}")
  find_library(MINISAT_LIBRARY NAMES minisat minisat2
             HINTS ${MINISAT_LIBDIR} ${MINISAT_LIBRARY_DIRS} )
endif()

set(MINISAT_LIBRARIES ${MINISAT_LIBRARY} )
set(MINISAT_INCLUDE_DIRS ${MINISAT_INCLUDE_DIR} )

include(FindPackageHandleStandardArgs)
# handle the QUIETLY and REQUIRED arguments and set MINISAT_FOUND to TRUE
# if all listed variables are set
find_package_handle_standard_args(minisat  DEFAULT_MSG
                                  MINISAT_LIBRARY MINISAT_INCLUDE_DIR)

mark_as_advanced(MINISAT_INCLUDE_DIR MINISAT_LIBRARY )
