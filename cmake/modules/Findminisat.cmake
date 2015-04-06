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
