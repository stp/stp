# Installs what STP consumes from an ABC build tree: the position-independent
# archive and the headers. Run as ABC-EP's INSTALL_COMMAND by
# cmake/FindABC.cmake, which passes SRC, BIN, DST and LIBNAME.
#
# ABC has no install rules at all -- its CMakeLists declares two libraries,
# both EXCLUDE_FROM_ALL, and stops -- which is why STP used to add it with
# add_subdirectory() and link the archive straight out of the build tree.

if(NOT SRC OR NOT BIN OR NOT DST OR NOT LIBNAME)
    message(FATAL_ERROR "abc-install.cmake needs -DSRC= -DBIN= -DDST= -DLIBNAME=")
endif()

file(GLOB_RECURSE _found "${BIN}/${LIBNAME}")
if(NOT _found)
    message(FATAL_ERROR "No ${LIBNAME} anywhere under ${BIN}")
endif()
list(GET _found 0 _lib)
file(COPY "${_lib}" DESTINATION "${DST}/lib")

# Every header under src/, at the path it is included by: STP says
# #include "aig/aig/aig.h", "opt/dar/dar.h", "sat/cnf/cnf.h" and so on, so
# src/ is the include root. Copying the lot rather than the closure of those
# three, because ABC publishes no list of its public headers, and a missing one
# would surface only as a compile error in whichever STP build first needed it.
file(GLOB_RECURSE _headers RELATIVE "${SRC}/src" "${SRC}/src/*.h")
foreach(_header ${_headers})
    get_filename_component(_dir "${_header}" DIRECTORY)
    file(COPY "${SRC}/src/${_header}" DESTINATION "${DST}/include/${_dir}")
endforeach()

# EOF
