# Installs what STP consumes from a Riss build tree. Run as Riss-EP's
# INSTALL_COMMAND by cmake/FindRiss.cmake, which passes SRC, BIN, DST and
# LIBNAME.
#
# Riss has no install rules of its own, which is why STP used to consume it
# from a checkout: RISS_DIR named the source tree for the headers and its
# build/ subdirectory for the archive. Copying both into the dependency prefix
# instead is what lets a Riss that one build directory produced be found by the
# next one, the same as every other dependency here.

if(NOT SRC OR NOT BIN OR NOT DST OR NOT LIBNAME)
    message(FATAL_ERROR "riss-install.cmake needs -DSRC= -DBIN= -DDST= -DLIBNAME=")
endif()

file(GLOB_RECURSE _found "${BIN}/${LIBNAME}")
if(NOT _found)
    message(FATAL_ERROR "No ${LIBNAME} anywhere under ${BIN}")
endif()
list(GET _found 0 _lib)
file(COPY "${_lib}" DESTINATION "${DST}/lib")

# Every header, at the path it is included by: STP says
# #include "riss/core/Solver.h", so the checkout root is the include root, and
# that header reaches a good deal of the rest of the tree. Copying the lot is
# both simpler and safer than trying to work out the closure -- Riss publishes
# no list, and a missing header would only show up as a compile error in
# whichever STP build first needed it.
file(GLOB_RECURSE _headers RELATIVE "${SRC}" "${SRC}/*.h" "${SRC}/*.hh")
foreach(_header ${_headers})
    get_filename_component(_dir "${_header}" DIRECTORY)
    file(COPY "${SRC}/${_header}" DESTINATION "${DST}/include/${_dir}")
endforeach()

# EOF
