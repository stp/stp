# Installs what STP consumes from a MiniSat build tree, and only that: the
# library and the public headers. Run as MiniSat-EP's INSTALL_COMMAND by
# cmake/FindMiniSat.cmake, which passes SRC, BIN, DST and LIBNAME.
#
# Upstream's own install rule names minisat_core and minisat_simp alongside the
# library. They are command-line programs STP never runs, and building them is
# not free: MiniSat puts -static on its executables whenever the library is
# static, so producing them needs a static libz, libstdc++ and libc present on
# the build machine. A build of STP has no reason to require those, and on a
# distribution that does not ship libz.a it cannot have them at all -- the
# shell script this replaces failed outright there. So build the library target
# alone and install it here.

if(NOT SRC OR NOT BIN OR NOT DST OR NOT LIBNAME)
    message(FATAL_ERROR "minisat-install.cmake needs -DSRC= -DBIN= -DDST= -DLIBNAME=")
endif()

# GLOB_RECURSE because a multi-config generator puts the archive in a
# per-configuration subdirectory of the build tree rather than at its root.
file(GLOB_RECURSE _found "${BIN}/${LIBNAME}")
if(NOT _found)
    message(FATAL_ERROR "No ${LIBNAME} anywhere under ${BIN}")
endif()
list(GET _found 0 _lib)
file(COPY "${_lib}" DESTINATION "${DST}/lib")

# The four directories upstream's install rule publishes, filtered to headers
# the same way it filters them.
foreach(_dir mtl utils core simp)
    file(GLOB _hdrs "${SRC}/minisat/${_dir}/*.h")
    if(_hdrs)
        file(COPY ${_hdrs} DESTINATION "${DST}/include/minisat/${_dir}")
    endif()
endforeach()

# EOF
