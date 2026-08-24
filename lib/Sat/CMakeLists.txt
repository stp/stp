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

set(sat_lib_to_add
    SATSolverFactory.cpp
)

if (USE_MINISAT)
    set(sat_lib_to_add ${sat_lib_to_add}
        MinisatCore.cpp
        SimplifyingMinisat.cpp
    )
endif()

if (USE_CRYPTOMINISAT)
    set(sat_lib_to_add ${sat_lib_to_add} CryptoMinisat5.cpp)
endif()

if (USE_CADICAL)
    set(sat_lib_to_add ${sat_lib_to_add} Cadical.cpp)
endif()


if (USE_RISS)
    set(sat_lib_to_add ${sat_lib_to_add} RissCore.cpp)
endif()

add_library(sat OBJECT ${sat_lib_to_add})

# cryptominisat.h includes gmpxx.h, and the cryptominisat5 imported target
# carries that requirement as PkgConfig::GMP in its link interface. Linking
# the object library to the target is what brings GMP's include directory to
# the compile of CryptoMinisat5.cpp; STP has no GMP lookup of its own. Only
# the usage requirements travel: sat's objects reach libstp through
# $<TARGET_OBJECTS:sat>, and libstp names the target on its own link line.
if (USE_CRYPTOMINISAT)
    target_link_libraries(sat PRIVATE ${CRYPTOMINISAT5_LIBRARIES})
endif()

# The target does not carry CryptoMiniSat's own include directory, only
# CRYPTOMINISAT5_INCLUDE_DIRS does -- and that directory is given to the one
# file that includes cryptominisat.h rather than to the target or the
# directory. That is not tidiness.
#
# CryptoMiniSat >= 5.14 builds and installs its own bundled CaDiCaL into its
# prefix, where the header lands as include/cadical/cadical.hpp: the exact
# spelling include/stp/Sat/Cadical.h uses to reach the CaDiCaL that CADICAL_DIR
# or STP_DEP_DIR named. Anything wider than one file therefore puts a second,
# older cadical/cadical.hpp on the search path of files that want STP's, and
# the compiler prefers the wrong one twice over: an include_directories() is
# emitted ahead of any target's own directories, and the CaDiCaL target
# contributes its directory as -isystem, which every -I outranks whatever the
# order. What that produced was Cadical.cpp compiled against
# CryptoMiniSat's 2.1.3 header while the configure had already read 3.0.1 from
# the checkout and defined STP_CADICAL_HAS_FACTOR -- an error on
# declare_more_variables, and, for any API that had happened to line up, a
# silent header/library mismatch instead. Cadical.h asserts the pairing so a
# future recurrence says so; this keeps it from arising.
if (USE_CRYPTOMINISAT)
    set_source_files_properties(CryptoMinisat5.cpp PROPERTIES
        INCLUDE_DIRECTORIES "${CRYPTOMINISAT5_INCLUDE_DIRS}")
endif()

# Likewise for CaDiCaL, whose imported target carries the (staged) include
# directory holding cadical/cadical.hpp. This replaces a project-wide
# include_directories(); only Cadical.cpp and SATSolverFactory.cpp reach that
# header. The archive itself is named on libstp's own link line, in
# lib/CMakeLists.txt, alongside the other backends.
if (USE_CADICAL)
    target_link_libraries(sat PRIVATE CaDiCaL)
endif()

# And for MiniSat, whose target additionally carries zlib: its public headers
# include zlib.h, so anything compiling against it needs zlib's include
# directory as well as its own.
if (USE_MINISAT)
    target_link_libraries(sat PRIVATE MiniSat)
endif()

# And Riss, whose target carries its headers as SYSTEM headers: Riss is
# upstream code whose warnings STP does not control, and it is consumed as
# headers rather than as a target STP builds, so there is no target to hang a
# -Wno-error on. Without that a WERROR build fails inside Riss's own headers,
# some ninety diagnostics across a dozen files. STP's own code in RissCore.cpp
# stays gated on warnings.
if (USE_RISS)
    target_link_libraries(sat PRIVATE Riss)
endif()
