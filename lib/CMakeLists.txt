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

# Symbol visibility, see the DLL_PUBLIC block in include/stp/Util/Attributes.h
# (duplicated in include/stp/c_interface.h). Both macros only ever do anything
# under MSVC; the GNU/clang branch of that block tests neither of them, so on
# every non-MSVC build these definitions are inert.
#
# STP_EXPORTS means "this translation unit is part of libstp", as opposed to a
# client compiling against the installed headers. It must reach every source
# that goes into the library, which is all of lib/ and its subdirectories --
# hence directory scope here, ahead of the add_subdirectory() calls that create
# the object libraries. It is deliberately not set for tools/, bindings/ or the
# tests: those are clients of the library and want the import side.
#
# This used to read add_definitions(-D STP_EXPORTS). CMake's -D handling does
# not match a bare -D followed by a separate argument, so neither token became a
# compile definition; both fell through to the directory's COMPILE_OPTIONS and
# only reached the compiler because they happened to stay adjacent on the
# command line -- invisible to COMPILE_DEFINITIONS and to anything that inspects
# it.
add_compile_definitions(STP_EXPORTS)

# STP_SHARED_LIB means "libstp is a DLL". Only then may the __declspec arms be
# used: a static MSVC build that saw __declspec(dllimport) would fail to link,
# which is why the #else fallback to an empty DLL_PUBLIC is the correct one for
# static and must stay reachable. STATICCOMPILE forces BUILD_SHARED_LIBS OFF, so
# static builds (including the Windows CI job) keep the empty expansion.
#
# Note this is currently dormant: no shared MSVC build of STP is produced, so
# nothing has exercised the __declspec arms.
if (BUILD_SHARED_LIBS)
    add_compile_definitions(STP_SHARED_LIB)
endif()

add_subdirectory(Globals)
add_subdirectory(AST)
add_subdirectory(AbsRefineCounterExample)
add_subdirectory(Extensionality)
add_subdirectory(UninterpretedFunctions)
add_subdirectory(FloatBlaster)
add_subdirectory(Simplifier)
add_subdirectory(Printer)
add_subdirectory(Parser)
add_subdirectory(Interface)
add_subdirectory(extlib-constbv)
add_subdirectory(STPManager)
add_subdirectory(ToSat)
add_subdirectory(Sat)
add_subdirectory(Incremental)
add_subdirectory(Util)
add_subdirectory(NodeFactory)



# FIXME: Do we need all these targets
# in the client library? Maybe
# some targets should just link directly
# the stp binary and not be in the client
# library?
set(stp_lib_targets
    stpglobals
    AST
    stpmgr
    abstractionrefinement
    extensionality
    uninterpretedfunctions
    tosat
    sat
    incremental
    floatblaster
    simplifier
    constantbv
    cinterface
    cppinterface
    parser
    printer
    util
    nodefactories
    ${PLATFORM_COMPAT_LIBRARIES}
)

# Create list of objects and gather list of
# associated public headers.
set(stp_lib_objects "")
set(stp_public_headers "")
foreach(target ${stp_lib_targets})
    list(APPEND stp_lib_objects $<TARGET_OBJECTS:${target}>)

    get_target_property(TARGETS_PUBLIC_HEADERS ${target} PUBLIC_HEADER)
    if (EXISTS "${TARGETS_PUBLIC_HEADERS}")
        list(APPEND stp_public_headers "${TARGETS_PUBLIC_HEADERS}")
        message("Adding public header(s) ${TARGETS_PUBLIC_HEADERS} to target stp")
    endif()
endforeach()

if(CMAKE_GENERATOR STREQUAL Xcode)
    # XCode has a serious bug where the XCode project produces an invalid target that will not get
    # linked if it consists only of objects from object libraries, it will not generate any
    # products (executables, libraries). The only work around is to add a dummy source
    # file to the library definition. This is an XCode, not a CMake bug.
    # see https://itk.org/Bug/view.php?id=14044
    set(XCODE_DUMMY_FILE "${CMAKE_BINARY_DIR}/xcode_dummy.cpp")
    file(WRITE ${XCODE_DUMMY_FILE} "")
    list(APPEND stp_lib_objects ${XCODE_DUMMY_FILE})
endif()

add_library(stp
    ${stp_lib_objects}
)

# The directory-scope definitions above cover the object libraries this target
# is assembled from. Repeating STP_EXPORTS as a PRIVATE requirement keeps it
# attached to the library target itself rather than only to the directory, so it
# still applies if sources are ever added to stp directly -- and, more to the
# point, it documents that STP_EXPORTS is a build-of-the-library requirement and
# must never become part of the link interface.
#
# STP_SHARED_LIB is the opposite: consumers need it too. A client compiling
# against the installed c_interface.h must see STP_SHARED_LIB (so DLL_PUBLIC is
# a __declspec) with STP_EXPORTS unset (so it resolves to dllimport). Putting it
# in the INTERFACE requirements records it in the exported STPTargets.cmake, so
# anything that links the imported stp target picks it up automatically, and
# in-tree consumers (tools/, bindings/, tests/) get it for free.
target_compile_definitions(stp PRIVATE STP_EXPORTS)
if (BUILD_SHARED_LIBS)
    target_compile_definitions(stp INTERFACE STP_SHARED_LIB)
endif()
target_include_directories(stp INTERFACE
    $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/include>
    $<BUILD_INTERFACE:${PROJECT_BINARY_DIR}/include>
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
)

# Set the public header so it will be installed
set_target_properties(stp PROPERTIES
    PUBLIC_HEADER "${PROJECT_SOURCE_DIR}/include/stp/c_interface.h;${PROJECT_SOURCE_DIR}/include/stp/fp.hpp;${PROJECT_SOURCE_DIR}/include/stp/uf.hpp"
    VERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
    SOVERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
)

if(WIN32)
    set_target_properties(stp PROPERTIES
        OUTPUT_NAME stpwin
    )
else()
    set_target_properties(stp PROPERTIES
        OUTPUT_NAME stp
    )
endif()


# Configure ABC library build options
set(READLINE_FOUND FALSE CACHE BOOL "Disable readline for ABC" FORCE)
set(ABC_SKIP_TESTS ON CACHE BOOL "Skip ABC tests" FORCE)

# ABC has no CMake cache variables for the options below: its CMakeLists runs
# ABC's own Makefile to extract the source list and flags, forwarding only the
# readline and namespace settings. The Makefile gates these on ifndef, and make
# honours the environment for that, which the inherited environment of ABC's
# execute_process() reaches. So set them here rather than patching the submodule.
#
# CUDD: pulls in nine BDD modules (src/bdd/{cudd,extrab,dsd,epd,mtr,reo,cas,bbr,
# llb}), 123 files and ~110k lines that STP never uses -- we only touch AIG
# construction, Dar rewriting and CNF derivation. Safe for our include set:
# ABC_USE_CUDD guards only Abc_Frame_t's DdManager field in base/main/mainInt.h
# and three Kit_*ToBdd declarations in bool/kit/kit.h, and neither header is
# reachable from aig/aig/aig.h, opt/dar/dar.h or sat/cnf/cnf.h.
set(ENV{ABC_USE_NO_CUDD} 1)
# pthreads: every ABC file we compile that calls pthread_* guards on
# ABC_USE_PTHREADS (src/starter.c does not, but is in no module.make and is
# never built). Dropping it also keeps the macro consistent between ABC's own
# translation units and STP's, which include ABC headers without ABC's flags --
# see the note on $<TARGET_FILE:libabc-pic> below.
set(ENV{ABC_USE_NO_PTHREADS} 1)

# EXCLUDE_FROM_ALL: ABC marks libabc and libabc-pic EXCLUDE_FROM_ALL but not its
# abc executable, which links libabc (non-PIC) and so compiles all of ABC a
# second time. STP only ever links libabc-pic, pulled in by the dependency
# below; the executable is dead weight worth ~50% of ABC's build cost.
#
# BUILD_SHARED_LIBS: ABC's add_library() calls name neither STATIC nor SHARED,
# so they follow BUILD_SHARED_LIBS, which defaults to ON. That made libabc-pic a
# 17MB shared library which libstp.so recorded as a NEEDED entry even though ABC
# has no install() rules, so an installed libstp.so named a library that was
# never installed; only the build-tree RUNPATH kept it working. Building it as an
# archive links the ABC code into libstp.so instead, which is self-contained and
# installable. libabc-pic is already POSITION_INDEPENDENT_CODE, which is what
# linking it into a shared library needs. Note the archive does not shrink the
# result much: ABC is interconnected enough that our ~30 entry points transitively
# pull in most of it either way -- what changes is that the symbols stop being
# public, see --exclude-libs at the bottom of this file.
# The normal variable shadows the cache entry for this scope only; unset()
# restores the cached value for the rest of lib/.
set(BUILD_SHARED_LIBS OFF)
add_subdirectory(extlib-abc EXCLUDE_FROM_ALL)
unset(BUILD_SHARED_LIBS)

# ABC is a vendored, upstream submodule (berkeley-abc/abc) whose warnings we
# don't control, so keep WERROR from turning them into build failures. The
# -Wno-error comes after the global -Werror, so it wins for these targets only;
# STP's own code stays gated on warnings.
if (WERROR AND NOT MSVC)
    foreach(_abc_target abc libabc libabc-pic)
        if (TARGET ${_abc_target})
            target_compile_options(${_abc_target} PRIVATE -Wno-error)
        endif()
    endforeach()
endif()

# Give each ABC function and data object its own section so the --gc-sections
# below can drop the ones we never call. Applied to ABC only: the dead weight is
# all on this side, and confining it keeps STP's own codegen unchanged.
if (NOT MSVC)
    foreach(_abc_target libabc libabc-pic)
        if (TARGET ${_abc_target})
            target_compile_options(${_abc_target} PRIVATE
                -ffunction-sections -fdata-sections)
        endif()
    endforeach()
endif()

# Link to the ABC library target
add_dependencies(stp libabc-pic)
# Use the full path to the library instead of the target name for export
# compatibility. Note this bypasses ABC's PUBLIC usage requirements, so the
# flags ABC sets for its own translation units do not reach STP's: any ABC
# option that changes a declaration in aig.h, dar.h or cnf.h would have to be
# defined for STP's sources too.
set(stp_link_libs ${MINISAT_LIBRARIES} $<TARGET_FILE:libabc-pic>)

# LibBF is not optional -- folding the real literals in floating-point input is
# part of every build -- so it is always on the link line. Named by path rather
# than by its imported target, for the export-compatibility reason given over
# $<TARGET_FILE:libabc-pic> above: a target name here would be written into
# STPTargets.cmake, where no consumer has a target to resolve it against. The
# target itself is used where it does belong, on the one object library that
# compiles against the header (lib/FloatBlaster).
set(stp_link_libs ${stp_link_libs} ${LIBBF_LIBRARY})

# RunTimes reads the process's peak memory through GetProcessMemoryInfo,
# which lives in psapi. ABC's sclLiberty.c calls PathMatchSpec from
# shlwapi; MSVC picks that library up through ABC's #pragma comment(lib),
# which MinGW's linker ignores, so it has to be named here.
if (WIN32)
    set(stp_link_libs ${stp_link_libs} psapi shlwapi)
endif()

if (USE_CRYPTOMINISAT)
    if (STATICCOMPILE)
      set(stp_link_libs
        ${stp_link_libs}
        ${CRYPTOMINISAT5_STATIC_LIBRARIES}
        ${CRYPTOMINISAT5_STATIC_LIBRARIES_DEPS})
    else()
      set(stp_link_libs
        ${stp_link_libs}
        ${CRYPTOMINISAT5_LIBRARIES})
    endif()
endif()

if (USE_RISS)
    set(stp_link_libs
        ${stp_link_libs} ${RISS_LIBRARY})
endif()

# By path, for the same reason as LibBF above; lib/Sat links the CaDiCaL target
# itself, which is what carries the include directory to the compile.
if (USE_CADICAL)
    set(stp_link_libs
        ${stp_link_libs} ${CADICAL_LIBRARY})
endif()

# PRIVATE, not LINK_PUBLIC: these are implementation details of libstp, and
# naming them in the link interface put them in the exported STPTargets.cmake,
# where they were unusable - $<TARGET_FILE:libabc-pic> names a target no
# consumer has, and the minisat entry was an absolute path into whichever build
# tree happened to produce the package. find_package(STP) failed outright on
# the generator expression, so no external project could link STP at all; see
# examples/simple. A shared libstp needs none of this propagated anyway: the
# ABC archive is linked into the library (with its symbols localised, see
# --exclude-libs below) and minisat is picked up transitively through
# DT_NEEDED.
target_link_libraries(stp
    PRIVATE ${stp_link_libs}
)

# SymFPU reaches further than the sources that name it. It is header-only, and
# stp/FloatBlaster/symbolic_fp.h -- an internal header, but one any part of the
# tree may include -- includes symfpu/core/unpackedFloat.h. So the tools and
# tests that include it need SymFPU's include directory too, and listing them
# one by one is a list that rots: it was already wrong by two targets when
# first written.
#
# BUILD_INTERFACE, so it reaches everything in this build that links stp and
# nothing at all in the exported STPTargets.cmake -- SymFPU is a target no
# consumer of an installed STP has, and none of them need it: the headers STP
# installs (c_interface.h, fp.hpp, uf.hpp) do not include it.
target_link_libraries(stp INTERFACE $<BUILD_INTERFACE:SymFPU>)

# ABC is interconnected enough that satisfying our ~30 entry points transitively
# drags in most of the archive, including its vendored zlib and bzlib (gzopen,
# inflate, deflate, crc32, BZ2_*). Left with default visibility those would be
# exported from libstp.so, where they can serve requests that belong to the real
# libz used by minisat and CryptoMiniSat. --exclude-libs makes symbols taken from
# static archives local to the output, so libstp.so exports only STP's own API
# and the ABC code it uses stays private. GNU ld and lld only; on Apple and
# Windows this is skipped, and for a static libstp there is no link step to
# apply it to.
#
# --gc-sections then discards the ABC sections nothing reaches. Linking ABC as an
# archive puts its code inside libstp.so, and the transitive pull-in is most of
# ABC, so without this the library grows from ~2MB to ~18MB; with it, ~3.4MB.
# Hiding the symbols first is what makes the collection effective -- an exported
# symbol is a GC root.
if (BUILD_SHARED_LIBS AND NOT APPLE AND NOT WIN32 AND NOT MSVC)
    set_property(TARGET stp APPEND_STRING PROPERTY
        LINK_FLAGS " -Wl,--exclude-libs,ALL -Wl,--gc-sections")
endif()

install(TARGETS stp
    EXPORT ${STP_EXPORT_NAME}
    LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    RUNTIME DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_FULL_INCLUDEDIR}/stp"
)
