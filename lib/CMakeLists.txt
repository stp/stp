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

# Enable symbol exports
add_definitions(-D STP_EXPORTS)

add_subdirectory(Globals)
add_subdirectory(AST)
add_subdirectory(AbsRefineCounterExample)
add_subdirectory(Simplifier)
add_subdirectory(Printer)
add_subdirectory(Parser)
add_subdirectory(Interface)
add_subdirectory(extlib-abc)
add_subdirectory(extlib-constbv)
add_subdirectory(STPManager)
add_subdirectory(ToSat)
add_subdirectory(Sat)
add_subdirectory(Util)


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
    tosat
    sat
    simplifier
    constantbv
    abc
    cinterface
    cppinterface
    parser
    printer
    util
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
        message("Adding public header(s) ${TARGETS_PUBLIC_HEADERS} to target libstp")
    endif()
endforeach()

if (STATICCOMPILE)
    add_library(libstp STATIC
        ${stp_lib_objects}
    )
else()
    add_library(libstp SHARED
        ${stp_lib_objects}
    )
endif()

# Set the public header so it will be installed
set_target_properties(libstp
    PROPERTIES
    OUTPUT_NAME stp
    PUBLIC_HEADER "${PROJECT_SOURCE_DIR}/include/stp/c_interface.h"
    VERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
    SOVERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
)


# -----------------------------------------------------------------------------
# On non-windows systems a built static library cannot have another static
# library linked to it. So this does not cause the Boost libraries to be
# added to ``libstp.a``. Instead what this does is tell CMake that anything
# that we built that uses the ``libstp`` target should also link in these
# Boost libraries.
#
# So the stp executable and any clients of libstp that use the exported CMake
# targets (e.g. examples/simple) will know what to link in.
#
# Clients of libstp that don't use CMake will have to link the Boost libraries
# in manually.
# -----------------------------------------------------------------------------
set(libstp_link_libs ${Boost_LIBRARIES} ${MINISAT_LIBRARIES})
if (USE_CRYPTOMINISAT)
    if (STATICCOMPILE)
      set(libstp_link_libs
        ${libstp_link_libs}
        ${CRYPTOMINISAT5_STATIC_LIBRARIES}
        ${CRYPTOMINISAT5_STATIC_LIBRARIES_DEPS})
    else()
      set(libstp_link_libs
        ${libstp_link_libs}
        ${CRYPTOMINISAT5_LIBRARIES})
    endif()
endif()

target_link_libraries(libstp
    LINK_PUBLIC ${libstp_link_libs}
)

install(TARGETS libstp
    EXPORT ${STP_EXPORT_NAME}
    LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR}
    ARCHIVE DESTINATION ${CMAKE_INSTALL_LIBDIR}
    PUBLIC_HEADER DESTINATION include/stp
)
