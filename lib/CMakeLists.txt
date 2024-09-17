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
add_subdirectory(abc)
add_subdirectory(extlib-constbv)
add_subdirectory(STPManager)
add_subdirectory(ToSat)
add_subdirectory(Sat)
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
    tosat
    sat
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
    STATIC
    ${stp_lib_objects}
)

# Set the public header so it will be installed
set_target_properties(stp PROPERTIES
    PUBLIC_HEADER "${PROJECT_SOURCE_DIR}/include/stp/c_interface.h"
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


# -----------------------------------------------------------------------------
# On non-windows systems a built static library cannot have another static
# library linked to it. So this does not cause the Boost libraries to be
# added to ``stp.a``. Instead what this does is tell CMake that anything
# that we built that uses the ``stp`` target should also link in these
# Boost libraries.
#
# So the stp executable and any clients of stp that use the exported CMake
# targets (e.g. examples/simple) will know what to link in.
#
# Clients of stp that don't use CMake will have to link the Boost libraries
# in manually.
# -----------------------------------------------------------------------------
# https://gitlab.kitware.com/cmake/cmake/-/issues/15415#note_633938
set(stp_link_libs ${MINISAT_LIBRARIES} $<BUILD_LOCAL_INTERFACE:libabc>)

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
        ${stp_link_libs} -lriss-coprocessor)
endif()

target_link_libraries(stp
    LINK_PUBLIC ${stp_link_libs}
)

install(TARGETS stp
    EXPORT ${STP_EXPORT_NAME}
    LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    RUNTIME DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_FULL_INCLUDEDIR}/stp"
)
