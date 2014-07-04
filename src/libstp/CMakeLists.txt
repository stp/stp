# Targets to include in libstp

# FIXME: Do we need all these targets
# in the client library? Maybe
# some targets should just link directly
# the stp binary and not be in the client
# library?
set(stp_lib_targets
    AST
    globalstp
    stpmgr
    abstractionrefinement
    tosat
    sat
    minisat2
    cryptominisat2
    simplifier
    constantbv
    abc
    cinterface
    cppinterface
    parser
    printer
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

add_library(libstp ${stp_lib_objects})

set_target_properties(libstp PROPERTIES
                        OUTPUT_NAME stp
                        PUBLIC_HEADER "${stp_public_headers}"
                     )

# -----------------------------------------------------------------------------
# Support building both static and dynamic library
# -----------------------------------------------------------------------------
if (BUILD_SHARED_LIBS AND ALSO_BUILD_STATIC_LIB)
  add_library(libstp_static STATIC ${stp_lib_objects})

  set_target_properties(libstp_static PROPERTIES
                          OUTPUT_NAME stp
                       )

  install(TARGETS libstp_static
              EXPORT ${STP_EXPORT_NAME}
              LIBRARY DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
              ARCHIVE DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
         )
endif()

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
set(libstp_link_libs ${Boost_LIBRARIES})
if (USE_CRYPTOMINISAT4)
    set(libstp_link_libs ${libstp_link_libs} ${CRYPTOMINISAT4_LIBRARIES})
endif()
target_link_libraries(libstp ${libstp_link_libs})


# -----------------------------------------------------------------------------
# Copy public headers into build directory include directory.
# This is done so that projects that use STP as external project (not via CMake)
# can find the public header files.
# -----------------------------------------------------------------------------
set(HEADER_DEST "${CMAKE_BINARY_DIR}/include/stp")
add_custom_target(CopyPublicHeaders ALL)
foreach(public_header ${stp_public_headers})
    get_filename_component(HEADER_NAME ${public_header} NAME)
    add_custom_command(TARGET CopyPublicHeaders PRE_BUILD
                       COMMAND ${CMAKE_COMMAND} -E make_directory
                               "${HEADER_DEST}"
                       COMMAND ${CMAKE_COMMAND} -E echo
                       "Copying ${HEADER_NAME} to ${HEADER_DEST}"
                       COMMAND ${CMAKE_COMMAND} -E
                           copy_if_different
                           ${public_header}
                           "${HEADER_DEST}"
                      )
endforeach()

install(TARGETS libstp
            EXPORT ${STP_EXPORT_NAME}
            LIBRARY DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
            ARCHIVE DESTINATION "${CMAKE_INSTALL_PREFIX}/lib"
            PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_PREFIX}/include/stp"
       )
