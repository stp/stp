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


# Sort out Boost dependency
if(BUILD_SHARED_LIBS)
    message(STATUS "Boost dynamic libraries will be linked to client library") 
    target_link_libraries(libstp ${Boost_LIBRARIES}) 
else()
    message(STATUS "Boost static libraries will be embedded in client library")
    include(MergeStaticLibraries)
    MERGE_STATIC_LIBRARIES(libstp ALL "${Boost_LIBRARIES}")
endif()


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
            LIBRARY DESTINATION lib
            ARCHIVE DESTINATION lib
            PUBLIC_HEADER DESTINATION "${CMAKE_INSTALL_PREFIX}/include/stp"
       )
