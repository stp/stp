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

# Create list of objects
set(stp_lib_objects "")
foreach(target ${stp_lib_targets})
    list(APPEND stp_lib_objects $<TARGET_OBJECTS:${target}>)
endforeach()

add_library(libstp ${stp_lib_objects})
set(stp_lib_output_dir ${PROJECT_BINARY_DIR}/lib)
set_target_properties(libstp PROPERTIES 
                        OUTPUT_NAME stp    
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
