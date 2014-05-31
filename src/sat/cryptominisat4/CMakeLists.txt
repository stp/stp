include_directories(
    ${PROJECT_SOURCE_DIR}
    ${Boost_INCLUDE_DIRS}
)

set(cryptominisat4_public_headers "")

set(cryptoms_lib_files
    cnf.cpp
    propengine.cpp
    varreplacer.cpp
    clausecleaner.cpp
    clauseusagestats.cpp
    prober.cpp
    simplifier.cpp
    subsumestrengthen.cpp
    clauseallocator.cpp
    sccfinder.cpp
    solverconf.cpp
    vivifier.cpp
    strengthener.cpp
    calcdefpolars.cpp
    solutionextender.cpp
    completedetachreattacher.cpp
    searcher.cpp
    solver.cpp
    gatefinder.cpp
    sqlstats.cpp
    implcache.cpp
    stamp.cpp
    compfinder.cpp
    comphandler.cpp
    hyperengine.cpp
    subsumeimplicit.cpp
    cryptominisat.cpp
    cleaningstats.cpp
    datasync.cpp
    reducedb.cpp
)

set(cryptoms_lib_link_libs "")
# if (M4RI_FOUND)
#     include_directories(${M4RI_INCLUDE_DIRS})
#
#     add_library(m4ri SHARED IMPORTED)
#     set_property(TARGET m4ri PROPERTY IMPORTED_LOCATION ${M4RI_LIBRARIES})
#
#     SET(cryptoms_lib_files ${cryptoms_lib_files} xorfinder.cpp)
#     SET(cryptoms_lib_link_libs ${cryptoms_lib_link_libs} m4ri)
# endif (M4RI_FOUND)

add_library(cryptominisat4 OBJECT ${cryptoms_lib_files})

# target_link_libraries(cryptominisat4
#     ${cryptoms_lib_link_libs}
# )
