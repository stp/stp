#!/bin/bash -x
# This file wraps CMake invocation for TravisCI
# so we can set different configurations via environment variables.
#
# We could modify our CMake scripts to read environment variables directly but
# that would create two ways of setting the same thing which doesn't seem like
# a good idea.

SOURCE_DIR="$1"
COMMON_CMAKE_ARGS="-G \"Unix Makefiles\" -DENABLE_TESTING:BOOL=ON -DLIT_ARGS:STRING=-v"

# Note eval is needed so COMMON_CMAKE_ARGS is expanded properly
case $STP_CONFIG in
    STATIC_LIB)
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_SHARED_LIBS:BOOL=OFF \
                   -DBUILD_STATIC_BIN:BOOL=OFF \
                   ${SOURCE_DIR}
    ;;

    DYNAMIC_LIB)
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_SHARED_LIBS:BOOL=ON \
                   -DBUILD_STATIC_BIN:BOOL=OFF \
                   -DALSO_BUILD_STATIC_LIB:BOOL=OFF \
                   ${SOURCE_DIR}
    ;;

    DYNAMIC_AND_STATIC_LIB)
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_SHARED_LIBS:BOOL=ON \
                   -DBUILD_STATIC_BIN:BOOL=OFF \
                   -DALSO_BUILD_STATIC_LIB:BOOL=ON \
                   ${SOURCE_DIR}
    ;;

    STATIC_BINARY)
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DBUILD_STATIC_BIN:BOOL=ON \
                   ${SOURCE_DIR}
    ;;

    RELEASE)
        eval cmake ${COMMON_CMAKE_ARGS} \
                   -DENABLE_ASSERTIONS:BOOL=OFF \
                   -DCMAKE_BUILD_TYPE:STRING=Release \
                   ${SOURCE_DIR}
    ;;

    *)
        echo "\"${STP_CONFIG}\" configuration not recognised"
        exit 1
esac

exit $?

