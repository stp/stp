# This macro creates a true static library bundle with debug and release configurations
# TARGET - the output library, or target, that you wish to contain all of the object files
# CONFIGURATION - DEBUG, RELEASE or ALL
# LIBRARIES - a list of all of the static libraries you want merged into the TARGET
#
# Example use:
#   MERGE_STATIC_LIBRARIES (mytarget ALL "${MY_STATIC_LIBRARIES}")
#
# NOTE: When you call this script, make sure you quote the argument to LIBRARIES if it is a list!

macro (MERGE_STATIC_LIBRARIES TARGET CONFIGURATION LIBRARIES)
	if (WIN32)
		# On Windows you must add aditional formatting to the LIBRARIES variable as a single string for the windows libtool
		# with each library path wrapped in "" in case it contains spaces
		string (REPLACE ";" "\" \"" LIBS "${LIBRARIES}")
		set (LIBS \"${LIBS}\")

		if(${CONFIGURATION} STREQUAL "DEBUG")
			set_property (TARGET ${TARGET} APPEND PROPERTY STATIC_LIBRARY_FLAGS_DEBUG "${LIBS}")
		elseif (${CONFIGURATION} STREQUAL "RELEASE")
			set_property (TARGET ${TARGET} APPEND PROPERTY STATIC_LIBRARY_FLAGS_RELEASE "${LIBS}")
		elseif (${CONFIGURATION} STREQUAL "RELWITHDEBINFO")
			set_property (TARGET ${TARGET} APPEND PROPERTY STATIC_LIBRARY_FLAGS_RELWITHDEBINFO "${LIBS}")
		elseif (${CONFIGURATION} STREQUAL "ALL")
			set_property (TARGET ${TARGET} APPEND PROPERTY STATIC_LIBRARY_FLAGS "${LIBS}")
		else (${CONFIGURATION} STREQUAL "DEBUG")
			message (FATAL_ERROR "Be sure to set the CONFIGURATION argument to DEBUG, RELEASE or ALL")
		endif(${CONFIGURATION} STREQUAL "DEBUG")
	elseif (APPLE AND ${CMAKE_GENERATOR} STREQUAL "Xcode")
		# iOS and OSX platforms with Xcode need slighly less formatting
		string (REPLACE ";" " " LIBS "${LIBRARIES}")

		if(${CONFIGURATION} STREQUAL "DEBUG")
			set_property (TARGET ${TARGET} APPEND PROPERTY STATIC_LIBRARY_FLAGS_DEBUG "${LIBS}")
		elseif (${CONFIGURATION} STREQUAL "RELEASE")
			set_property (TARGET ${TARGET} APPEND PROPERTY STATIC_LIBRARY_FLAGS_RELEASE "${LIBS}")
		elseif (${CONFIGURATION} STREQUAL "RELWITHDEBINFO")
			set_property (TARGET ${TARGET} APPEND PROPERTY STATIC_LIBRARY_FLAGS_RELWITHDEBINFO "${LIBS}")
		elseif (${CONFIGURATION} STREQUAL "ALL")
			set_property (TARGET ${TARGET} APPEND PROPERTY STATIC_LIBRARY_FLAGS "${LIBS}")
		else (${CONFIGURATION} STREQUAL "DEBUG")
			message (FATAL_ERROR "Be sure to set the CONFIGURATION argument to DEBUG, RELEASE or ALL")
		endif(${CONFIGURATION} STREQUAL "DEBUG")
	elseif (UNIX)
		# Posix platforms, including Android, require manual merging of static libraries via a special script
		set (LIBRARIES ${LIBRARIES})

		if (NOT CMAKE_BUILD_TYPE)
			message (FATAL_ERROR "To use the MergeStaticLibraries script on Posix systems, you MUST define your CMAKE_BUILD_TYPE")
		endif (NOT CMAKE_BUILD_TYPE)
		
		set (MERGE OFF)

		# We need the debug postfix on posix systems for the merge script
		string (TOUPPER ${CMAKE_BUILD_TYPE} BUILD_TYPE)
		if (${BUILD_TYPE} STREQUAL ${CONFIGURATION} OR ${CONFIGURATION} STREQUAL "ALL")
			if (${BUILD_TYPE} STREQUAL "DEBUG")
				get_target_property (TARGETLOC ${TARGET} LOCATION_DEBUG)
			else ()
				get_target_property (TARGETLOC ${TARGET} LOCATION)
			endif ()
			set (MERGE ON)
        endif()

		# Setup the static library merge script
		if (NOT MERGE)
			message (STATUS "MergeStaticLibraries ignores mismatch betwen BUILD_TYPE=${BUILD_TYPE} and CONFIGURATION=${CONFIGURATION}")
			message(STATUS "damn")
		else (NOT MERGE)
			configure_file (
				${PROJECT_SOURCE_DIR}/cmake/modules/PosixMergeStaticLibraries.cmake.in 
				${CMAKE_CURRENT_BINARY_DIR}/PosixMergeStaticLibraries-${TARGET}.cmake @ONLY
			)
			add_custom_target(${TARGET} ALL COMMENT "Copying binaries from subdirs to build directory")
			add_custom_command (TARGET ${TARGET} POST_BUILD
				COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/PosixMergeStaticLibraries-${TARGET}.cmake
			)
			message(STATUS "OK ${TARGET} command added")
		endif (NOT MERGE)
	endif (WIN32)
endmacro (MERGE_STATIC_LIBRARIES)
