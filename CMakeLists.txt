project(STP)
cmake_minimum_required(VERSION 2.8.8 FATAL_ERROR)


if (CMAKE_MAJOR_VERSION GREATER 2)
    # FIXME: We need to find a proper way to get the LOCATION property of a target
    # when using CMake >= 3.0
    cmake_policy(SET CMP0026 OLD) # See cmake --help-policy CMP0026
endif()

# Search paths for custom CMake modules
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/modules)

set(CMAKE_INSTALL_LIBDIR lib CACHE STRING "Output directory for libraries")

set(STP_TIMESTAMPS ON CACHE BOOL "Enable build with timestamps")

# -----------------------------------------------------------------------------
# Make RelWithDebInfo the default build type if otherwise not set
# -----------------------------------------------------------------------------
set(build_types Debug Release RelWithDebInfo MinSizeRel)
if(NOT CMAKE_BUILD_TYPE)

      message(STATUS "You can choose the type of build, options are:${build_types}")
      set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE String
          "Options are ${build_types}"
          FORCE
         )

      # Provide drop down menu options in cmake-gui
      set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Doing a ${CMAKE_BUILD_TYPE} build")

# -----------------------------------------------------------------------------
# Option to enable/disable assertions
# -----------------------------------------------------------------------------

# Filter out definition of NDEBUG from the default build configuration flags.
# We will add this ourselves if we want to disable assertions
foreach (build_config ${build_types})
    string(TOUPPER ${build_config} upper_case_build_config)
    foreach (language CXX C)
        set(VAR_TO_MODIFY "CMAKE_${language}_FLAGS_${upper_case_build_config}")
        string(REGEX REPLACE "(^| )[/-]D *NDEBUG($| )"
                             " "
                             replacement
                             "${${VAR_TO_MODIFY}}"
              )
        #message("Original (${VAR_TO_MODIFY}) is ${${VAR_TO_MODIFY}} replacement is ${replacement}")
        set(${VAR_TO_MODIFY} "${replacement}" CACHE STRING "Default flags for ${build_config} configuration" FORCE)
    endforeach()
endforeach()

option(ENABLE_ASSERTIONS "Build with assertions enabled" ON)
if (ENABLE_ASSERTIONS)
    # NDEBUG was already removed.
else()
    # Note this definition doesn't appear in the cache variables.
    add_definitions(-DNDEBUG)
endif()

# -----------------------------------------------------------------------------
# Enable LLVM sanitizations.
# Note that check_cxx_compiler_flag doesn't work, a fix is needed here
# -----------------------------------------------------------------------------
macro(add_cxx_flag flagname)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}")
endmacro()

include(MacroPushRequiredVars)

option(SANITIZE "Use Clang sanitizers. This will force using clang++ as the compiler" OFF)
if (SANITIZE)
    # Set in Cache so user can tweak it later
    SET(CMAKE_CXX_COMPILER "clang++" CACHE FILEPATH "" FORCE)
    message("Forcing compiler:${CMAKE_CXX_COMPILER}")
    add_cxx_flag("-fsanitize=return")
    add_cxx_flag("-fsanitize=bounds")
    add_cxx_flag("-fsanitize=integer")
    add_cxx_flag("-fsanitize=undefined")
    add_cxx_flag("-fsanitize=float-divide-by-zero")
    add_cxx_flag("-fsanitize=integer-divide-by-zero")
    add_cxx_flag("-fsanitize=null")
    add_cxx_flag("-fsanitize=unsigned-integer-overflow")
    add_cxx_flag("-fsanitize=address")
    add_cxx_flag("-Wno-bitfield-constant-conversion")
endif()

# -----------------------------------------------------------------------------
# Let the user decide if they want to build shared or static client library.
# STP will link against this client library
# -----------------------------------------------------------------------------
option(BUILD_SHARED_LIBS "Build client library as a shared library" ON)

if (WIN32)
  # building of shared lib on windows is not done at source level
  set(BUILD_SHARED_LIBS OFF)
  message(WARNING "Disabling building of shared library on Windows")
else()
    option(BUILD_STATIC_BIN "Build a static binary (and no shared libs)" OFF)

    if (BUILD_STATIC_BIN)
        set(BUILD_SHARED_LIBS OFF)
        # Flags for the linker will be set later
    endif()
endif()

if (BUILD_SHARED_LIBS)
  option(ALSO_BUILD_STATIC_LIB "IF building shared library, also build the static library" ON)

  set(STP_SHARED_LIBRARY libstp) # Used for exporting target

  if (ALSO_BUILD_STATIC_LIB AND NOT WIN32)
    list(APPEND TARGETS_TO_EXPORT libstp_static)
    set(STP_STATIC_LIBRARY libstp_static) # Used for exporting target
  endif()

else()
  set(STP_STATIC_LIBRARY libstp) # Used for exporting target
  unset(ALSO_BUILD_STATIC_LIB CACHE) # Hide this option for ccmake and cmake-gui users
endif()

# -----------------------------------------------------------------------------
# Set the appropriate build flags
# -----------------------------------------------------------------------------
include(CheckCXXCompilerFlag)

macro(add_cxx_flag_if_supported flagname)
  check_cxx_compiler_flag("${flagname}" HAVE_FLAG_${flagname})

  if(HAVE_FLAG_${flagname})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flagname}")
  endif()
endmacro()

if(BUILD_SHARED_LIBS)
    message(STATUS "Building shared library currently broken due to mix of C++/C code")
    add_cxx_flag_if_supported("-fPIC")
endif()

check_cxx_compiler_flag("-std=c++11" HAVE_FLAG_STD_CPP11)
check_cxx_compiler_flag("-std=gnu++11" HAVE_FLAG_STD_GNUCPP11)
check_cxx_compiler_flag("-std=gnu++0x" HAVE_FLAG_STD_GNUCPP0X)
check_cxx_compiler_flag("-std=c++0x" HAVE_FLAG_STD_CPP0X)
check_cxx_compiler_flag("-stdlib=libc++" HAVE_FLAG_STDLIB_LIBCPP)

#needed for MiniSat's PRi64 to set stdc++ to 03 temporarily
check_cxx_compiler_flag("-std=c++03" HAVE_FLAG_CPP03)

if(HAVE_FLAG_STD_CPP11)
  set(CMAKE_CXX_FLAGS "-std=c++11 ${CMAKE_CXX_FLAGS}")
elseif(HAVE_FLAG_STD_GNUCPP11)
  set(CMAKE_CXX_FLAGS "-std=gnu++11 ${CMAKE_CXX_FLAGS}")
elseif(HAVE_FLAG_STD_GNUCPP0X)
  set(CMAKE_CXX_FLAGS "-std=gnu++0x ${CMAKE_CXX_FLAGS}")
elseif(HAVE_FLAG_STD_CPP0X)
  set(CMAKE_CXX_FLAGS "-std=c++0x ${CMAKE_CXX_FLAGS}")
endif()

if(APPLE AND HAVE_FLAG_STDLIB_LIBCPP)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
endif()

add_cxx_flag_if_supported("-Wall")
#add_cxx_flag_if_supported("-Wextra")
add_cxx_flag_if_supported("-pedantic")
add_cxx_flag_if_supported("-Wunused")
add_cxx_flag_if_supported("-Wsign-compare")
add_cxx_flag_if_supported("-Wtype-limits")
add_cxx_flag_if_supported("-Wuninitialized")
add_cxx_flag_if_supported("-Wno-deprecated")
add_cxx_flag_if_supported("-Wstrict-aliasing")
add_cxx_flag_if_supported("-Wpointer-arith")
add_cxx_flag_if_supported("-Wheader-guard")
add_definitions("-D__STDC_LIMIT_MACROS")

option(TUNE_NATIVE "Use -mtune=native" OFF)
if(TUNE_NATIVE)
  add_cxx_flag_if_supported("-mtune=native")
endif()



if(WIN32)
  set(FLEX_PATH_HINT "e:/cygwin/bin" CACHE STRING "Flex path hints, can be null if on your path")
  set(BISON_PATH_HINT "e:/cygwin/bin" CACHE STRING "Bison path hints, can be null if on your path")
  set(PERL_PATH_HINT "C:/Perl/bin" CACHE STRING "Perl path hints, can be null if on your pat")

  set(PHINTS ${PERL_PATH_HINT} ${FLEX_PATH_HINT} ${BISON_PATH_HINT})

  if(MSVC)
      set(OPTIMIZITION_FLAGS  "/GL /Ox /Oi /Ot /Oy")
      set(STP_DEFS_COMM ${STP_DEFS_COMM} -D_CRT_SECURE_NO_WARNINGS)
      set(STP_INCL_COMM windows/winports windows/winports/msc99hdr ${STP_INCL_COMM})
      include_directories(${STP_INCL_COMM})

      # stack size of MSVC must be specified
      string(REGEX REPLACE "/STACK:[0-9]+" "" CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS})
      set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /STACK:256000000")

      # inline is not a keyword in visual studios old C version, allow its redefinition
      add_definitions("-D_ALLOW_KEYWORD_MACROS")
  else()
      # mingw
      set(STP_DEFS_COMM ${STP_DEFS_COMM} -DEXT_HASH_MAP)
  endif()
  add_definitions(${STP_DEFS_COMM})
endif()

# -----------------------------------------------------------------------------
# Determine the locations of C++ hash_set and hash_map
# -----------------------------------------------------------------------------

include(CheckCxxHashSet)
check_cxx_hashset()

include(CheckCxxHashMultiSet)
check_cxx_hashmultiset()

include(CheckCxxHashMap)
check_cxx_hashmap()

# -----------------------------------------------------------------------------
# Add GIT version
# -----------------------------------------------------------------------------
function(SetVersionNumber PREFIX VERSION_MAJOR VERSION_MINOR VERSION_PATCH)
  set(${PREFIX}_VERSION_MAJOR ${VERSION_MAJOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_MINOR ${VERSION_MINOR} PARENT_SCOPE)
  set(${PREFIX}_VERSION_PATCH ${VERSION_PATCH} PARENT_SCOPE)
  set(${PREFIX}_VERSION
        "${VERSION_MAJOR}.${VERSION_MINOR}.${VERSION_PATCH}"
        PARENT_SCOPE)
endfunction()

find_program (GIT_EXECUTABLE git)
if (GIT_EXECUTABLE)
  include(GetGitRevisionDescription)
  get_git_head_revision(GIT_REFSPEC GIT_SHA)
  git_get_closest_tag(GIT_TAG)
  MESSAGE(STATUS "GIT tag found: ${GIT_TAG}")
  MESSAGE(STATUS "GIT version found: ${GIT_SHA}")
  string(REGEX REPLACE ".*(NOTFOUND).*" "\\1" NO_TAG "${GIT_TAG}")
  if ("NOTFOUND" STREQUAL ${NO_TAG})
    set(GIT_TAG "2.0.99")
  endif()
else()
  message(WARNING "This tarball should have been created with file describing the version")
  set(GIT_SHA "GIT-notfound")
  set(GIT_TAG "2.0.99")
endif()

string(REPLACE "." ";" GIT_TAG_LIST ${GIT_TAG})
SetVersionNumber("PROJECT" ${GIT_TAG_LIST})
MESSAGE(STATUS "PROJECT_VERSION: ${PROJECT_VERSION}")
MESSAGE(STATUS "PROJECT_VERSION_MAJOR: ${PROJECT_VERSION_MAJOR}")
MESSAGE(STATUS "PROJECT_VERSION_MINOR: ${PROJECT_VERSION_MINOR}")
MESSAGE(STATUS "PROJECT_VERSION_PATCH: ${PROJECT_VERSION_PATCH}")

# -----------------------------------------------------------------------------
# Write out the config.h
# -----------------------------------------------------------------------------

configure_file(
  "${CMAKE_CURRENT_SOURCE_DIR}/include/stp/config.h.in"
  "${CMAKE_CURRENT_BINARY_DIR}/include/stp/config.h"
)

# -----------------------------------------------------------------------------
# Set up includes
# -----------------------------------------------------------------------------
include_directories("${CMAKE_CURRENT_SOURCE_DIR}/include")
include_directories("${CMAKE_CURRENT_BINARY_DIR}/include")

# FIXME: External library includes
include_directories(# For extlib-abc and extlib-constbv
                    ${PROJECT_SOURCE_DIR}/lib
                    # For minisat and cryptominisat4
                    ${PROJECT_SOURCE_DIR}/lib/Sat
                   )

# -----------------------------------------------------------------------------
# Uncomment these for static compilation under Linux (messes up Valgrind)
# -----------------------------------------------------------------------------

# -----------------------------------------------------------------------------
# Find the Boost package components
# -----------------------------------------------------------------------------

if(NOT BUILD_SHARED_LIBS)
  message("Trying to use static Boost and Minisat libraries")
  set(Boost_USE_STATIC_LIBS ON)
  set(Minisat_USE_STATIC_LIBS ON)
  set(CryptoMiniSat_USE_STATIC_LIBS ON)
endif()

option(NO_BOOST "Don't try to use boost" OFF)
if (NOT NO_BOOST)
  find_package( Boost 1.46 COMPONENTS program_options)
endif()
if(NOT Boost_FOUND)
  message(STATUS "Only building executable with few command-line options because the boost program_options library were not available")
else()
  include_directories(${Boost_INCLUDE_DIRS})
endif()


# -----------------------------------------------------------------------------
# Find CryptoMiniSat4
# -----------------------------------------------------------------------------
set(cryptominisat4_DIR "" CACHE PATH "Path to directory containing cryptominisat4Config.cmake")
find_package(cryptominisat4 CONFIG)
if (cryptominisat4_FOUND AND HAVE_FLAG_STD_CPP11)
  message(STATUS "Found CryptoMiniSat4 and C++11, allowing --cryptominisat4 option")
  message(STATUS "CryptoMiniSat4 dynamic lib: ${CRYPTOMINISAT4_LIBRARIES}")
  message(STATUS "CryptoMiniSat4 static lib:  ${CRYPTOMINISAT4_STATIC_LIBRARIES}")
  message(STATUS "CryptoMiniSat4 static lib deps: ${CRYPTOMINISAT4_STATIC_LIBRARIES_DEPS}")
  add_definitions(-DUSE_CRYPTOMINISAT4)
  include_directories(${CRYPTOMINISAT4_INCLUDE_DIRS})
  set(USE_CRYPTOMINISAT4 ON)
else()
  message(WARNING "CryptoMiniSat4 (v4.2 or above) or C++11 support not found, not allowing --cryptominisat4 option")
endif()

# -----------------------------------------------------------------------------
# Find Minisat
# -----------------------------------------------------------------------------
find_package(minisat)
if (NOT MINISAT_FOUND)
  message(FATAL_ERROR "You must install minisat from https://github.com/niklasso/minisat")
else()
  message(STATUS "OK, found Minisat library under ${MINISAT_LIBRARIES} and Minisat include dirs under ${MINISAT_INCLUDE_DIRS}")
endif()
include_directories(${MINISAT_INCLUDE_DIRS})
set(LIBS ${LIBS} ${MINISAT_LIBRARIES})

# -----------------------------------------------------------------------------
# Find Parser and Lexer generators
# -----------------------------------------------------------------------------
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

# -----------------------------------------------------------------------------
# Setup library build path (this is **not** the library install path)
# -----------------------------------------------------------------------------
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)

# -----------------------------------------------------------------------------
# Provide an export name to be used by targets that wish to export themselves.
# -----------------------------------------------------------------------------
set(STP_EXPORT_NAME "STPTargets")

# -----------------------------------------------------------------------------
# Testing and Python interface options
# -----------------------------------------------------------------------------

option(ENABLE_TESTING "Enable testing" OFF)
option(ENABLE_PYTHON_INTERFACE "Enable Python interface" ON)

if (ENABLE_PYTHON_INTERFACE AND NOT BUILD_SHARED_LIBS)
    message(FATAL_ERROR "Python interface requires shared library")
endif()

# Both the testing infrastructure and python interface depend on python
if(ENABLE_TESTING OR ENABLE_PYTHON_INTERFACE)
  find_package(PythonInterp REQUIRED)
  mark_as_advanced(CLEAR PYTHON_EXECUTABLE) # Make visible in cmake-gui/ccmake

  if(NOT PYTHONINTERP_FOUND)
    message(FATAL_ERROR "Python cannot be found. Please install it or disable testing and/or python interface")
  endif()
endif()

# -----------------------------------------------------------------------------
# Compile all subdirs
# -----------------------------------------------------------------------------

message(STATUS "Final CXX flags ${CMAKE_CXX_FLAGS}")
add_subdirectory(lib)
add_subdirectory(tools)
add_subdirectory(bindings)

# -----------------------------------------------------------------------------
# Add uninstall target for makefiles
# -----------------------------------------------------------------------------
configure_file(
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules/cmake_uninstall.cmake.in"
  "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  IMMEDIATE @ONLY
)

add_custom_target(uninstall
  COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake
)

# -----------------------------------------------------------------------------
# Add tests if required
# -----------------------------------------------------------------------------

if(ENABLE_TESTING)
  message(STATUS "Testing is enabled")

  set(UNIT_TEST_EXE_SUFFIX "Tests" CACHE STRING "Suffix for Unit test executable")

  add_custom_target(check
    COMMENT "top level target to invoke all other tests"
  )

  add_subdirectory(tests)
else()
    message(WARNING "Testing is disabled")
endif()

# -----------------------------------------------------------------------------
# Export our targets so that other CMake based projects can interface with
# the build of STP in the build-tree
# -----------------------------------------------------------------------------
set(STP_TARGETS_FILENAME "STPTargets.cmake")
set(STP_CONFIG_FILENAME "STPConfig.cmake")
set(STP_CONFIG_VERSION_FILENAME "STPConfigVersion.cmake")

# Export targets
if (Boost_FOUND)
  export(TARGETS stp stp_simple ${STP_SHARED_LIBRARY} ${STP_STATIC_LIBRARY}
    FILE "${PROJECT_BINARY_DIR}/${STP_TARGETS_FILENAME}"
  )
else()
  export(TARGETS stp_simple ${STP_SHARED_LIBRARY} ${STP_STATIC_LIBRARY}
    FILE "${PROJECT_BINARY_DIR}/${STP_TARGETS_FILENAME}"
  )
endif()

# Create STPConfig file
set(EXPORT_TYPE "Build-tree")
set(CONF_INCLUDE_DIRS "${PROJECT_BINARY_DIR}/include")
configure_file(STPConfig.cmake.in
  "${PROJECT_BINARY_DIR}/${STP_CONFIG_FILENAME}" @ONLY
)
configure_file(STPConfigVersion.cmake.in
  "${PROJECT_BINARY_DIR}/${STP_CONFIG_VERSION_FILENAME}" @ONLY
)

# Export this package to the CMake user package registry
# Now the user can just use find_package(STP) on their system
export(PACKAGE STP)


# -----------------------------------------------------------------------------
# Export our targets so that other CMake based projects can interface with
# the build of STP that is installed.
# -----------------------------------------------------------------------------
if(WIN32 AND NOT CYGWIN)
  set(DEF_INSTALL_CMAKE_DIR CMake)
else()
  set(DEF_INSTALL_CMAKE_DIR ${CMAKE_INSTALL_LIBDIR}/cmake/STP)
endif()
set(STP_INSTALL_CMAKE_DIR ${DEF_INSTALL_CMAKE_DIR} CACHE PATH
  "Installation directory for STP CMake files"
)

# Create STPConfig file
set(EXPORT_TYPE "installed")
set(CONF_INCLUDE_DIRS "${CMAKE_INSTALL_PREFIX}/include")
configure_file(STPConfig.cmake.in
  "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${STP_CONFIG_FILENAME}" @ONLY
)

install(FILES
  "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/${STP_CONFIG_FILENAME}"
  "${PROJECT_BINARY_DIR}/${STP_CONFIG_VERSION_FILENAME}"
  DESTINATION "${STP_INSTALL_CMAKE_DIR}"
)

# Install the export set for use with the install-tree
install(EXPORT ${STP_EXPORT_NAME} DESTINATION
  "${STP_INSTALL_CMAKE_DIR}"
)

