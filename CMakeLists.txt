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

project(STP)
cmake_minimum_required(VERSION 3.0.2 FATAL_ERROR)
set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 11)

if(NOT (CMAKE_MAJOR_VERSION LESS 2))
    if(POLICY CMP0048)
        #policy for VERSION in cmake 3.0
        cmake_policy(SET CMP0048 NEW)
    endif()
endif()

# Search paths for custom CMake modules
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake/modules)

set(CMAKE_INSTALL_LIBDIR lib CACHE STRING "Output directory for libraries")
set(CMAKE_INSTALL_BINDIR bin CACHE STRING "Output directory for executables")
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
if(CMAKE_BUILD_TYPE STREQUAL "Release")
    set(ENABLE_ASSERTIONS OFF)
endif()

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
option(STATICCOMPILE "Compile static library and executable" OFF)

if (STATICCOMPILE)
    set(Boost_USE_STATIC_LIBS ON)
    if (NOT MSVC)
        set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -static -Wl,--whole-archive -lpthread -Wl,--no-whole-archive -static ")
        set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")

        # removing -rdynamic that's automatically added
        foreach (language CXX C)
            set(VAR_TO_MODIFY "CMAKE_SHARED_LIBRARY_LINK_${language}_FLAGS")
            string(REGEX REPLACE "(^| )-rdynamic($| )"
                                 " "
                                 replacement
                                 "${${VAR_TO_MODIFY}}")
            #message("Original (${VAR_TO_MODIFY}) is ${${VAR_TO_MODIFY}} replacement is ${replacement}")
            set(${VAR_TO_MODIFY} "${replacement}" CACHE STRING "Default flags for ${build_config} configuration" FORCE)
        endforeach()
    endif()
else ()
    if (APPLE)
      set(CMAKE_MACOSX_RPATH ON)
      set(CMAKE_INSTALL_RPATH "@loader_path/../lib")
      message(STATUS "Using RPATH for dynamic linking")
    endif()
endif()

if (MSVC AND NOT STATICCOMPILE)
    add_definitions(-D STP_SHARED_LIB) # Used for symbol visibilty control
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

check_cxx_compiler_flag("-std=c++11" HAVE_FLAG_STD_CPP11)

if(APPLE)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
endif()

if (NOT MSVC)
    add_cxx_flag_if_supported("-Wall")
    add_cxx_flag_if_supported("-Wextra")
    add_cxx_flag_if_supported("-Wunused")
    add_cxx_flag_if_supported("-pedantic")
    add_cxx_flag_if_supported("-Wsign-compare")
    if (NOT CMAKE_BUILD_TYPE STREQUAL "Release")
        add_cxx_flag_if_supported("-fno-omit-frame-pointer")
    endif()
    add_cxx_flag_if_supported("-Wtype-limits")
    add_cxx_flag_if_supported("-Wuninitialized")
    add_cxx_flag_if_supported("-Wno-deprecated")
    add_cxx_flag_if_supported("-Wstrict-aliasing")
    add_cxx_flag_if_supported("-Wpointer-arith")
    add_cxx_flag_if_supported("-Wheader-guard")
    #if(NOT ENABLE_TESTING AND ${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
        # almost working
        # add_cxx_flag_if_supported("-fvisibility=hidden")
        set(CMAKE_EXE_LINKER_FLAGS " ${CMAKE_EXE_LINKER_FLAGS} -Wl,--discard-all -Wl,--build-id=sha1")
    endif()
    add_cxx_flag_if_supported("-Wpointer-arith")
    add_cxx_flag_if_supported("-Wformat-nonliteral")
    add_cxx_flag_if_supported("-Winit-self")
    add_cxx_flag_if_supported("-Wparentheses")
    add_cxx_flag_if_supported("-Wunreachable-code")
    add_cxx_flag_if_supported("-ggdb3")
    add_cxx_flag("-fPIC")
    # add_cxx_flag_if_supported("-flto") # slow compile and not enough benefits
endif()

add_definitions("-D__STDC_LIMIT_MACROS")

option(TUNE_NATIVE "Use -mtune=native" OFF)
if(TUNE_NATIVE)
  add_cxx_flag_if_supported("-mtune=native")
endif()

option(COVERAGE "Build with coverage check" OFF)
if (COVERAGE)
    add_cxx_flag("--coverage")
endif()

if(WIN32)
  set(FLEX_PATH_HINT "e:/cygwin/bin" CACHE STRING "Flex path hints, can be null if on your path")
  set(BISON_PATH_HINT "e:/cygwin/bin" CACHE STRING "Bison path hints, can be null if on your path")
  set(PERL_PATH_HINT "C:/Perl/bin" CACHE STRING "Perl path hints, can be null if on your pat")

  set(PHINTS ${PERL_PATH_HINT} ${FLEX_PATH_HINT} ${BISON_PATH_HINT})

  if(MSVC)
      # see https://msdn.microsoft.com/en-us/library/fwkeyyhe.aspx for details
      # /ZI = include debug info
      # /Oy omit frame pointers
      # /Wall = all warnings
      # /GL whole program optimisation
      SET(CMAKE_CXX_FLAGS_RELWITHDEBINFO "${CMAKE_CXX_FLAGS_RELWITHDEBINFO} /Ox /ZI")
      SET(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} /O3 /D NDEBUG /ZI")
      SET(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} /Od")

      #don't give too many warnings
      add_compile_options(/W1)

      # buffers security check
      add_compile_options(/GS)

      set(STP_DEFS_COMM ${STP_DEFS_COMM} -D_CRT_SECURE_NO_WARNINGS)
      set(STP_INCL_COMM windows/winports windows/winports/msc99hdr ${STP_INCL_COMM})
      include_directories(${STP_INCL_COMM})
      add_subdirectory(windows)
      set(PLATFORM_COMPAT_LIBRARIES ${PLATFORM_COMPAT_LIBRARIES} windows_compat)
      set(CMAKE_FIND_LIBRARY_SUFFIXES .lib .a ${CMAKE_FIND_LIBRARY_SUFFIXES})

      # stack size of MSVC must be specified
      string(REGEX REPLACE "/STACK:[0-9]+" "" CMAKE_EXE_LINKER_FLAGS ${CMAKE_EXE_LINKER_FLAGS})
      set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} /STACK:512000000")

      # inline is not a keyword in visual studios old C version, allow its redefinition
      add_definitions("-D_ALLOW_KEYWORD_MACROS")
  endif()
  add_definitions(${STP_DEFS_COMM})
endif()

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
  MESSAGE(STATUS "GIT hash found: ${GIT_SHA}")
else()
  set(GIT_SHA "GIT-hash-notfound")
endif()
set(STP_FULL_VERSION "2.1.2")

string(REPLACE "." ";" STP_FULL_VERSION_LIST ${STP_FULL_VERSION})
SetVersionNumber("PROJECT" ${STP_FULL_VERSION_LIST})
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
                   )

option(ONLY_SIMPLE "Don't try to use boost" OFF)
if (NOT ONLY_SIMPLE)
  find_package( Boost 1.46 COMPONENTS program_options)
endif()

if(NOT Boost_FOUND)
  message(STATUS "Only building executable with few command-line options because the boost program_options library were not available")
endif()


# -----------------------------------------------------------------------------
# Find CryptoMiniSat
# -----------------------------------------------------------------------------
option(NOCRYPTOMINISAT "Don't try to use cryptominisat" OFF)

if (NOT NOCRYPTOMINISAT)
  set(cryptominisat_DIR "" CACHE PATH "Path to directory containing cryptominisat5Config.cmake")
  find_package(cryptominisat5 CONFIG)
  if (cryptominisat5_FOUND AND HAVE_FLAG_STD_CPP11 AND (NOT NOCRYPTOMINISAT))
    message(STATUS "Found CryptoMiniSat 5.x and C++11, allowing --cryptominisat5 option")
    message(STATUS "CryptoMiniSat5 dynamic lib: ${CRYPTOMINISAT5_LIBRARIES}")
    message(STATUS "CryptoMiniSat5 static lib:  ${CRYPTOMINISAT5_STATIC_LIBRARIES}")
    message(STATUS "CryptoMiniSat5 static lib deps: ${CRYPTOMINISAT5_STATIC_LIBRARIES_DEPS}")
    add_definitions(-DUSE_CRYPTOMINISAT)
    include_directories(${CRYPTOMINISAT5_INCLUDE_DIRS})
    set(USE_CRYPTOMINISAT ON)
  else()
    message(WARNING "CryptoMiniSat5 (5.0 or above) or C++11 support not found, not allowing --cryptominisat option")
  endif()
endif()

option(FORCE_CMS "Must build with CryptoMiniSat" OFF)
if (FORCE_CMS AND NOT USE_CRYPTOMINISAT)
    message(FATAL_ERROR "CryptoMiniSat 5.x was not found but it was requested. Exiting.")
endif()

# -----------------------------------------------------------------------------
# Find ZLIB (needed for MiniSat)
# yes, we need to include the zlib header location or STP will not build
# thanks to MiniSat include-ing it n the header
# -----------------------------------------------------------------------------
find_package(ZLIB)
include_directories(${ZLIB_INCLUDE_DIR})
include_directories(${minisat_SOURCE_DIR})

# -----------------------------------------------------------------------------
# Find Minisat
# -----------------------------------------------------------------------------
find_package(minisat)
set(MINISAT_INCLUDE_DIRS "" CACHE PATH "MiniSat include directory")
set(MINISAT_LIBDIR "" CACHE PATH "MiniSat library directory")
if (NOT MINISAT_FOUND)
  message(FATAL_ERROR "You must install minisat from https://github.com/niklasso/minisat")
else()
  message(STATUS "OK, found Minisat library under ${MINISAT_LIBRARIES} and Minisat include dirs under ${MINISAT_INCLUDE_DIR}")
endif()
include_directories(${MINISAT_INCLUDE_DIR})
set(LIBS ${LIBS} ${MINISAT_LIBRARIES})

# -----------------------------------------------------------------------------
# Find Parser and Lexer generators
# -----------------------------------------------------------------------------
find_package(BISON REQUIRED)
find_package(FLEX REQUIRED)

# -----------------------------------------------------------------------------
# Query definitions
# -----------------------------------------------------------------------------
get_directory_property( DirDefs DIRECTORY ${CMAKE_SOURCE_DIR} COMPILE_DEFINITIONS )
set(COMPILE_DEFINES)
foreach( d ${DirDefs} )
    # message( STATUS "Found Define: " ${d} )
    set(COMPILE_DEFINES "${COMPILE_DEFINES} -D${d}")
endforeach()
message(STATUS "All defines at startup: ${COMPILE_DEFINES}")

# -----------------------------------------------------------------------------
# Setup library build path (this is **not** the library install path)
# -----------------------------------------------------------------------------
if(WIN32)
  # Create a single bin/ output directory so that DLL files can be
  # readily found on DLL platforms.
  set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
  set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/bin)
endif()

if(DEFINED CMAKE_CONFIGURATION_TYPES)
  # Placing the binaries in ${CMAKE_*_OUTPUT_DIRECTORY} without regard to
  # the debug/release/... configuration. This is needed for build systems
  # where files for multiple configurations are kept within the same build
  # directory (eg. MSBuild), since some targets (e.g. python-interface-tests)
  # require the path to the stp library to be given in a configuration file.
  # Note: the paths could be determined in a cleaner fashion by using generator
  # expressions, which were used up to commit 1af1f5. However, that solution
  # was not feasible, since CMake versions provided by recent Debian versions
  # are buggy w.r.t. generator expressions.
  foreach(OUTPUTCONFIG ${CMAKE_CONFIGURATION_TYPES})
    string(TOUPPER ${OUTPUTCONFIG} OUTPUTCONFIG_UPPER)
    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY_${OUTPUTCONFIG_UPPER} ${CMAKE_RUNTIME_OUTPUT_DIRECTORY})
    set(CMAKE_LIBRARY_OUTPUT_DIRECTORY_${OUTPUTCONFIG_UPPER} ${CMAKE_LIBRARY_OUTPUT_DIRECTORY})
    set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY_${OUTPUTCONFIG_UPPER} ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY})
  endforeach(OUTPUTCONFIG CMAKE_CONFIGURATION_TYPES)
else()
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)
  set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_BINARY_DIR}/lib)
endif()

# -----------------------------------------------------------------------------
# Provide an export name to be used by targets that wish to export themselves.
# -----------------------------------------------------------------------------
set(STP_EXPORT_NAME "STPTargets")

# -----------------------------------------------------------------------------
# Testing and Python interface options
# -----------------------------------------------------------------------------

option(ENABLE_TESTING "Enable testing" OFF)

# try finding python if the user did not explicitly said that
# he/she does not want python bindings
if ((NOT DEFINED ENABLE_PYTHON_INTERFACE) OR ENABLE_PYTHON_INTERFACE)
    find_package (PythonInterp 2.7)
    find_package (PythonLibs 2.7)
    if (PYTHON_EXECUTABLE AND PYTHON_LIBRARY AND PYTHON_INCLUDE_DIR)
        message(STATUS "PYTHON_EXECUTABLE:FILEPATH=${PYTHON_EXECUTABLE}")
        message(STATUS "PYTHON_LIBRARY:FILEPATH=${PYTHON_LIBRARY}")
        message(STATUS "PYTHON_INCLUDE_DIR:FILEPATH=${PYTHON_INCLUDE_DIR}")
        message(STATUS "PYTHONLIBS_VERSION_STRING=${PYTHONLIBS_VERSION_STRING}")
        set(PYTHON_OK ON)
        message(STATUS "OK, found python interpreter, libs and header files")
    else()
        message(WARNING "Cannot find python interpreter, libs and header files, cannot build python interface")
    endif()

    if (PYTHON_OK AND NOT STATICCOMPILE)
        message(STATUS "Python found, enabling python interface")
        set(ENABLE_PYTHON_INTERFACE ON)
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

if(ENABLE_TESTING AND NOT PYTHON_EXECUTABLE)
    message(STATUS "Python interpreter cannot be found. Please install it to have the python interface and to enable testing")
    set(ENABLE_TESTING OFF)
endif()

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
    set(EXTRA_EXPORT_TARGETS stp)
endif()
export(TARGETS stp_simple libstp ${EXTRA_EXPORT_TARGETS}
    FILE "${PROJECT_BINARY_DIR}/${STP_TARGETS_FILENAME}")

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
