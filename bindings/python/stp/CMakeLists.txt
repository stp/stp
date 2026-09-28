# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# # furnished to do so, subject to the following conditions:
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

# -----------------------------------------------------------------------------
# Setup python module in build directory
# -----------------------------------------------------------------------------

# The binary path isn't known until the build process starts
# (e.g. when building with MSBuild), so generate the file lately.)

# get_property(STP_LIB_LOCATION TARGET stp PROPERTY LOCATION)
# file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>)

get_target_property(LIBSTP_BASENAME stp OUTPUT_NAME)
set(LIBSTP_FILENAME "${CMAKE_SHARED_LIBRARY_PREFIX}${LIBSTP_BASENAME}${CMAKE_SHARED_LIBRARY_SUFFIX}")

#
# 'library_path.py.in' has some code that is conditional on being on Win32 or
# not -- rather than have two `.in` files, we leave the non-Win32 code comment
# out.
#
if(WIN32)
  set(WIN32PYTHONCOMMENT "")
else()
  set(WIN32PYTHONCOMMENT "#")
endif()

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/library_path.py.in
               ${CMAKE_CURRENT_BINARY_DIR}/library_path.py @ONLY)

# Copy rest of files to build directory
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/stp.py.in
              ${CMAKE_CURRENT_BINARY_DIR}/stp.py)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/__init__.py.in
                ${CMAKE_CURRENT_BINARY_DIR}/__init__.py)

# -----------------------------------------------------------------------------
# Handle installation
# -----------------------------------------------------------------------------

# The interpreter's own site-packages, and where the same interpreter would put
# packages under an arbitrary prefix, relative to that prefix.
execute_process(COMMAND ${PYTHON_EXECUTABLE} -c
                        "import os, sys, sysconfig; scheme = 'nt' if os.name == 'nt' else 'posix_prefix'; print(sysconfig.get_path('purelib', vars={'base': sys.base_prefix})); print(os.path.relpath(sysconfig.get_path('purelib', scheme, vars={'base': '/p', 'platbase': '/p'}), '/p'))"
                 RESULT_VARIABLE RETURN_CODE
                 OUTPUT_VARIABLE PYTHON_LIB_DIRS
                 OUTPUT_STRIP_TRAILING_WHITESPACE
               )

if (${RETURN_CODE} GREATER 0)
    message(FATAL_ERROR "Failed to determine python site package directory")
endif()

string(REPLACE "\n" ";" PYTHON_LIB_DIRS "${PYTHON_LIB_DIRS}")
list(GET PYTHON_LIB_DIRS 0 PYTHON_LIB_DIR_DETECTED)
list(GET PYTHON_LIB_DIRS 1 PYTHON_LIB_DIR_UNDER_PREFIX)
file(TO_CMAKE_PATH "${PYTHON_LIB_DIR_DETECTED}" PYTHON_LIB_DIR_DETECTED)
file(TO_CMAKE_PATH "${PYTHON_LIB_DIR_UNDER_PREFIX}" PYTHON_LIB_DIR_UNDER_PREFIX)

# Relative to the install prefix, so the package goes wherever the rest of STP
# goes, --prefix included. The interpreter's site-packages when it lies inside
# the prefix (the default /usr/local install), so `import stp` works unaided;
# otherwise the prefix's own site-packages, which needs PYTHONPATH.
get_filename_component(_stp_prefix "${CMAKE_INSTALL_PREFIX}" ABSOLUTE)
file(RELATIVE_PATH _stp_detected_rel "${_stp_prefix}" "${PYTHON_LIB_DIR_DETECTED}")
if(IS_ABSOLUTE "${_stp_detected_rel}" OR _stp_detected_rel MATCHES "^\\.\\.(/|$)")
    set(_stp_python_default "${PYTHON_LIB_DIR_UNDER_PREFIX}")
else()
    set(_stp_python_default "${_stp_detected_rel}")
endif()

# STRING, not PATH: CMake makes a relative PATH given with -D absolute against
# the build directory.
set(PYTHON_LIB_INSTALL_DIR "${_stp_python_default}" CACHE STRING
    "Installation directory for stp python package, relative to CMAKE_INSTALL_PREFIX unless absolute")

if(IS_ABSOLUTE "${PYTHON_LIB_INSTALL_DIR}")
    if(NOT EXISTS "${PYTHON_LIB_INSTALL_DIR}")
        message(FATAL_ERROR "Python site package directory '${PYTHON_LIB_INSTALL_DIR}' does not exist")
    endif()
    set(STP_PYTHON_LIB_INSTALL_ABSOLUTE "${PYTHON_LIB_INSTALL_DIR}")
else()
    set(STP_PYTHON_LIB_INSTALL_ABSOLUTE
        "${CMAKE_INSTALL_PREFIX}/${PYTHON_LIB_INSTALL_DIR}")
endif()
message(STATUS "Python package installs to ${STP_PYTHON_LIB_INSTALL_ABSOLUTE}")
get_filename_component(_stp_python_install_abs
                       "${STP_PYTHON_LIB_INSTALL_ABSOLUTE}" ABSOLUTE)
if(NOT _stp_python_install_abs STREQUAL PYTHON_LIB_DIR_DETECTED)
    message(STATUS "  outside ${PYTHON_EXECUTABLE}'s site-packages; add it to PYTHONPATH to import stp")
endif()

# Install main files

install(FILES ${CMAKE_CURRENT_BINARY_DIR}/stp.py
              ${CMAKE_CURRENT_BINARY_DIR}/__init__.py
        DESTINATION "${PYTHON_LIB_INSTALL_DIR}/stp")

# Generate and install file describing install location of stp shared library
# FIXME: the concrete binary filename should be obtained via generator
#         expressions, but they can't be used for now due to bugs in older
#         versions of CMake
get_filename_component(STP_PYTHON_PACKAGE_INSTALL_DIR
                       "${STP_PYTHON_LIB_INSTALL_ABSOLUTE}/stp" ABSOLUTE)
if(IS_ABSOLUTE "${CMAKE_INSTALL_LIBDIR}")
  set(STP_LIBRARY_INSTALL_DIR "${CMAKE_INSTALL_LIBDIR}")
else()
  set(STP_LIBRARY_INSTALL_DIR
      "${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR}")
endif()
if(IS_ABSOLUTE "${CMAKE_INSTALL_BINDIR}")
  set(STP_RUNTIME_INSTALL_DIR "${CMAKE_INSTALL_BINDIR}")
else()
  set(STP_RUNTIME_INSTALL_DIR
      "${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_BINDIR}")
endif()
get_filename_component(STP_LIBRARY_INSTALL_DIR
                       "${STP_LIBRARY_INSTALL_DIR}" ABSOLUTE)
get_filename_component(STP_RUNTIME_INSTALL_DIR
                       "${STP_RUNTIME_INSTALL_DIR}" ABSOLUTE)
file(RELATIVE_PATH STP_PYTHON_TO_INSTALL_LIBDIR
     "${STP_PYTHON_PACKAGE_INSTALL_DIR}" "${STP_LIBRARY_INSTALL_DIR}")
file(RELATIVE_PATH STP_PYTHON_TO_INSTALL_BINDIR
     "${STP_PYTHON_PACKAGE_INSTALL_DIR}" "${STP_RUNTIME_INSTALL_DIR}")
file(TO_CMAKE_PATH "${STP_PYTHON_TO_INSTALL_LIBDIR}"
     STP_PYTHON_TO_INSTALL_LIBDIR)
file(TO_CMAKE_PATH "${STP_PYTHON_TO_INSTALL_BINDIR}"
     STP_PYTHON_TO_INSTALL_BINDIR)
configure_file(library_path.py.in_install "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/library_path.py" @ONLY)

install(FILES "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/library_path.py"
        DESTINATION "${PYTHON_LIB_INSTALL_DIR}/stp"
       )
