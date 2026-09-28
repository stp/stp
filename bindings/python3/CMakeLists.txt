# AUTHORS: Andrew Teylu
#
# BEGIN DATE: September, 2026
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

# -----------------------------------------------------------------------------
# The STP 3.x Python API: the Cython extension stp._core over <stp/stp.h> and
# the pure-Python package around it, assembled in <build>/bindings/python3/stp/
# so that PYTHONPATH=<build>/bindings/python3 gives `import stp`.
#
# ENABLE_PYTHON3_API defaults to ON when the chosen interpreter can import
# Cython (cython runs at build time; nothing generated is checked in).
# -----------------------------------------------------------------------------

if(NOT PYTHON_EXECUTABLE)
    set(_stp_py3_cython_found OFF)
else()
    execute_process(
        COMMAND ${PYTHON_EXECUTABLE} -c "import Cython; print(Cython.__version__)"
        RESULT_VARIABLE _stp_py3_cython_rc
        OUTPUT_VARIABLE _stp_py3_cython_version
        OUTPUT_STRIP_TRAILING_WHITESPACE
        ERROR_QUIET)
    if(_stp_py3_cython_rc EQUAL 0)
        set(_stp_py3_cython_found ON)
    else()
        set(_stp_py3_cython_found OFF)
    endif()
endif()

if(_stp_py3_cython_found AND BUILD_SHARED_LIBS)
    set(_stp_py3_default ON)
else()
    set(_stp_py3_default OFF)
endif()
option(ENABLE_PYTHON3_API "Build the STP 3.x Python API (needs Cython for PYTHON_EXECUTABLE)" ${_stp_py3_default})
add_feature_info(Python3API ENABLE_PYTHON3_API "Enables the 3.x Python API (stp._core, Cython)")

if(NOT ENABLE_PYTHON3_API)
    return()
endif()

if(NOT _stp_py3_cython_found)
    message(FATAL_ERROR "ENABLE_PYTHON3_API=ON but ${PYTHON_EXECUTABLE} cannot import Cython; "
                        "install it for that interpreter or point PYTHON_EXECUTABLE at one that has it.")
endif()
message(STATUS "Python 3.x API: Cython ${_stp_py3_cython_version} via ${PYTHON_EXECUTABLE}")

# The development files of the interpreter the rest of the build already
# chose (Python3_EXECUTABLE is set from PYTHON_EXECUTABLE at the top level).
set(Python3_EXECUTABLE "${PYTHON_EXECUTABLE}")
find_package(Python3 COMPONENTS Interpreter Development.Module REQUIRED)

# lib/Api/CMakeLists.txt publishes STP_API_GEN_DIR into lib/ only; the
# generated tree is always <build>/generated.
if(NOT STP_API_GEN_DIR)
    set(STP_API_GEN_DIR ${PROJECT_BINARY_DIR}/generated)
endif()

set(STP_PY3_SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/stp)
set(STP_PY3_PACKAGE_DIR ${CMAKE_CURRENT_BINARY_DIR}/stp)
file(MAKE_DIRECTORY ${STP_PY3_PACKAGE_DIR})

# --- the extension ----------------------------------------------------------
set(STP_PY3_CYTHON_C ${CMAKE_CURRENT_BINARY_DIR}/_core.c)
add_custom_command(
    OUTPUT ${STP_PY3_CYTHON_C}
    COMMAND ${PYTHON_EXECUTABLE} -m cython -3
            --module-name stp._core
            -I ${STP_API_GEN_DIR}/python -I ${CMAKE_CURRENT_SOURCE_DIR}
            -o ${STP_PY3_CYTHON_C}
            ${STP_PY3_SOURCE_DIR}/_core.pyx
    DEPENDS ${STP_PY3_SOURCE_DIR}/_core.pyx
            ${STP_PY3_SOURCE_DIR}/_core.pxd
            ${STP_API_GEN_DIR}/python/_gen_enums.pxi
    COMMENT "Cythonising stp/_core.pyx"
    VERBATIM)

Python3_add_library(stp_py3_core MODULE WITH_SOABI ${STP_PY3_CYTHON_C})
add_dependencies(stp_py3_core stp_api_tables)
set_target_properties(stp_py3_core PROPERTIES
    OUTPUT_NAME _core
    LIBRARY_OUTPUT_DIRECTORY ${STP_PY3_PACKAGE_DIR})
target_link_libraries(stp_py3_core PRIVATE stp)
target_include_directories(stp_py3_core PRIVATE ${STP_PY3_SOURCE_DIR})
if(NOT MSVC)
    # Cython's generated C is not this project's code: keep its warnings quiet.
    target_compile_options(stp_py3_core PRIVATE -w)
endif()

# --- the package ------------------------------------------------------------
set(STP_PY3_MODULES
    __init__.py
    _terms.py
    _solver.py
    _pretty.py
    _smt2.py)
set(_stp_py3_copied "")
foreach(_m ${STP_PY3_MODULES})
    add_custom_command(
        OUTPUT ${STP_PY3_PACKAGE_DIR}/${_m}
        COMMAND ${CMAKE_COMMAND} -E copy_if_different ${STP_PY3_SOURCE_DIR}/${_m} ${STP_PY3_PACKAGE_DIR}/${_m}
        DEPENDS ${STP_PY3_SOURCE_DIR}/${_m}
        COMMENT "Copying stp/${_m}"
        VERBATIM)
    list(APPEND _stp_py3_copied ${STP_PY3_PACKAGE_DIR}/${_m})
endforeach()
# the generated enums (Kind, Option, ErrorCode) live in the package too
add_custom_command(
    OUTPUT ${STP_PY3_PACKAGE_DIR}/_gen_kinds.py
    COMMAND ${CMAKE_COMMAND} -E copy_if_different ${STP_API_GEN_DIR}/python/_gen_kinds.py ${STP_PY3_PACKAGE_DIR}/_gen_kinds.py
    DEPENDS ${STP_API_GEN_DIR}/python/_gen_kinds.py stp_api_tables
    COMMENT "Copying the generated stp/_gen_kinds.py"
    VERBATIM)
list(APPEND _stp_py3_copied ${STP_PY3_PACKAGE_DIR}/_gen_kinds.py)

add_custom_target(stp_python3 ALL DEPENDS ${_stp_py3_copied} stp_py3_core)

# The build-tree package directory, for the tests (tests/api/python).
set(STP_PY3_PYTHONPATH ${CMAKE_CURRENT_BINARY_DIR} CACHE INTERNAL "PYTHONPATH of the built 3.x Python package")

# --- installation -----------------------------------------------------------
# This is the installed `stp` Python package. PYTHON_LIB_INSTALL_DIR is
# relative to the install prefix, so the package goes wherever the rest of STP
# goes, --prefix included: to the interpreter's platform site-packages when
# that lies inside the prefix (the default /usr/local install), so `import stp`
# works unaided, and otherwise to the prefix's own, which needs PYTHONPATH. An
# explicit value, relative or absolute, wins. The extension finds libstp
# through an rpath to the library's install directory.
execute_process(
    COMMAND ${PYTHON_EXECUTABLE} -c
            "import os, sys, sysconfig; scheme = 'nt' if os.name == 'nt' else 'posix_prefix'; print(sysconfig.get_path('platlib', vars={'base': sys.base_prefix, 'platbase': sys.base_prefix})); print(os.path.relpath(sysconfig.get_path('platlib', scheme, vars={'base': '/p', 'platbase': '/p'}), '/p'))"
    RESULT_VARIABLE _stp_py3_site_rc
    OUTPUT_VARIABLE _stp_py3_site_dirs
    OUTPUT_STRIP_TRAILING_WHITESPACE)
if(NOT _stp_py3_site_rc EQUAL 0 OR _stp_py3_site_dirs STREQUAL "")
    message(FATAL_ERROR "Failed to determine the Python site-packages directory of ${PYTHON_EXECUTABLE}")
endif()
string(REPLACE "\n" ";" _stp_py3_site_dirs "${_stp_py3_site_dirs}")
list(GET _stp_py3_site_dirs 0 _stp_py3_site_detected)
list(GET _stp_py3_site_dirs 1 _stp_py3_site_under_prefix)
file(TO_CMAKE_PATH "${_stp_py3_site_detected}" _stp_py3_site_detected)
file(TO_CMAKE_PATH "${_stp_py3_site_under_prefix}" _stp_py3_site_under_prefix)

get_filename_component(_stp_py3_prefix "${CMAKE_INSTALL_PREFIX}" ABSOLUTE)
file(RELATIVE_PATH _stp_py3_site_rel "${_stp_py3_prefix}" "${_stp_py3_site_detected}")
if(IS_ABSOLUTE "${_stp_py3_site_rel}" OR _stp_py3_site_rel MATCHES "^\\.\\.(/|$)")
    set(_stp_py3_site_default "${_stp_py3_site_under_prefix}")
else()
    set(_stp_py3_site_default "${_stp_py3_site_rel}")
endif()

# STRING, not PATH: CMake makes a relative PATH given with -D absolute against
# the build directory.
set(PYTHON_LIB_INSTALL_DIR "${_stp_py3_site_default}" CACHE STRING
    "Installation directory for the stp Python package, relative to CMAKE_INSTALL_PREFIX unless absolute")
if(IS_ABSOLUTE "${PYTHON_LIB_INSTALL_DIR}")
    if(NOT EXISTS "${PYTHON_LIB_INSTALL_DIR}")
        message(FATAL_ERROR "Python site package directory '${PYTHON_LIB_INSTALL_DIR}' does not exist")
    endif()
    set(_stp_py3_install_abs "${PYTHON_LIB_INSTALL_DIR}")
else()
    set(_stp_py3_install_abs "${CMAKE_INSTALL_PREFIX}/${PYTHON_LIB_INSTALL_DIR}")
endif()
message(STATUS "Python package installs to ${_stp_py3_install_abs}")
get_filename_component(_stp_py3_install_abs "${_stp_py3_install_abs}" ABSOLUTE)
if(NOT _stp_py3_install_abs STREQUAL _stp_py3_site_detected)
    message(STATUS "  outside ${PYTHON_EXECUTABLE}'s site-packages; add it to PYTHONPATH to import stp")
endif()

if(IS_ABSOLUTE "${CMAKE_INSTALL_LIBDIR}")
    set(_stp_py3_libdir "${CMAKE_INSTALL_LIBDIR}")
else()
    set(_stp_py3_libdir "${CMAKE_INSTALL_PREFIX}/${CMAKE_INSTALL_LIBDIR}")
endif()
set_target_properties(stp_py3_core PROPERTIES INSTALL_RPATH "${_stp_py3_libdir}")
install(TARGETS stp_py3_core LIBRARY DESTINATION "${PYTHON_LIB_INSTALL_DIR}/stp")
install(FILES ${_stp_py3_copied} DESTINATION "${PYTHON_LIB_INSTALL_DIR}/stp")
