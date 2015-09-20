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

# -----------------------------------------------------------------------------
# Setup python module in build directory
# -----------------------------------------------------------------------------
get_target_property(LIBSTP_PATH libstp LOCATION)
configure_file(library_path.py.in library_path.py @ONLY)

# Copy rest of files to build directory
configure_file(stp.py stp.py COPYONLY)
configure_file(__init__.py __init__.py COPYONLY)

# -----------------------------------------------------------------------------
# Handle installation
# -----------------------------------------------------------------------------

# Try to guess the right place by asking the current python interpreter for its
# Python library directory
execute_process(COMMAND ${PYTHON_EXECUTABLE} -c
                        "from distutils.sysconfig import get_python_lib; print(get_python_lib())"
                 RESULT_VARIABLE RETURN_CODE
                 OUTPUT_VARIABLE PYTHON_LIB_DIR_DETECTED
                 OUTPUT_STRIP_TRAILING_WHITESPACE
               )

if (${RETURN_CODE} GREATER 0)
    message(FATAL_ERROR "Failed to determine python site package directory")
endif()

# Provide an option so users can override what we detected earlier
set(PYTHON_LIB_INSTALL_DIR "${PYTHON_LIB_DIR_DETECTED}" CACHE PATH "Installation directory for stp python package")

if (EXISTS "${PYTHON_LIB_INSTALL_DIR}")
    message(STATUS "Detected python site package directory ${PYTHON_LIB_INSTALL_DIR}")
else()
    message(FATAL_ERROR "Reported python site package directory '${PYTHON_LIB_INSTALL_DIR}' does not exist")
endif()

# Install main files
install(FILES stp.py __init__.py DESTINATION "${PYTHON_LIB_INSTALL_DIR}/stp")

# Generate and install file describing install location of stp shared library
get_target_property(LIBSTP_LOCATAION libstp LOCATION) # This the full path in the build directory
get_filename_component(LIBSTP_FILENAME "${LIBSTP_LOCATAION}" NAME)
set(LIBSTP_PATH ${CMAKE_INSTALL_PREFIX}/lib/${LIBSTP_FILENAME}) # FIXME: This is also set in libstp/CMakeLists.txt which could be fragile

configure_file(library_path.py.in "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/library_path.py" @ONLY)
install(FILES "${PROJECT_BINARY_DIR}/${CMAKE_FILES_DIRECTORY}/library_path.py"
        DESTINATION "${PYTHON_LIB_INSTALL_DIR}/stp"
       )
