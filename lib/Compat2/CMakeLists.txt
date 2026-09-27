# AUTHORS: Andrew Teylu
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

# libstp2: every function of include/stp/c_interface.h (the 2.x C API),
# re-implemented over the 3.x C API of include/stp/stp.h. It links libstp and
# nothing of the engine directly: the point of the library is that the public
# 3.x C surface suffices to carry the 2.x one. See NOTES.md in this directory.
#
# Built in every configuration. With STP_LEGACY_C_INTERFACE=ON libstp carries
# the same entry points itself and the two must not both be linked into one
# program; with it OFF this is the only provider, and the 2.x tests, tools and
# the ctypes Python package use it (see STP_LEGACY_C_LINK).
add_library(stp2
    c_interface2.cpp
    c_interface2_terms.cpp
)
add_dependencies(stp2 stp_api_tables)
target_link_libraries(stp2 PUBLIC stp)
target_compile_features(stp2 PRIVATE cxx_std_17)
# The build-of-the-library side of the DLL_PUBLIC switch in c_interface.h (see
# the note in lib/CMakeLists.txt; inert outside MSVC).
target_compile_definitions(stp2 PRIVATE STP_EXPORTS)
set_target_properties(stp2 PROPERTIES
    VERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
    SOVERSION ${PROJECT_VERSION_MAJOR}.${PROJECT_VERSION_MINOR}
)
if(WIN32)
    set_target_properties(stp2 PROPERTIES OUTPUT_NAME stp2win)
else()
    set_target_properties(stp2 PROPERTIES OUTPUT_NAME stp2)
endif()
# The library needs libstp next to it at run time. In the install tree the two
# land in the same directory, which $ORIGIN names wherever the tree is moved.
if(BUILD_SHARED_LIBS AND UNIX AND NOT APPLE)
    set_target_properties(stp2 PROPERTIES INSTALL_RPATH "$ORIGIN")
endif()

install(TARGETS stp2
    EXPORT ${STP_EXPORT_NAME}
    LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    ARCHIVE DESTINATION "${CMAKE_INSTALL_LIBDIR}"
    RUNTIME DESTINATION "${CMAKE_INSTALL_LIBDIR}"
)
