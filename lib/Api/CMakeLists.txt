#********************************************************************
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
#********************************************************************
# The STP 3.x API: the C++ core over the engine (this directory), the C layer
# (c/) and the generated tables. Everything is compiled into libstp itself.

set(STP_API_TABLES
    ${CMAKE_CURRENT_SOURCE_DIR}/tables/kinds.toml
    ${CMAKE_CURRENT_SOURCE_DIR}/tables/options.toml
    ${CMAKE_CURRENT_SOURCE_DIR}/tables/errors.toml
    ${CMAKE_CURRENT_SOURCE_DIR}/tables/statistics.toml
)
set(STP_API_GEN_DIR ${PROJECT_BINARY_DIR}/generated)
set(STP_API_GENERATED
    ${STP_API_GEN_DIR}/include/stp/api/gen/kinds.hpp
    ${STP_API_GEN_DIR}/include/stp/api/gen/kind_ctors.hpp
    ${STP_API_GEN_DIR}/include/stp/api/gen/kind_ctor_templates.hpp
    ${STP_API_GEN_DIR}/include/stp/api/gen/options.hpp
    ${STP_API_GEN_DIR}/include/stp/api/gen/errors.hpp
    ${STP_API_GEN_DIR}/include/stp/api/gen/kinds.h
    ${STP_API_GEN_DIR}/include/stp/api/gen/kind_ctors.h
    ${STP_API_GEN_DIR}/include/stp/api/gen/options.h
    ${STP_API_GEN_DIR}/include/stp/api/gen/errors.h
    ${STP_API_GEN_DIR}/lib/Api/gen/kind_table.inc
    ${STP_API_GEN_DIR}/lib/Api/gen/kind_ctors.inc
    ${STP_API_GEN_DIR}/lib/Api/gen/kind_ctors_c.inc
    ${STP_API_GEN_DIR}/lib/Api/gen/option_table.inc
    ${STP_API_GEN_DIR}/lib/Api/gen/option_apply.inc
    ${STP_API_GEN_DIR}/lib/Api/gen/option_defaults.inc
    ${STP_API_GEN_DIR}/lib/Api/gen/cli_table.inc
    ${STP_API_GEN_DIR}/lib/Api/gen/error_table.inc
    ${STP_API_GEN_DIR}/lib/Api/gen/stat_table.inc
    ${STP_API_GEN_DIR}/python/_gen_enums.pxi
    ${STP_API_GEN_DIR}/python/_gen_kinds.py
)
add_custom_command(
    OUTPUT ${STP_API_GENERATED}
    COMMAND ${PYTHON_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/gen/generate.py
            --tables ${CMAKE_CURRENT_SOURCE_DIR}/tables --out ${STP_API_GEN_DIR}
    DEPENDS ${STP_API_TABLES} ${CMAKE_CURRENT_SOURCE_DIR}/gen/generate.py
    COMMENT "Generating the STP 3.x API tables"
    VERBATIM
)
add_custom_target(stp_api_tables DEPENDS ${STP_API_GENERATED})

# The 3.x version header.
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/version.hpp.in
               ${STP_API_GEN_DIR}/include/stp/api/version.hpp @ONLY)

add_library(stpapi OBJECT
    Errors.cpp
    Manager.cpp
    Terms.cpp
    Construct.cpp
    Options.cpp
    Solver.cpp
    Model.cpp
    Library.cpp
    Output.cpp
    c/stp_c.cpp
    c/stp_c_options.cpp
    c/stp_c_solver.cpp
)
add_dependencies(stpapi ASTKind_header stp_api_tables)
# The objects that define the 3.x API's exported functions: on Windows their
# declarations are dllexport while libstp is a DLL (see STP_API in stp.h).
# Not STP_EXPORTS, which libstp2 defines too and would then export libstp's
# functions as its own.
target_compile_definitions(stpapi PRIVATE STP_API3_BUILDING)
# The option registry and capabilities() answer for the build they are in:
# the same HiGHS macros the LRA objects and the stp binary see.
if(ENABLE_HIGHS)
    target_compile_definitions(stpapi PRIVATE STP_HAVE_HIGHS)
    if(ENABLE_HIGHS_CUT_LOG)
        target_compile_definitions(stpapi PRIVATE STP_HAVE_HIGHS_CUT_LOG)
    endif()
endif()
target_include_directories(stpapi PRIVATE
    ${STP_API_GEN_DIR}/include
    ${STP_API_GEN_DIR}/lib/Api
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(stpapi PRIVATE IMath)
if(TARGET cryptominisat5)
    target_link_libraries(stpapi PRIVATE cryptominisat5)
endif()

set(STP_API_PUBLIC_HEADERS
    ${PROJECT_SOURCE_DIR}/include/stp/stp.hpp
    ${PROJECT_SOURCE_DIR}/include/stp/stp.h
    PARENT_SCOPE
)
set(STP_API_GEN_DIR ${STP_API_GEN_DIR} PARENT_SCOPE)
