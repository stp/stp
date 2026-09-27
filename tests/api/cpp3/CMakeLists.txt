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
# -----------------------------------------------------------------------------
# Tests of the 3.x C++ API (<stp/stp.hpp>). GTest files go through
# AddSTPGTest; smoke.cpp is a plain program with its own pass/fail exit code.
# -----------------------------------------------------------------------------
add_executable(api3-smoke smoke.cpp)
target_link_libraries(api3-smoke stp)
add_test(NAME api3-smoke COMMAND api3-smoke)

# The GoogleTest suites, one per area of the header. Every file includes
# api3_common.hpp from this directory.
AddSTPGTest(api3-kinds.cpp)
AddSTPGTest(api3-sorts.cpp)
AddSTPGTest(api3-values.cpp)
AddSTPGTest(api3-options.cpp)
AddSTPGTest(api3-solver.cpp)
AddSTPGTest(api3-solvers.cpp)
AddSTPGTest(api3-models.cpp)
AddSTPGTest(api3-parsing.cpp)
AddSTPGTest(api3-errors.cpp)
AddSTPGTest(api3-engine-failure.cpp)
AddSTPGTest(api3-rosetta.cpp)

# The registry against the engine and the command line generated from it:
# reads lib/Api/Internal.h, the in-tree view tools/stp/main.cpp registers from.
AddSTPGTest(api3-registry.cpp)
target_include_directories(api3-registryTests PRIVATE ${PROJECT_SOURCE_DIR}/lib)
add_dependencies(api3-registryTests stp_api_tables)

# The stp binary's command line is generated from options.toml: its --help
# must list every entry with a CLI form, every alias and short flag, and every
# frontend row, and a sample of spellings must parse.
if(BUILD_EXECUTABLES)
    add_test(NAME api3-cli-help
             COMMAND ${PYTHON_EXECUTABLE}
                     ${PROJECT_SOURCE_DIR}/lib/Api/gen/check_cli_help.py
                     --stp $<TARGET_FILE:stp-bin>
                     --tables ${PROJECT_SOURCE_DIR}/lib/Api/tables)
endif()
