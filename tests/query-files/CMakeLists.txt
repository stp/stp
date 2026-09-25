# AUTHORS: Dan Liew, Ryan Govostes, Mate Soos
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

set(STP_EXECUTABLE_PATH "$<TARGET_FILE:stp-bin>")

# A Python literal for lit.site.cfg.in: CMake booleans render as ON/OFF.
if (USE_MINISAT)
    set(STP_MINISAT_PYBOOL "True")
else()
    set(STP_MINISAT_PYBOOL "False")
endif()
if (USE_CADICAL)
    set(STP_CADICAL_PYBOOL "True")
else()
    set(STP_CADICAL_PYBOOL "False")
endif()
if (CADICAL_HAS_INPROBING)
    set(STP_CADICAL_INPROBING_PYBOOL "True")
else()
    set(STP_CADICAL_INPROBING_PYBOOL "False")
endif()
# The 3.x line as a whole: what the whole-trail reuse (ilb=2) and the
# decision hints need, and what CADICAL_HAS_FACTOR is decided from.
if (CADICAL_HAS_FACTOR)
    set(STP_CADICAL_3_PYBOOL "True")
else()
    set(STP_CADICAL_3_PYBOOL "False")
endif()
# Whether the backend a query gets when its RUN line names none can host the
# theory propagator. That backend is CryptoMiniSat when it is compiled in,
# else CaDiCaL, else MiniSat (UserDefinedFlags.h). CaDiCaL always can,
# CryptoMiniSat only when built with the interface, and MiniSat never.
if (STP_BUILD_WITH_CRYPTOMINISAT)
    set(_stp_default_backend_propagates "${CRYPTOMINISAT_HAS_UP}")
elseif (STP_BUILD_WITH_CADICAL)
    set(_stp_default_backend_propagates TRUE)
else()
    set(_stp_default_backend_propagates FALSE)
endif()
if (_stp_default_backend_propagates)
    set(STP_DEFAULT_BACKEND_PROPAGATOR_PYBOOL "True")
else()
    set(STP_DEFAULT_BACKEND_PROPAGATOR_PYBOOL "False")
endif()

# Create llvm-lit configuration file
configure_file(lit.site.cfg.in lit.site.cfg.g @ONLY)
file(GENERATE OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/$<CONFIG>.site.cfg
              INPUT ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg.g)

add_test(NAME query-files
    COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG> .
    WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
)

# CaDiCaL's bounded variable addition is on by default, so the run above
# already covers the declare/translate machinery across the whole corpus --
# every STP variable travels through the translation table there. What it no
# longer covers is the other side of the switch, so the sweep forces the
# factor off instead: the untranslated path has to keep answering identically.
# Only registered when the flag can engage at all; on pre-3.0 CaDiCaL builds
# the factor is never on in the first place and the sweep would just repeat
# the run above.
if (USE_CADICAL AND CADICAL_HAS_FACTOR)
    add_test(NAME query-files-cadical-factor-off
        COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG>
                --param solver_params=--cadical-factor=off .
        WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    )
    # Both lit invocations write per-test Output/ files into this same
    # directory, so running them concurrently under ctest -j corrupts each
    # other's results. Serialise them against each other (only).
    set_tests_properties(query-files query-files-cadical-factor-off
        PROPERTIES RESOURCE_LOCK query-files-exec-root
    )
endif()

# The refinement loop keeps CaDiCaL's trail between its rounds by default, so
# the run above already covers every verdict reached across a kept trail.
# What it no longer covers is the other side of the switch, so this sweep
# forces the trail dropped instead: the re-descending path has to keep
# answering identically.
if (USE_CADICAL)
    add_test(NAME query-files-refinement-trail-reuse-off
        COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG>
                --param solver_params=--refinement-trail-reuse=0 .
        WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    )
    set_tests_properties(query-files-refinement-trail-reuse-off
        PROPERTIES RESOURCE_LOCK query-files-exec-root
    )
endif()

# The array index hints are off by default, so nothing above drives
# CaDiCaL's external propagator. This sweep decides every array's read
# indices through it on every query in the corpus: the propagator's
# bookkeeping of what is assigned has to agree with CaDiCaL's on every
# search shape here, or CaDiCaL rejects a proposed decision outright.
if (USE_CADICAL)
    add_test(NAME query-files-array-index-hints-decide
        COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG>
                --param solver_params=--array-index-hints=decide .
        WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
    )
    set_tests_properties(query-files-array-index-hints-decide
        PROPERTIES RESOURCE_LOCK query-files-exec-root
    )
endif()

# The linear-arithmetic files under every backend that can host the theory
# propagator: the propagator is the same
# code above both solvers, and each solver's bridge is what these sweeps
# exercise. A CryptoMiniSat built without the interface is left out, as is
# MiniSat, which hosts no propagator: the theory runs full-lazy on them.
# The sweep above already runs these files under the default backend, so
# when that is the only backend listed nothing new is registered here. A
# test that names a backend of its own would clash with the flag appended
# here; none of the lra-* files does. Every backend listed hosts the
# propagator, and each run tells lit so (backend_propagator=1): a file that
# requires one runs here even when the default backend cannot host it.
file(GLOB _stp_lra_query_files CONFIGURE_DEPENDS
     RELATIVE "${CMAKE_CURRENT_SOURCE_DIR}" "lra-*.smt2")
set(_stp_lra_backends "")
if (USE_CADICAL)
    list(APPEND _stp_lra_backends "--cadical")
endif()
if (STP_BUILD_WITH_CRYPTOMINISAT AND CRYPTOMINISAT_HAS_UP)
    list(APPEND _stp_lra_backends "--cryptominisat")
endif()
list(LENGTH _stp_lra_backends _stp_lra_backend_count)
# A default backend that can host the propagator is on the list, and a list
# of one is then that backend alone. One that cannot is not on it.
if (_stp_lra_query_files AND
    (_stp_lra_backend_count GREATER 1 OR
     (_stp_lra_backend_count EQUAL 1 AND NOT _stp_default_backend_propagates)))
    set(_stp_lra_query_paths "")
    foreach(_file ${_stp_lra_query_files})
        list(APPEND _stp_lra_query_paths "./${_file}")
    endforeach()
    foreach(_backend ${_stp_lra_backends})
        string(REGEX REPLACE "^--" "" _backend_name "${_backend}")
        set(_name "lra-query-files-${_backend_name}")
        add_test(NAME ${_name}
            COMMAND ${LIT_TOOL} ${LIT_ARGS} --config-prefix=$<CONFIG>
                    --param "solver_params=${_backend}"
                    --param backend_propagator=1
                    ${_stp_lra_query_paths}
            WORKING_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
        )
        set_tests_properties(${_name}
            PROPERTIES RESOURCE_LOCK query-files-exec-root
        )
    endforeach()
endif()
