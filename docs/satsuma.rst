Satsuma CNF preprocessing
=========================

Satsuma optionally preprocesses STP's complete CNF before it is loaded into
the SAT backend. It uses an output callback inside the process, with no
temporary DIMACS file or preprocessing subprocess. The same adapter supports
CaDiCaL and CryptoMiniSat. Both the build option and runtime option are off
by default; this is an experimental pipeline.

Build and use
-------------

.. code-block:: bash

   cmake -S . -B build -DENABLE_AUTO_DOWNLOAD=ON -DUSE_SATSUMA=ON
   cmake --build build --parallel
   build/stp --satsuma=lex problem.smt2
   build/stp --satsuma=fix problem.smt2

``USE_SATSUMA`` requires a C++20 compiler for the SAT adapter. CMake builds
the pinned ``stp/satsuma`` dependency through ``Satsuma-EP`` and installs its
header API and pinned Dejavu headers into ``STP_DEP_DIR``. The revision is
in ``cmake/FindSatsuma.cmake``. Dependency changes are commits in the fork;
STP does not apply patches during its build. A separately installed copy
can be selected with ``-DSATSUMA_DIR=/path/to/prefix``. An ordinary Satsuma
installation without the CNF output API is rejected during configuration.

The runtime option is ``satsuma=off|lex|fix``. API clients can set it through
``options.set("satsuma", "lex")`` before their first check. Explicit backend
selection is supported: ``--cadical`` or ``--cryptominisat`` on the CLI,
and ``options.set("sat-backend", "cadical")`` in the C++ API.

Lex uses unit propagation, removed-variable units, a component limit of
500,000, an order-model budget of 750,000, and a dense-model budget of
20,000,000. Fix additionally enables iterative orbitopal, Schreier, and
negation fixing, with pure-literal preprocessing. Cliquer is disabled.
The output contains the simplified formula and symmetry-breaking clauses;
its size can grow, and solving it can be slower than solving the original.

Model preservation and supported queries
----------------------------------------

Original variable numbers are retained, extension variables are allocated
before clauses are loaded, and removed assignments are restored as unit
clauses. STP can therefore read a model of its original encoding.

Preprocessing is restricted to a complete batch encoding on a fresh SAT
backend. Incremental sessions, assumptions, auxiliary solvers, and queries
requiring array, BV, FP, UF, or LRA refinement bypass it. An abstraction's
symmetry may be invalidated by later refinement clauses. Merely freezing
variables would not make permanent symmetry breaking sound in that case.
Surviving array operations or an active equality registry also force bypass.
Formulas with at least five million variables, or beyond integer arena
size limits, use ordinary clause loading.

Eligibility depends on the encoding path, rather than the declared SMT
logic. QF_ABV and QF_ABVFP queries can use Satsuma when the early eager
array pass removes their array operations, floating-point operations are
encoded exactly, and no other refinement source is active. Queries using
lazy array reads, lazy array equality, or FP abstraction bypass it. This
restriction applies regardless of the SAT backend. With ``-s``, the
``satsuma: mode=...`` or ``satsuma: skipped ...`` line reports whether
preprocessing ran when CNF reached clause loading.

STP polls its preparation budget while translating and loading clauses and
before and after Satsuma. Satsuma's core currently has no cooperative
wall-clock cancellation hook. An external process watchdog is needed to
enforce a strict complete-process cutoff. Large formulas can exhaust memory;
Dejavu's allocation handling can crash under an address-space limit.
Proof production and a combined STP/Satsuma proof are not supported here.

Testing and performance
-----------------------

.. code-block:: bash

   cmake -S . -B build -DENABLE_AUTO_DOWNLOAD=ON -DUSE_SATSUMA=ON \
     -DENABLE_TESTING=ON -DUSE_CADICAL=ON -DUSE_CRYPTOMINISAT=ON
   cmake --build build --parallel
   ctest --test-dir build -L satsuma --output-on-failure

The tests run both backends through off, lex, and fix modes. They include
exhaustive Boolean oracles, pigeonhole symmetry, original-model checking,
floating-point arithmetic, refinement bypass, incremental push/pop, and a
standalone public C++ API client. The fork separately compares callback
output byte for byte against its original DIMACS output path.

The prototype experiment on 63,441 non-incremental QF_BV/QF_BVFP files,
using CaDiCaL 3.0.1, had the following PAR2 at a 60-second end-to-end cutoff
and a 10 GiB virtual-address-space limit. Every unsuccessful run cost 120
seconds, and each configuration ran once per file.

.. csv-table:: Prototype experiment
   :header: "Configuration", "Solved", "PAR2 seconds"

   off, 62526, 2.217422
   lex, 62438, 2.431454
   fix, 62294, 2.971489

These are measurements of the prototype revision, not a benchmark of this
upstream integration branch. They motivate keeping the feature optional;
they do not establish a useful policy for automatically selecting it.
