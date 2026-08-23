Source code layout
==================

The ``lib/`` directory is organized into subdirectories for each distinct
component of STP. The headers that go with them live under
``include/stp/``.

-  ``AbsRefineCounterExample``: Functions related to abstraction
   refinement and counterexample construction.
-  ``AST``: Implements the abstract syntax tree for parsed solver
   inputs.
-  ``Extensionality``: The decision procedure for equalities between
   whole arrays, described in :doc:`array-extensionality`.
-  ``FloatBlaster``: Bit-blasting of the floating-point theories, built
   on the header-only SymFPU library.
-  ``Globals``: The handful of thread-local globals that the parser
   shares with the rest of STP.
-  ``Incremental``: The driver for incremental solving -- ``push``,
   ``pop`` and repeated ``check-sat`` against a solver kept alive between
   queries. See :doc:`incremental-solving`.
-  ``Interface``: Defines the C interface (``stp/c_interface.h``) for
   parsing input files, constructing expressions, executing queries,
   etc., and the C++ interface (``stp/cpp_interface.h``) for invoking
   STP.
-  ``NodeFactory``: Creates AST nodes. Which factory a client asks for
   decides how much work happens as nodes are built, from hash consing
   alone up to the rewriting done by ``SimplifyingNodeFactory``.
-  ``Parser``: Contains the parsers for the CVC, SMT-LIB1, and SMT-LIB2
   input formats.
-  ``Printer``: Implements various output formatters.
-  ``Sat``: Adapters presenting each supported SAT solver --
   `MiniSat <https://github.com/stp/minisat>`__,
   `CryptoMiniSat <https://github.com/msoos/cryptominisat>`__,
   `CaDiCaL <https://github.com/arminbiere/cadical>`__ and
   `Riss <https://github.com/nmanthey/riss-solver>`__ -- through STP's
   common ``SATSolver`` interface. The solvers themselves are external;
   only the wrappers live here.
-  ``Simplifier``: Simplification algorithms for the AST, including the
   constant bit propagator under ``constantBitP/``.
-  ``STPManager``: Class that holds all the components together.
-  ``ToSat``: Conversion of AST to SAT.
-  ``Util``: Handy utilities for smaller tasks.

Third-party code compiled into STP. Two of these are fetched during
configuration rather than living under ``lib/``, because STP builds them as
part of itself and so needs their sources present before it configures its
own targets; the other two are small enough to be carried in the tree:

-  ABC: The `ABC <https://github.com/berkeley-abc/abc>`__ package, used to
   build AIGs and convert them to CNF. Fetched from
   `stp/abc <https://github.com/stp/abc>`__ rather than from ABC itself. That fork keeps two branches: ``master`` mirrors upstream
   untouched, and ``stp`` -- the branch ``ABC_GIT_TAG`` in the top-level
   ``CMakeLists.txt`` pins a commit of -- carries our changes as commits on
   top of the upstream revision we have taken. Bumping ABC means rebasing
   ``stp`` onto a newer ``master`` in that repository, then moving that pin.

   To work on the fork, clone it and configure with
   ``-DFETCHCONTENT_SOURCE_DIR_ABC=<clone>``: the build then uses that
   checkout in place and fetches nothing, so it can be edited, committed and
   pushed from where it is.

   The fork exists because the changes cannot live upstream: some are fixes
   that were offered to ABC and not taken, and the rest adjust which parts of
   ABC get built. STP uses four of its packages -- ``aig/aig``, ``aig/gia``,
   ``opt/dar`` and ``sat/cnf`` -- and ABC's build compiles every other one
   too, including SAT solvers that STP already links its own copies of.
-  ``extlib-constbv``: A library that implements multi-word fixed-length
   integers, based on Steffen Beyer's
   `Bit::Vector <https://metacpan.org/pod/Bit::Vector>`__ perl module.
-  mimalloc: `mimalloc <https://github.com/microsoft/mimalloc>`__, the
   allocator the STP executables link against by default. Fetched, and
   built as part of STP; see ``STP_ALLOCATOR`` in :doc:`building` for the
   alternatives.
-  ankerl::unordered_dense:
   `a densely stored hash map and set <https://github.com/martinus/unordered_dense>`__,
   used in place of ``std::unordered_map`` where it pays off. A single
   header, fetched at a pinned release.

CLI11, the command-line parser of the ``stp`` executable, and SymFPU, the
header-only implementation of the floating-point operations in terms of
bitvectors that ``FloatBlaster`` uses, used to sit here as submodules too.
Both are now fetched by ``cmake/FindCLI11.cmake`` and
``cmake/FindSymFPU.cmake`` -- being headers, there is nothing about them
for STP's own build to reach into, which is what keeps ABC and mimalloc
here. STP's four local fixes to SymFPU live in ``cmake/deps-utils/symfpu``
and are applied to the copy the build fetches.

The executables are built from ``tools/``:

-  ``stp``: The main command-line solver.
-  ``extdiff``: Built alongside it, unconditionally. Compares two STP
   binaries on the same query, which the baseline-differential test uses.
-  ``test_fpbackend`` and ``test_fprewrites``: Floating-point checkers,
   built when either ``ENABLE_TESTING`` or ``BUILD_EXTRA_TOOLS`` is on;
   they are registered as tests.
-  The rest are development aids, built only when ``BUILD_EXTRA_TOOLS``
   is enabled: ``difficulty_bench`` measures the difficulty scorer against
   AIG sizes; ``fp_rewrite_gen`` searches for floating-point rewrite rules;
   ``rewrite_rule_gen`` searches for bitvector ones; and
   ``propagator_bench`` times the propagators, checks how much they deduce,
   and with ``--bcp-check`` compares that against what unit propagation on
   the bit-blasted encoding deduces on its own. ``propagator_bench``
   additionally needs a build with CryptoMiniSat and is skipped without
   one.

The Python bindings are in ``bindings/python``, and the tests are in
``tests/`` (see :doc:`testing`).
