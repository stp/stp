Source code layout
==================

The ``lib/`` directory is organized into subdirectories for each distinct
component of STP. The headers that go with them live under
``include/stp/``.

-  ``AbsRefineCounterExample``: Functions related to abstraction
   refinement and counterexample construction.
-  ``AST``: Implements the abstract syntax tree for parsed solver
   inputs.
-  ``Globals``: The handful of thread-local globals that the parser
   shares with the rest of STP.
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

Third-party code that is compiled into STP also lives under ``lib/``:

-  ``extlib-abc``: The `ABC <https://github.com/berkeley-abc/abc>`__
   package, used to build AIGs and convert them to CNF. A git submodule.
-  ``extlib-constbv``: A library that implements multi-word fixed-length
   integers, based on Steffen Beyer's
   `Bit::Vector <https://metacpan.org/pod/Bit::Vector>`__ perl module.
-  ``extlib-mimalloc``:
   `mimalloc <https://github.com/microsoft/mimalloc>`__, the allocator
   the STP executables link against by default. A git submodule; see
   ``STP_ALLOCATOR`` in the README for the alternatives.
-  ``extlib-unordered-dense``:
   `ankerl::unordered_dense <https://github.com/martinus/unordered_dense>`__,
   a densely stored hash map and set, used in place of
   ``std::unordered_map`` where it pays off.

The executables are built from ``tools/``:

-  ``stp``: The main command-line solver.
-  ``stp_simple``: A cut-down front end that accepts a single SMT-LIB2
   file (or stdin) and no other options. Setting ``ONLY_SIMPLE`` builds
   this instead of ``stp``, which drops the dependency on Boost.
-  The rest are development aids, built only when ``BUILD_EXTRA_TOOLS``
   is enabled: ``propagator_bench`` times the propagators and checks how
   much they deduce, ``measure_constantbitprop`` compares that against
   what unit propagation on the bit-blasted encoding deduces, and
   ``rewrite_rule_gen`` searches for rewrite rules.

The Python bindings are in ``bindings/python``, and the tests are in
``tests/`` (see :doc:`testing`).
