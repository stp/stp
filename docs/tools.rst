Developer tools
===============

Besides ``stp`` itself (:doc:`command-line`), the ``tools/`` directory
holds programs for working on STP: searches for rewrite rules the
simplifier is missing, benchmarks of its propagators and of its size
estimate, and self-tests. None of them is installed. They are built into
the build directory by the targets named below, and they fall into three
groups by what switches them on:

.. list-table::
   :header-rows: 1
   :widths: 30 34 36

   * - Program
     - Built with
     - Purpose
   * - ``extdiff``
     - every build
     - C API observation driver for a differential test
   * - ``test_fpbackend``
     - ``ENABLE_TESTING`` or ``BUILD_EXTRA_TOOLS``
     - self-test of the floating-point circuit backend
   * - ``test_fprewrites``
     - ``ENABLE_TESTING`` or ``BUILD_EXTRA_TOOLS``
     - exhaustive check of the floating-point rewrite rules
   * - ``c_handle_churn_benchmark``
     - ``ENABLE_TESTING`` or ``BUILD_EXTRA_TOOLS``
     - cost of creating and releasing C API handles
   * - ``rewrite_rule_gen``
     - ``BUILD_EXTRA_TOOLS`` and CryptoMiniSat
     - search for bit-vector rewrite rules
   * - ``fp_rewrite_gen``
     - ``BUILD_EXTRA_TOOLS``
     - search for floating-point rewrite rules
   * - ``propagator_bench``
     - ``BUILD_EXTRA_TOOLS`` and CryptoMiniSat
     - speed and precision of the propagators
   * - ``difficulty_bench``
     - ``BUILD_EXTRA_TOOLS``
     - accuracy of the difficulty estimate

.. code-block:: bash

    ./configure.sh release -DBUILD_EXTRA_TOOLS=ON
    cmake --build build --target difficulty_bench

Build the benchmarks as Release: a Debug build times the assertions, not
the code under test.

Rewrite-rule searches
---------------------

``rewrite_rule_gen``
~~~~~~~~~~~~~~~~~~~~

Discovers bit-vector rewrite rules for the simplifier to adopt. It
enumerates small terms, groups those that agree on a set of sample
assignments, proves each candidate equality with the SAT solver at
increasing widths, and keeps the rules that survive. The rule set lives
in ``rules_new.smt2`` in the current directory, one rule per frame, and
is read from and written back to there.

.. code-block:: text

    rewrite_rule_gen                     search for new rules, unbounded
    rewrite_rule_gen generate D N        search to depth D, or until N rules
    rewrite_rule_gen verify [FILE]       SAT-check every rule in FILE
    rewrite_rule_gen expand MS [FILE]    check the rules at wider widths,
                                         MS milliseconds each
    rewrite_rule_gen rewrite             apply the rule set to itself
    rewrite_rule_gen write-out           re-emit the rules, with their C++ form
    rewrite_rule_gen missed-constants [V A]
                                         report two-level terms over V variables
                                         the node factory leaves unfolded
                                         though they can take only one value
    rewrite_rule_gen unit-test           check the commutative matcher
    rewrite_rule_gen test                check the rule properties

The unbounded search can run for a long time before it reports anything.
CI runs ``unit-test``, ``test``, ``verify`` on
``tools/rewrite_rule_gen/test-rules.smt2`` and ``generate 5 3``.

``fp_rewrite_gen``
~~~~~~~~~~~~~~~~~~

The floating-point counterpart. Every depth-1 term and predicate over one
float variable, the five rounding modes and a pool of special constants
(NaN, ±∞, ±0, ±1) is evaluated on every float of a small format. A term
whose values match those of a cheaper form -- a constant, ``x``,
``(fp.neg x)``, ``(fp.isNaN x)`` and so on -- is a candidate rule. Each hit
is confirmed on a second format and then rebuilt through the simplifying
node factory, and what the factory does not already rewrite is reported.
Depth 2 nests one inner term, such as ``(fp.abs x)`` or
``(fp.roundToIntegral rm x)``, inside each operation.

.. code-block:: bash

    fp_rewrite_gen        # both depths
    fp_rewrite_gen 1      # depth 1 only
    fp_rewrite_gen 2      # depth 2 only

Benchmarks
----------

``propagator_bench``
~~~~~~~~~~~~~~~~~~~~

Times one transfer function at a time -- constant-bit propagation
(``cbitp``), interval analysis (``interval``) or value-set analysis
(``valueset``) -- over random cases at a chosen width and density of
known input bits. It reports operations per second, the bits each call
deduced, and whether the propagator is maximally precise: checked
exhaustively at a small width, and optionally against the SAT solver at
the benchmarked width. ``--bcp-check`` compares a propagator with what
unit propagation deduces on the bit-blasted CNF instead.

.. code-block:: bash

    propagator_bench --list
    propagator_bench --domains cbitp --ops bvsgt --widths 64 --probs 50 \
                     --directions bottom-up
    propagator_bench --html report.html --csv report.csv   # everything

|propbench|_ explains every column and the caveats worth knowing before
quoting a number.

``difficulty_bench``
~~~~~~~~~~~~~~~~~~~~

STP estimates how many AIG nodes a formula will bit-blast to, and reverts
simplifications that made that estimate worse. This measures the estimate
against the real count, one operation at a time over fresh symbols, and
prints both with their ratio. The constants in
``lib/Simplifier/DifficultyScore.cpp`` were fitted to its output; re-run it
after changing the bit-blaster.

.. code-block:: bash

    difficulty_bench                        # everything, at 8 to 128 bits
    difficulty_bench --widths 32 --no-fp    # bit-vector operations only
    difficulty_bench --no-bv                # floating-point operations only
    difficulty_bench --csv > measured.csv   # for re-fitting

See |diffbench|_.

``c_handle_churn_benchmark``
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Creates the same bit-vector constant through the C API and releases its
handle, a million times by default, and prints the time taken and the
peak memory:

.. code-block:: text

    $ c_handle_churn_benchmark --iterations 1000000
    mode=legacy iterations=1000000 seconds=... peak_rss_kib=...

``--uf`` turns on uninterpreted-function support first, which keeps a
registry of live handles, and measures that path instead. Compare the median of several fresh runs of
each mode; |churnbench|_ has the recipe.

Tests
-----

``test_fpbackend`` and ``test_fprewrites`` are self-tests that exit
non-zero on failure, and ``ctest`` runs both (:doc:`testing`).
``test_fpbackend`` checks the bit-vector backend SymFPU builds its
floating-point circuits from, operation by operation, against values
worked out by hand. ``test_fprewrites`` checks each floating-point
rewrite in the simplifying node factory by requiring the rewritten and
unrewritten terms to agree on every float of a small format -- zeros,
subnormals, infinities and NaNs included.

``extdiff`` prints what the C API reports about a fixed set of array
queries: status, counterexample-array entries and their values. The
differential test builds it against the current tree and against a
baseline commit, runs both with ``--array-equality`` off, and requires
byte-identical output, so the array-equality feature cannot change
behaviour for callers who do not ask for it. It takes no arguments.

.. |propbench| replace:: ``tools/propagator_bench/README.md``
.. _propbench: https://github.com/stp/stp/blob/master/tools/propagator_bench/README.md

.. |diffbench| replace:: ``tools/difficulty_bench/README.md``
.. _diffbench: https://github.com/stp/stp/blob/master/tools/difficulty_bench/README.md

.. |churnbench| replace:: ``tools/c_handle_churn_benchmark/README.md``
.. _churnbench: https://github.com/stp/stp/blob/master/tools/c_handle_churn_benchmark/README.md
