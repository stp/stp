Running STP
===========

``stp`` is the solver's command-line front end, and the only program an
installation puts on the path. It reads one problem, from a file or from
standard input, and writes the answer to standard output:

.. code-block:: text

    stp [options] [input-file]

``stp --help`` lists every option, with its default where it has one,
and ``man stp`` shows the same list where the manpage was installed -- on
Linux, a build makes it whenever ``help2man`` is available.
``stp --version`` prints the version, the commit it was built from, the
build configuration and the SAT solvers compiled in.

Input
-----

With no file named, ``stp`` reads standard input. The input is SMT-LIB2,
whatever the file is called; ``--SMTLIB2`` is accepted, and changes
nothing. (Releases up to 2.4 also read STP's original CVC language and the
pre-2010 SMT-LIB1 format.)

.. code-block:: bash

    stp problem.smt2
    stp < problem.smt2

Output
------

An SMT-LIB2 input is a script, and STP answers its commands as it reaches
them: ``sat``, ``unsat`` or ``unknown`` for each ``(check-sat)``, and the
responses to ``(get-model)`` and ``(get-value ...)``. Those two need
``(set-option :produce-models true)`` before ``set-logic``, or ``-p`` or
``-d`` on the command line, and require a current satisfiable context.
Without the option, they report an error and end the script.
:doc:`smtlib27` describes the command modes and other compatibility rules.

.. code-block:: text

    $ cat example.smt2
    (set-option :produce-models true)
    (set-logic QF_BV)
    (declare-fun x () (_ BitVec 8))
    (declare-fun y () (_ BitVec 8))
    (assert (= (bvadd x y) #x10))
    (assert (bvugt x #x0c))
    (check-sat)
    (get-value (x))
    (exit)
    $ stp example.smt2
    sat
    (
    ( |x|  #xFF )
    )

``-p`` (``--print-counterex``) prints a model with every satisfiable
answer without the input asking for one, as ``define-fun`` lines after
the answer.

Exit status
~~~~~~~~~~~

``stp`` exits with 0 once it has read and answered the input, whatever
the answers were -- ``unsat`` and ``unknown`` included. It exits
non-zero when it could not: usually with 255, for an unreadable file, an
unknown or conflicting option, or an input it rejected. STP stops at the first error in an SMT-LIB2 script, usually
printing an ``(error "...")`` response saying why; answers already given
to earlier ``(check-sat)`` commands stand. Read the answers from standard
output, not from the exit status.

Driving STP over a pipe
-----------------------

When it reads standard input, ``stp`` reads SMT-LIB2 a character at a
time, so a program can write one command, wait for the answer and write
the next:

.. code-block:: text

    (set-logic QF_BV)
    (declare-fun x () (_ BitVec 4))
    (assert (= x #x3))
    (check-sat)          ; answers sat
    (push 1)
    (assert (= x #x4))
    (check-sat)          ; unsat
    (pop 1)
    (check-sat)          ; sat
    (exit)

``--interactive=false`` reads standard input in blocks instead, which is
faster when the whole script is already there; ``--interactive=true``
does the reverse for a named file, such as a FIFO. Both are for
SMT-LIB2 only. STP can keep the SAT
solver and the encoding between the checks of a script like this one;
:doc:`incremental-solving` describes when it does, and the
``--incremental`` option that controls it.

Choosing a SAT solver
---------------------

STP translates what its preprocessing leaves into SAT. Which SAT solvers
are available depends on how STP was built (:doc:`building`);
``stp --version`` lists them on the ``STP SAT solvers`` line. When more
than one is compiled in, STP uses CryptoMiniSat, then CaDiCaL, then
MiniSat, whichever it finds first. One flag picks another for a run:

.. list-table::
   :header-rows: 1
   :widths: 30 70

   * - Option
     - Solver
   * - ``--cadical``
     - CaDiCaL
   * - ``--cryptominisat``
     - CryptoMiniSat; ``--threads N`` runs it with *N* threads, and is
       refused with any other solver
   * - ``--minisat``
     - MiniSat
   * - ``--simplifying-minisat``
     - MiniSat with its variable elimination

The flags exclude one another, and ``--sat-backend`` names the solver
instead (``cryptominisat``, ``cadical``, ``minisat`` or
``simplifying-minisat``; ``auto``, the default, is the order above), as the
API's ``sat-backend`` option does. ``--search-bias unsat`` tunes the solver
for problems that are expected to be unsatisfiable, such as verification
conditions, and ``--search-bias sat`` for the reverse; a solver with no
such setting warns and ignores it.

Limits
------

``-k N`` (``--max-time``) gives each check *N* seconds, counted from
its start and so including preprocessing and building the CNF. ``-g N``
(``--max-num-confl``) gives each call into the SAT solver *N* conflicts;
a check that refines its encoding makes several calls. A check that runs
out answers ``unknown``. Parsing is not counted, and the deadline is
tested between stages rather than enforced, so a hard wall-clock limit
still needs ``timeout(1)`` or similar around ``stp``.

Stack size
----------

STP recurses over the formula, and deeply nested inputs can overflow the
8 MB stack most Linux systems give a process by default. The symptom is a
segmentation fault. Raise the limit in the shell that runs ``stp``:

.. code-block:: bash

    ulimit -s 80000      # about 80 MB

Checking and statistics
-----------------------

.. list-table::
   :header-rows: 1
   :widths: 34 66

   * - Option
     - Effect
   * - ``-d``, ``--check-sanity``
     - build each satisfying assignment and check it against the input
       before answering
   * - ``-t``, ``--print-quickstat``
     - print the time spent in each stage, and the process's peak
       memory, to standard error after each check
   * - ``-s``, ``--print-functionstat``
     - trace the solve: node counts after each simplification on
       standard output, mixed with the answers, and what each pass did on
       standard error
   * - ``--parse-only``
     - read the input without solving it: an SMT-LIB2 script's other
       commands still run, but ``(check-sat)`` does not; with ``-t``,
       time the parse

Controlling preprocessing
-------------------------

STP simplifies the formula at the word level before bit-blasting it. The
``Simplifications`` group of ``stp --help`` switches individual passes on
and off. The broad switches are:

.. list-table::
   :header-rows: 1
   :widths: 34 66

   * - Option
     - Effect
   * - ``--disable-simplifications``
     - turn off the word-level simplifications listed with it in the
       help
   * - ``--size-reducing-only``
     - turn off the simplifications that can enlarge the formula
   * - ``-a``, ``--disable-opt-inc``
     - turn off the rewriting simplifier
   * - ``-w``, ``--switch-word``
     - turn off the word-level equation solver
   * - ``--disable-cbitp``
     - turn off constant bit propagation
   * - ``--disable-equality``
     - turn off equality propagation

An option that takes a value accepts it either separately or after
``=`` -- ``--flattening 0`` and ``--flattening=false`` are the same --
except ``--incremental``, whose value must follow ``=``. Contradictory
options are rejected rather than one silently winning:
``--disable-simplifications --flattening 1`` is an error.

:doc:`architecture` describes the passes these options control.

Writing CNF
-----------

``--output-CNF`` writes the CNF STP hands to the SAT solver as DIMACS
files named ``output_0.cnf``, ``output_1.cnf`` and so on, one per
check, in the current directory, replacing any a previous run left. Its
variables cannot be mapped back to the input's. A check that
preprocessing answers on its own reaches no SAT solver and writes no
file, and neither does a check solved incrementally
(:doc:`incremental-solving`). Under lazy array-read refinement or a
bit-vector abstraction the file is not the whole problem, and a warning
says so: ``--ackermanize`` completes it for arrays.

``--exit-after-CNF`` exits, with no answer, once the first CNF is built;
the two options together turn a single-check problem into DIMACS.
``--cnf-generation-effort`` trades the time spent minimising the CNF
against its size. ``--cnf-link-shared-cells`` makes the ``new-*`` rungs
keep a comparator cell propagation-complete when its exclusive-or has
another reader, at the price of a few more clauses.

Other options
-------------

The ``Bit-blasting options`` group (``--bb.*``) chooses how each
operation is encoded as CNF; it has no page of its own, and
``stp --help`` describes each option. The ``--cadical-*`` options in the
``SAT Solver options`` group tune CaDiCaL, and the rest of the
``Printing options`` group are debugging aids. ``-r``
(``--ackermanize``) expands every array read eagerly, instead of
refining array reads lazily as STP does by default.

Options for particular theories are spread through ``stp --help``; each
theory's page covers its own:

.. list-table::
   :header-rows: 1
   :widths: 40 60

   * - Page
     - Options
   * - :doc:`array-extensionality`
     - ``--array-equality``, for equalities between whole arrays
   * - :doc:`uninterpreted-functions`
     - ``--uninterpreted-functions`` and the ``--uf-*`` options
   * - :doc:`incremental-solving`
     - ``--incremental`` and the ``--incremental-*`` options
   * - :doc:`bv-abstraction`
     - ``--bv-eq-abstraction`` and ``--bv-term-abstraction``
   * - :doc:`fp-abstraction`
     - the ``--fp-abstraction-*`` options
   * - :doc:`linear-real-arithmetic`
     - the ``--lra-*`` options

Other programs
--------------

The other programs under ``tools/`` in the source tree are for working on
STP, and none of them is installed: :doc:`tools` describes them.
