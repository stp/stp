Running STP
===========

``stp`` is the solver's command-line front end, and the only program an
installation puts on the path. It reads one problem, from a file or from
standard input, and writes the answer to standard output:

.. code-block:: text

    stp [options] [input-file]

``stp --help`` lists every option with its default, grouped as below,
and ``man stp`` shows the same list where the manpage was installed -- on
Linux, a build makes it whenever ``help2man`` is available.
``stp --version`` prints the version, the commit it was built from, the
build configuration and the SAT solvers compiled in.

Input
-----

With no file named, ``stp`` reads standard input. Three input languages
are understood:

.. list-table::
   :header-rows: 1
   :widths: 22 30 48

   * - Language
     - Chosen by
     - Notes
   * - SMT-LIB2
     - ``--SMTLIB2``, a ``.smt2`` file, or no other choice
     - The recommended format, and the one this manual describes.
   * - CVC
     - ``--CVC``, or a ``.cvc`` file
     - STP's original input language.
   * - SMT-LIB1
     - ``--SMTLIB1`` (``-m``), or a ``.smt`` file
     - The pre-2010 SMT-LIB format.

A flag overrides the file extension, and naming more than one of them is
an error. Standard input has no extension, so it is read as SMT-LIB2
unless a flag says otherwise:

.. code-block:: bash

    stp problem.smt2
    stp < problem.smt2
    stp --CVC < problem.cvc

Output
------

An SMT-LIB2 input is a script, and STP answers its commands as it reaches
them: ``sat``, ``unsat`` or ``unknown`` for each ``(check-sat)``, and the
responses to ``(get-model)`` and ``(get-value ...)``. Those two need
``(set-option :produce-models true)`` earlier in the script, and answer
``unsupported`` without it.

.. code-block:: text

    $ cat example.smt2
    (set-logic QF_BV)
    (set-option :produce-models true)
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

A CVC input asks whether its ``QUERY`` follows from its assertions, and
the answer is ``Valid.`` or ``Invalid.``. ``Invalid.`` means a
counterexample exists, so a satisfiable set of assertions with
``QUERY(FALSE);`` answers ``Invalid.``.

``-p`` (``--print-counterex``) prints a model after every satisfiable
answer without the input asking for one: as ``define-fun`` lines for
SMT-LIB2, as ``ASSERT`` lines for CVC. ``-y`` (``--print-counterexbin``)
writes the CVC form's values in binary rather than hexadecimal.

Exit status
~~~~~~~~~~~

``stp`` exits with 0 once it has read and answered the input, whatever
the answers were -- ``unsat`` and ``unknown`` included. It exits with 255
when it could not: an unreadable file, an unknown or conflicting option,
or an input it rejected. A rejected SMT-LIB2 input also prints an
``(error "...")`` response saying why; answers already given to earlier
``(check-sat)`` commands in the same script stand. Read the answer from
standard output, not from the exit status.

Stack size
~~~~~~~~~~

STP recurses over the formula, and deeply nested inputs can overflow the
8 MB stack most Linux systems give a process by default. The symptom is a
segmentation fault. Raise the limit in the shell that runs ``stp``:

.. code-block:: bash

    ulimit -s 80000

Driving STP over a pipe
-----------------------

When it reads standard input, ``stp`` reads SMT-LIB2 a character at a
time, so a program can write one command, wait for the answer and write
the next:

.. code-block:: text

    (set-logic QF_BV)
    (declare-fun x () (_ BitVec 4))
    (assert (= x #x3))
    (check-sat)          ; sat
    (push 1)
    (assert (= x #x4))
    (check-sat)          ; unsat
    (pop 1)
    (check-sat)          ; sat
    (exit)

``--interactive=false`` reads standard input in blocks instead, which is
faster when the whole script is already there; ``--interactive=true``
does the reverse for a named file, such as a FIFO. STP can keep the SAT
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
     - CryptoMiniSat; ``--threads N`` runs it with *N* threads
   * - ``--minisat``
     - MiniSat
   * - ``--simplifying-minisat``
     - MiniSat with its variable elimination

The flags exclude one another. ``--search-bias unsat`` tunes the solver
for problems that are expected to be unsatisfiable, such as verification
conditions, and ``--search-bias sat`` for the reverse; solvers with no
such setting ignore it.

Limits
------

``-k N`` (``--max-time``) gives the SAT solver *N* seconds for the whole
input, and ``-g N`` (``--max-num-confl``) gives it *N* conflicts. A check
that runs out answers ``unknown``. Both bound the SAT search only, not
parsing, preprocessing or building the CNF, so a hard wall-clock limit
still needs ``timeout(1)`` or similar around ``stp``.

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
     - print time and peak memory, per stage, to standard error
   * - ``-s``, ``--print-functionstat``
     - trace the solve on standard output: node counts after each
       simplification, and what each pass did
   * - ``--parse-only``
     - read the input and stop, without solving; with ``-t``, time the
       parse

Controlling preprocessing
-------------------------

Most of STP's work happens before the SAT solver runs. The
``Simplifications`` group of ``stp --help`` switches individual passes on
and off. The broad switches are:

.. list-table::
   :header-rows: 1
   :widths: 34 66

   * - Option
     - Effect
   * - ``--disable-simplifications``
     - turn off every word-level simplification
   * - ``--size-reducing-only``
     - keep only the simplifications that never enlarge the formula
   * - ``-w``, ``--switch-word``
     - turn off the word-level equation solver
   * - ``--disable-cbitp``
     - turn off constant bit propagation
   * - ``--disable-equality``
     - turn off equality propagation

A switch that takes a value -- shown as ``BOOLEAN`` or ``INT`` in the
help -- accepts it either separately or after ``=``: ``--flattening 0``
and ``--flattening=false`` are the same. Options that cannot both take
effect are refused together rather than one of them being ignored:
``--disable-simplifications --flattening 1`` is an error.

:doc:`architecture` describes the passes these options control.

Writing CNF
-----------

``--output-CNF`` writes the CNF STP hands to the SAT solver as DIMACS
files named ``output_0.cnf``, ``output_1.cnf`` and so on, one per SAT
call, in the current directory. Its variables cannot be mapped back to the
input's, and an input that preprocessing solves on its own reaches no SAT
solver and writes no file. ``--exit-after-CNF`` stops once the CNF is
built, without solving; the two together turn a problem into DIMACS.
``--cnf-generation-effort`` trades the time spent minimising the CNF
against its size.

Converting between formats
--------------------------

These print the parsed input and exit without solving:

.. list-table::
   :header-rows: 1
   :widths: 34 66

   * - Option
     - Prints
   * - ``--print-back-SMTLIB2``
     - SMT-LIB2
   * - ``--print-back-CVC``
     - CVC
   * - ``--print-back-dot``
     - a graph for Graphviz's ``dot``
   * - ``--print-back-GDL``
     - a graph in aiSee's GDL

They take CVC or SMT-LIB1 input: ``--print-back-SMTLIB2 problem.cvc``
converts a CVC problem to SMT-LIB2. An SMT-LIB2 input is refused.

Options for particular theories
-------------------------------

The remaining groups in ``stp --help`` tune how STP handles one kind of
term, and each has a page of its own:

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
     - ``--bv-eq-abstraction``, ``--bv-term-abstraction`` and
       ``--ackermanize``
   * - :doc:`fp-abstraction`
     - the ``--fp-abstraction-*`` options
   * - :doc:`linear-real-arithmetic`
     - the ``--lra-*`` options

Other programs
--------------

The other programs under ``tools/`` in the source tree are for working on
STP, and none of them is installed: :doc:`tools` describes them.
