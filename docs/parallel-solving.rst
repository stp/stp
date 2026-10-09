Parallel solving
================

``stp-p`` decides one SMT-LIB query on several CPUs at once. It encodes the
query the way ordinary STP does, once, and forks copies of the loaded SAT
solver that search differently and pass each other short learned clauses.
The first answer wins. Without ``-j`` it uses the CPUs the process is
allowed, at most 8 -- what the measurements below support; more CPUs are not
faster. Each holds a copy of the loaded solver, so memory grows with N:
``--worker-memory-mib`` bounds each process and ``--memory-mib`` the whole
invocation. ``-j1`` is the sequential run: ordinary STP's pipeline through
STP's API, on the build's default SAT backend, without models and under the
per-process memory limit. Input is read as "Input and limits" describes. It
is a Linux program, built with ``-DSTP_BUILD_PARALLEL=ON`` (:doc:`tools`),
and it needs CaDiCaL with STP's clause-import extension, which the build
applies when it fetches a 3.x CaDiCaL (the default); on a build with no
CaDiCaL, or another one, ``-jN`` is refused, the default is 1, and ``-j1``
still works.

.. code-block:: bash

    stp-p problem.smt2
    stp-p -j8 --timeout 120 --stats-json report.json problem.smt2
    stp-p -j4 --config eager-arrays problem.smt2

The answer is one line, and the exit status says the same, at ``-j1`` and
at ``-jN`` alike:

.. list-table::
   :header-rows: 1

   * - outcome
     - standard output
     - exit status
   * - satisfiable
     - ``sat``
     - 10
   * - unsatisfiable
     - ``unsat``
     - 20
   * - no answer: the deadline or the ``--memory-mib`` guard stopped the run,
       or the solver answered unknown in time (its reason is in the report)
     - ``unknown``
     - 0
   * - an error
     - nothing
     - 2
   * - ``SIGINT``, ``SIGTERM``
     - nothing
     - 130, 143

``stp`` exits 0 on every answer and 255 on an error. ``stp-p`` follows the
convention of SAT solvers and of the competition harnesses that read exit
statuses instead, so that a caller can branch on the status alone and keep
"no answer" apart from "error".

An error is a usage error (an option, an unreadable input, a terminal or
closed standard input, an input over the bound below, a ``--stats-json``
file that cannot be opened); an input refused under "Input and limits";
every process dying, or failing to start, without an answer before any
limit -- an ``unknown`` the library answers in time is an answer, not a
failure, and a process that dies while another is still searching leaves
its trace in the report while the run ends as the others do; two complete
answers that disagree; or the owner breaking its hand-off. An answer that
was found is always published with its status: one found before the
deadline or a guard stops the run is printed; when standard output cannot
take the line before the deadline, the exit status is still the answer's
and standard error says the line was lost; and a report that cannot be
written, or a cleanup that overruns its five seconds, goes to standard
error and the report, never into the exit status.

How it runs
-----------

The process ``stp-p`` starts is a supervisor. It reads the input -- a file,
which it maps read-only, or standard input, which must not be a terminal or
closed and which it spools into anonymous memory (so ``ulimit -f`` does not
apply); either is at most ``--worker-memory-mib`` (16 GiB when that is 0)
and counts against the address space -- and forks one owner, which parses
it, once; the supervisor watches the owner for its report, the deadline,
the memory guard and signals. It is a child subreaper: every
process of the invocation is its descendant, each binds its death to its
parent's, and the supervisor kills and reaps all of them, by process group
and then one by one, before it prints anything. Nothing is ever killed by
name. The owner runs in a process group of its own, so stopping ``stp-p``
from a terminal (``^Z``) stops the supervisor and not the search.

With ``-jN`` and N greater than 1 the owner runs a group on N CPUs:

- **The hedge**, on one CPU, for ``QF_BV`` only. Right after its parse the
  owner forks it, and it builds an incremental solver (``check_sat`` with
  ``incremental = on``) on the owner's term manager over the owner's parsed
  assertions -- shared copy-on-write, nothing parsed again. Its CNF and its
  search differ from the roots'. On any other logic, and for a script with
  no ``set-logic``, there is no hedge, and the roots take its CPU. An answer
  from the hedge while the owner is still encoding stops the encoding.
- **The roots**, on the other N − 1 CPUs (N without a hedge). The owner
  runs ordinary STP on the query, on CaDiCaL whatever the build's default
  backend -- simplification, bit-blasting, CNF -- up to the moment the CNF
  is loaded into CaDiCaL and its search would start
  (``Solver::set_before_search``). There it forks one root per CPU and
  abandons its own check; the roots are not pinned, and the kernel places
  them on the CPUs the process may use. Every root holds the same loaded
  solver, copy-on-write. Root 0 searches as ordinary STP does on CaDiCaL;
  root *i* > 0 is diversified by a fixed table (seed N + *i*, N being
  ``--random-seed`` or 0; saved phases, a shuffled decision order,
  focused- or stable-only search). The roots publish learned clauses of at
  most eight literals into rings of shared memory (2\ :sup:`20` literals
  each), about 2 000 clauses of two or more literals a second each (a
  token bucket), duplicates of a root's recent clauses filtered out; every
  256 of its own conflicts a root polls, scanning at most the newest
  2\ :sup:`16` literals of each other root's ring, and imports every unit
  and at most one longer clause per conflict, shortest first.

A check that preprocessing decides answers at once, in the owner. A check
that cannot offer the fork point, because it may refine after its first
solve (array axioms STP leaves lazy, when reads survive simplification, or
an uninterpreted function), searches in place in the owner, once, as
ordinary STP on CaDiCaL: on ``QF_BV`` the hedge runs beside it; on the
other logics there is no hedge, so the owner works alone on one of the N
CPUs. The report records ``fork_point`` ``refused`` and the library's
reason. An array equality the pipeline expands eagerly (between stores over
bit-vector arrays, say) does not refuse the point. When the rings cannot be
mapped (a small ``--worker-memory-mib``) the roots run without sharing and
the report says why (``sharing_off``); when no root can be forked, the
owner searches in place.

The first complete answer wins and the rest are killed. A root's answer is
the query's: every clause it imported was learned by another root forked
from the same loaded solver, and holds in every model of the query. It is
implied by the clauses all of them share -- or, under ``--config
eager-arrays``, where a root whose model fails its replay adds array axioms
after the fork, by those axioms, which are valid for the query -- because
every root runs the same CaDiCaL options (diversification changes only the
search), no technique that removes models runs between the fork and the
connection, and the variables created later lie above the cutoff that no
exported clause crosses. Every complete answer in hand is compared
with the others -- each root's, the hedge's, the owner's, and one written by
a process that was killed afterwards -- and two that disagree are an error (exit 2) whose report
carries every answer; but agreement is no check of soundness, since a clause
wrongly imported would reach every root through the exchange, and all of
them could agree.

Each process but the supervisor, which holds only the input within the same
bound, has an address-space limit (``--worker-memory-mib``, 16 GiB by
default). ``--memory-mib`` adds a guard on the whole invocation: the
supervisor samples the summed resident size every 50 ms and, when that is
over the limit, the summed PSS, which counts each copy-on-write page once,
at most every 0.5 s; over the limit in PSS the answer is ``unknown``.

What ``-jN`` runs, and why
--------------------------

Plain ``-jN`` is the configuration the measurements below chose; the test
driver can vary each policy, ``stp-p`` cannot.

- **Root 0 exports and never imports**. Imports
  slow a solver down, and on some inputs only ordinary STP's own search
  finds the proof: one input ordinary STP decides in 41 s was lost by
  every group whose root 0 imported, at 16 and 24 CPUs, and decided in
  40–89 s by every group whose root 0 did not.
- **Import is budgeted**: at most one clause of two
  or more literals per own conflict, the shortest first, plus every unit.
  Without a budget a root spent its time importing; with it, root 0 of an
  importing group made several times the conflicts.
- **The hedge**. Three of seventy development inputs
  are decided only by the incremental driver; without the hedge the group
  loses them at every size (PAR-2 7 014 against 5 172 with it, summed over
  8 and 24 CPUs).
- **Diversification** of every root but 0 and **sharing** between them;
  without sharing the roots are independent copies of one search.

Every process pays for the others: on the 24-vCPU machine these were
measured on, each of k identical busy processes ran 1.12 times slower at
k = 8 and 1.60 times slower at k = 24 than alone. A wider group must make
each root's work that much more effective before it is faster.

Options
-------

``-j N``, ``-jN``, ``--jobs=N``
  Without it, the CPUs the process is allowed, at most 8 (1 on a build
  without the extension). 1 is ordinary STP's pipeline (above). N > 1 is the
  group on N CPUs (N − 1 roots and the hedge on ``QF_BV``, N roots
  otherwise), holding N copies of the loaded solver. N may not exceed the
  CPUs the process is allowed. Numbers are read in base 10.
``--timeout SECONDS``
  The deadline for the whole invocation, reading and publishing included;
  0 (the default) is none. Cleanup has five more seconds.
``--random-seed N``
  The native seed of ordinary STP, of the hedge and of root 0; root *i* > 0
  takes N + *i*.
``--worker-memory-mib M``, ``--memory-mib M``
  The per-process address-space limit (default 16384, 0 inherits), which
  also bounds the input, and the invocation's PSS guard (default 0: none).
  Under AddressSanitizer, whose shadow memory an address-space limit
  starves, run with ``--worker-memory-mib 0``.
``--config default|eager-arrays``
  Ordinary STP, or ordinary STP with eager array-read axioms: the ``-j1``
  route, or the group's base (the hedge keeps its own). With eager axioms
  most array checks offer the fork point; an equality between arrays of
  floating-point elements, or one with a constant array, still refines and
  does not.
``--stats-json FILE``
  A JSON report: the answer, which side and which root decided, whether the
  fork point was offered, timings, the memory peaks, and each root's
  exchange counters.
``--help``, ``--version``
  The usage, or the version and commit of the STP library it runs on.

Input and limits
----------------

One decision-only query: declarations, definitions, assertions and one
``check-sat``, in ``QF_BV``, ``QF_ABV``, ``QF_FP``, ``QF_BVFP`` or
``QF_ABVFP``, at ``-j1`` and at ``-jN``; the hedge takes ``QF_BV`` only. A
script with no ``set-logic`` is read with every theory's keywords and
decided by ordinary STP, with no hedge. Admission goes by the label alone:
a script labelled ``QF_BV`` that declares an uninterpreted function or a
sort, or equates two arrays, is accepted (``stp`` refuses it) and decided
correctly, with the hedge beside the roots. ``stp-p`` has no parser of its
own: STP's reads the input in its single-query mode
(``ParseMode::SINGLE_QUERY``, :doc:`api`), which applies the query and
refuses, before anything is solved, every command outside one: ``push``,
``pop``, either reset, ``check-sat-assuming``, a second ``check-sat`` or
none at all, ``exit`` before the ``check-sat``, a command after it other
than ``exit``, text after the last command, output requests and ``echo``,
datatypes, ``declare-sort-parameter`` and recursive definitions, a late or
repeated ``set-logic``, and every option but ``:print-success`` and
``:produce-models``, which change nothing here. The error names the command
and its line. A NUL byte is refused too. There is no model output.

The input may be at most ``--worker-memory-mib`` (16 GiB when that is 0); a
larger one is an error. A file is mapped read-only, and standard input is
spooled into anonymous memory that the forked processes share
copy-on-write; the parser reads the source in place, without a copy, and
the owner releases it once the query is parsed. Nesting depth is not
limited. A refusal is exit status 2, never an answer.

Results
-------

These are a development version's numbers, measured on one 24-vCPU VM, one
invocation at a time; it pinned each root to a CPU and ran its hedge as a
side of its own. An earlier carve of this tool was checked against it at
``-j8`` on the reserved sample below: both decided the same 40 files with
the same answers, the carve at 1.006 times the development version's PAR-2
score and 0.96 times its geometric-mean time. The tool has changed since in
how it reads its input and where it forks its hedge, and has not been
measured on the sample again.

**A reserved sample** of 51 QF_BV files from 14 families, drawn after every
design choice above was fixed and never tuned on, split by whether ordinary
STP needs 10 s; a 120 s cap and 8 GiB per process:

.. list-table::
   :header-rows: 1

   * - mode
     - hard files decided (of 25)
     - PAR-2
     - time against the previous row (geometric mean)
     - easy files: time against the previous row
   * - ``stp``
     - 13
     - 3 418
     -
     -
   * - ``stp-p -j1``
     - 13
     - 3 412
     - 1.01
     - 1.02
   * - ``stp-p -j8``
     - 15
     - 2 826
     - 0.41
     - 0.64
   * - ``stp-p -j24``
     - 15
     - 2 800
     - 0.97
     - 1.16

``-j8`` is 2.4 times faster than ordinary STP on the hard files (2.5 times
than ``-j1``), with ten material wins over ``-j1`` and no loss, and decides
two files ordinary STP does not; on the easy files it is 1.5 times faster
(1.6 than ``-j1``). ``-j24`` is not faster than ``-j8``: on the hard files
it took 0.97 times ``-j8``'s time, within the spread of single runs (three
runs of one of those files at ``-j24`` differed by up to 2.5 times), and on
the files under 10 s it is slower than ``-j8`` (by 0.22 s at the median
over all 26), because of the contention described under "What ``-jN``
runs": each of k busy processes runs 1.12 times slower than alone at k = 8
and 1.60 times at k = 24, so a search of 4–10 s pays 1–3 s before sharing
can repay it. There was no disagreement,
and 40 of the 41 decided files are confirmed by Bitwuzla or a checked
witness.

**The QF_BV division of the SMT-COMP 2026 parallel track**, 52 files under
the competition's 1 200 s limit, run with the development version at 16 GiB
per process and a 128 GiB guard on the whole invocation (``--memory-mib``,
which is off by default). The competitors' results are the published ones,
from the competition's own runs, in its results file
(`results-parallel-2026.json.gz
<https://raw.githubusercontent.com/SMT-COMP/smt-comp.github.io/master/data/results-parallel-2026.json.gz>`_,
as fetched on 6 October 2026), which records how much CPU each used per
second of wall-clock time (the median over the 52 files); for ours on the
24-vCPU VM that is about 24, so the comparison favours them:

.. list-table::
   :header-rows: 1

   * - solver
     - CPU per wall-clock second (median)
     - decided
     - PAR-2
   * - Bitwuzllob
     - 65
     - 32
     - 57 085
   * - ``stp-p -j24``
     - 24
     - 30
     - 59 887
   * - Bitwuzla-BV_Parti
     - 95
     - 18
     - 90 406
   * - ``stp-p -j1`` (eight at a time)
     - 1
     - 20
     - 85 209

Diversified roots decided 28 of the 30, root 0 two, the hedge none. Two of
the decisions no competitor made; there was no disagreement with any
competitor's answer. Some open failures are memory, not search: on two of
the largest files (mcm ``184`` and ``186``) the 24 copies exceeded the
128 GiB guard, and ``AND-NESTED-32-32`` aborts at 16 GiB per process even
alone (an open decision below).

**Real arithmetic** is not parallel. Sequential STP decided 18 of the 40
QF_LRA files of the same track when this was measured (6 October 2026,
before later changes to STP's arithmetic presolve). In the competition's
results file
OpenSMT-SMTS-base decides 18 at one CPU second per wall-clock second, and
OpenSMT-SMTS decides 22 at a median of 126. The group's fork point needs a
check with one solve, and the arithmetic is checked outside the SAT solver.

The interface it is built on
----------------------------

Two members of the API (:doc:`api`, C++ only for now) make the group
possible and can be used without ``stp-p``:

- ``Solver::set_before_search`` runs a hook for the next check, at most
  once, at the moment its CNF is loaded and its search would start; a
  process may fork there. A check that may refine after its first solve
  does not offer the point, and is abandoned or searched in place, as the
  caller asks;
- the hook's ``SearchPoint`` connects a ``ClauseExchange`` (learned clauses
  out, clauses to import in, in the backend's own numbering) to that
  check's backend, or diversifies its search and nothing else.

Open decisions
--------------

Each of these is open, with the measurement that would settle it:

- **More than 8 CPUs by default**: the default stops at 8 because nothing
  measured favours more. A start-up ramp (seven roots at once, the rest
  after a fixed delay) would have to keep inputs under 10 s within 5% of
  ``-j8`` and beat ``-j8`` on the hard ones by more than the spread of
  repeated runs.
- **Memory-aware allocation**: fewer roots, or roots shed at runtime, when
  the loaded solver is large; two of the competition's largest files
  exceeded a 128 GiB guard at 24 CPUs. Measured by sampling each root's PSS
  against the owner's size after encoding.
- **Aborts at the address-space limit**: a process that exhausts
  ``--worker-memory-mib`` aborts or crashes rather than failing cleanly;
  when every process dies that way the answer is an error (exit 2), not
  ``unknown``. ``AND-NESTED-32-32`` aborts plain
  STP at 16 GiB on every route; a library defect to report on its own.
- **An unconfirmed answer**: ``Sage2/bench_9638`` is sat at 834 s, which
  Bitwuzla did not confirm in 1 200 s; ``stp-p`` prints no model, the API
  can produce one to check.
- **Import policy**: admission that adapts to what a root uses, and import
  at restarts; measured by a budget sweep on the 17 track files nobody
  decides.
- **Cubes on the batch base**: splitting the search under selectors that
  survive simplification, against more roots, at 24 CPUs.
- **Refinement in parallel**: a check that may refine (array axioms left
  lazy) offers no fork point and runs once, in the owner, today;
  the library could offer the point with a "refinement follows" flag, and
  the group would re-fork each round.
- **An automatic** ``ackermanize`` **rule**, chosen from the input's array
  reads (a sequential question).
- **Real arithmetic**: a seed and configuration screen on the QF_LRA files
  STP leaves open; a portfolio is worth building only if four or more fall.
- **The 17 track files nobody decides**, by family.
- **An in-library API**: the group's coordinator in ``libstp`` with a
  parallel options block on ``check_sat``, the C and Python mirrors of the
  two members above, and every ``stp-p`` option settable through it.
- **Builds without the extension**: ``-jN`` is refused where CaDiCaL is
  missing or unpatched; an independent-seed portfolio could run there
  instead.
- **Beyond 24 CPUs**: what ``-j48`` gains, NUMA-aware forking, and handing
  the CNF to a distributed solver as the comparison to make before building
  more.
