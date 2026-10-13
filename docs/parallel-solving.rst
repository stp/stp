Parallel solving
================

``stp-p`` decides one SMT-LIB query on several CPUs at once. By default it encodes the
query the way ordinary STP does, once, and forks copies of the loaded SAT
solver that search differently and pass each other short learned clauses.
The first answer wins. Without ``-j`` it uses the CPUs the process is
allowed, capped at 8 by default following the bit-vector measurements below.
Each holds a copy of the loaded solver, so memory grows with N:
``--worker-memory-mib`` bounds each process and ``--memory-mib`` the whole
invocation. ``-j1`` is the sequential run: ordinary STP's pipeline through
STP's API, on the build's default SAT backend, without models and under the
per-process memory limit. Input is read as "Input and limits" describes. It
is a Linux program, built with ``-DSTP_BUILD_PARALLEL=ON`` (:doc:`tools`),
and it needs CaDiCaL with STP's clause-import extension, which the default
pin of STP's CaDiCaL fork carries. On a build with no CaDiCaL, or one
without the extension, ``-jN`` is refused, the default is 1, and ``-j1``
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

For ``QF_LRA``, every root also inherits the arithmetic coordinator and its
atom registry. Each root solves the complete query with its own arithmetic
state and different Boolean search settings, sharing CDCL-learned clauses
over the common encoding. Simplex remains sequential; the arithmetic
problem is not divided into subproblems. There is no incremental hedge for
``QF_LRA``, and every group size uses the generic launch policy.

The Boolean skeleton is an abstraction. Each root continues the full
arithmetic check, and exact arithmetic certifies conflicts and SAT models.
Floating-point simplex supplies advisory proposals; sharing never relies
on an uncertified floating-point result. All roots use the same activation
assumption. Binding arithmetic atoms after the fork maps them onto existing
Boolean variables with the same meaning in every copy. Variables introduced
later lie above the exchange cutoff and cannot occur in shared clauses.

The library permits arithmetic-only refinement at the fork point. Mixed
queries with active array, uninterpreted-function or abstraction refinement
retain the ordinary refusal/fallback behavior. Admission and the general
refinement flag use the same predicate for non-arithmetic refinement
sources.

A root that rebuilds its SAT backend, for example to reroute from
floating-point simplex to the exact driver, stops sharing because its new
variable numbering is private. Its accepted Boolean search settings are
restored after loading the new CNF. The original hook runs only once and
does not fork another group during a reroute.
``before-search.rediversifications`` counts these restorations.

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

Optional encoding groups
------------------------

``--encoding-groups`` opts into two independent encodings for named ``QF_BV``
queries with ``--config default`` and at least four jobs:

.. code-block:: bash

    stp-p -j24 --encoding-groups --stats-json report.json problem.smt2

The coordinator parses once and forks two owners over the same assertions.
The default encoding gets half the job budget, rounded up, including the
retained hedge; GIA-high gets the remaining jobs without another hedge.
Each owner builds its own CNF and forks its roots from that loaded solver.
Learned clauses stay within that owner's encoding; no clauses cross between
groups. Other supported logics and unnamed queries use the ordinary single
group over the already parsed assertions. Without the option, the existing
single-encoding route and worker budget apply at every job count.

A validated decision note requests cancellation of the other encoding before
the winning owner finishes teardown. Owners stop their workers and drain their
reports, preserving the comparison of complete answers. An owner that does
not respond within a bounded grace period is forcibly stopped; in that case,
only evidence already forwarded by that owner remains available for comparison.
The invocation's deadline and memory guard still cover the entire process tree.

If one encoding fails while the other is running, the coordinator first reaps
the failed group's descendants, then makes one replacement group using the
surviving encoding and the freed job budget. The survivor retains its search
state. The replacement has a different seed and its own clause rings, and must
build its CNF again. No further replacement is attempted if that attempt fails.
To support this fallback, the coordinator retains the parsed assertions until
the run ends. Slots allocated to an encoding that is still being generated are
not redistributed while it is merely slow.

The JSON report identifies the groups, their budgets, any replacement, and
cooperative or forced cancellation. This option permits comparison with and
without grouping using the same executable; it makes no performance guarantee.

What ``-jN`` runs, and why
--------------------------

Plain ``-jN`` is the configuration the measurements below chose; the test
driver can vary its search and transport policies. The encoding-group option
above is separate and off by default.

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
``check-sat``, in ``QF_BV``, ``QF_ABV``, ``QF_FP``, ``QF_BVFP``,
``QF_ABVFP`` or ``QF_LRA``, at ``-j1`` and at ``-jN``; the hedge takes
``QF_BV`` only. A
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

The reserved sample and the competition track are a development version's
numbers, measured on one 24-vCPU VM, one invocation at a time; it pinned
each root to a CPU and ran its hedge as a side of its own. An earlier carve
of this tool was checked against it at ``-j8`` on the reserved sample
below: both decided the same 40 files with the same answers, the carve at
1.006 times the development version's PAR-2 score and 0.96 times its
geometric-mean time. The tool has changed since in how it reads its input
and where it forks its hedge, and has not been measured on the sample
again.

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
(1.6 than ``-j1``). On this sample ``-j24`` is not faster than ``-j8``: on
the hard files it took 0.97 times ``-j8``'s time, within the spread of
single runs (three runs of one of those files at ``-j24`` differed by up to
2.5 times), and on the files under 10 s it is slower than ``-j8`` (by
0.22 s at the median over all 26), because of the contention described
under "What ``-jN`` runs": each of k busy processes runs 1.12 times slower
than alone at k = 8 and 1.60 times at k = 24, so a search of 4–10 s pays
1–3 s before sharing can repay it. There was no disagreement, and 40 of
the 41 decided files are confirmed by Bitwuzla or a checked witness.

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

**Beyond 24 CPUs**: ten hard files of the same division, chosen to include
ones where earlier runs had gained, lost and decided nothing -- so, unlike
the reserved sample, not unseen -- run with a later development build on
12 and 13 October 2026, on a 64-core VM with two NUMA nodes and 251 GiB,
``-jN`` allowed one hardware thread on each of N cores; seed 0, one run
each, a 180 s cap and 16 GiB per process. The row without sharing is the
test driver's ``--clause-sharing off``:

.. list-table::
   :header-rows: 1

   * - mode
     - decided at ``-j8`` (of 10)
     - at ``-j24``
     - at ``-j64``
     - PAR-2 at ``-j8``, ``-j24``, ``-j64``
   * - ``stp-p -jN``
     - 2
     - 5
     - 7
     - 3 198, 2 292, 1 733
   * - without sharing
     - 2
     - 2
     - 3
     - 3 100, 3 082, 2 797

A group wider than 8 can pay on a hard query, and sharing is what pays: each
of the four unsatisfiable files decided was decided only with it, while
without it the group decided satisfiable files alone, two of them at
``-j8`` where the sharing group did not. The default stays at 8 for the
short files above and for memory (open decisions below). Six of the seven
decided files agree with the competition's published answers; the seventh,
``Sage2/bench_6746``, was sat in every run that decided it, unconfirmed.

**Real arithmetic, historical baseline.** Sequential STP decided 18 of the
40 QF_LRA files of the same track when this was measured (6 October 2026,
before parallel arithmetic support and later changes to STP's arithmetic
presolve). In the competition's
results file
OpenSMT-SMTS-base decides 18 at one CPU second per wall-clock second, and
OpenSMT-SMTS decides 22 at a median of 126. These are historical sequential
results, not measurements of the current arithmetic group.

**Real arithmetic, clause-sharing group.** All 1,753 non-incremental
QF_LRA benchmarks in a corpus spanning 17 families were run at ``-j1`` and
``-j12`` on 12 and 13 October 2026, using
`commit 87c582d18
<https://github.com/stp/stp/commit/87c582d1818be1befe2974931c21853ca2a1cf16>`_.
Both modes used the same frozen release executable and library, built with
Clang 21, mimalloc and CaDiCaL 3.0.1, on a shared 24-vCPU VMware host.
They were confined to the same 12 CPUs, one invocation at a time with
alternating job order. The whole-invocation wall deadline was 60 s,
with 16 GiB of address space per process and a 64 GiB aggregate PSS guard.
There was one full-corpus run per mode. PAR-2 below is the mean seconds per
benchmark: a complete answer within the deadline costs its end-to-end wall
time; an undecided or failed invocation costs 120 s.

.. list-table::
   :header-rows: 1

   * - mode
     - decided (of 1,753)
     - timeouts
     - PAR-2 mean (s)
   * - ``stp-p -j1``
     - 1,639
     - 114
     - 10.679
   * - ``stp-p -j12``
     - 1,686
     - 67
     - 6.676

``-j12`` reduced PAR-2 by 37.5%, decided 47 additional inputs and lost
none. The additional decisions came from LassoRanker (29), invariant
synthesis (7), miplib (6), 2019-ezsmt (4) and tropical-matrix (1). On the
1,639 inputs both modes decided, total runtime was 0.493 times ``-j1``'s
and geometric-mean runtime 0.965 times: gains were concentrated in
expensive inputs, while very easy families were often slower in parallel.
All 67 remaining undecided ``-j12`` inputs were wall timeouts, including
30 in LassoRanker, 14 in miplib and 8 in tropical-matrix.

**Selected follow-ups** used the same build and limits. Repeating 32
baseline gain/regression cases twice per mode gave 32 of 64 decisions at
``-j1`` and 63 of 64 at ``-j12``. On 48 selected hard inputs, the test
driver at ``-j12`` with sharing decided 34 and had mean PAR-2 46.113 s;
with ``--clause-sharing off`` it decided 30 and had mean PAR-2 59.661 s,
29.4% higher. Sharing on/off order alternated between blocks of eight
inputs. These subsets were selected after the baseline and are exploratory,
not further full-corpus estimates. Across the 3,730 baseline and follow-up
trials, the audit found no solver errors, benchmark-status mismatches or
contradictory complete answers.

These results support the existing arithmetic group and its clause sharing.
They do not compare ``-j8`` with ``-j12`` or measure QF_LRA at ``-j24``;
the eight-CPU default remains unchanged.

The interface it is built on
----------------------------

Two members of the API (:doc:`api`, C++ only for now) make the group
possible and can be used without ``stp-p``:

- ``Solver::set_before_search`` runs a hook for the next check, at most
  once, at the moment its CNF is loaded and its search would start; a
  process may fork there. A check that may refine outside arithmetic after
  its first solve does not offer the point, and is abandoned or searched in
  place, as the caller asks;
- the hook's ``SearchPoint`` connects a ``ClauseExchange`` (learned clauses
  out, clauses to import in, in the backend's own numbering) to that
  check's backend, or diversifies its search and nothing else.

Open decisions
--------------

Each of these is open, with the measurement that would settle it:

- **More than 8 CPUs by default**: the default remains at 8. A broader
  default needs evidence across supported logics and resource budgets,
  including short inputs, comparing latency and CPU cost.
- **Memory-aware allocation**: fewer roots, or roots shed at runtime, when
  the loaded solver is large; two of the competition's largest files
  exceeded a 128 GiB guard at 24 CPUs. At 64 they passed a 192 GiB guard
  within 36 s, and on one (mcm ``186``) memory grew too fast for the guard,
  which samples: the kernel killed a process at a 224 GiB cgroup limit
  first. Measured by sampling each root's PSS against the owner's size
  after encoding.
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
- **Real arithmetic**: the comparison above supports the clause-sharing
  group. Profiling the 67 remaining ``-j12`` timeouts should distinguish
  Boolean-search cost from arithmetic-check cost; very easy files still
  incur parallel overhead. Parallel simplex, arithmetic subproblem
  partitioning and HiGHS work sharing remain separate possible approaches
  to measure.
- **The 17 track files nobody decides**, by family.
- **An in-library API**: the group's coordinator in ``libstp`` with a
  parallel options block on ``check_sat``, the C and Python mirrors of the
  two members above, and every ``stp-p`` option settable through it.
- **Builds without the extension**: ``-jN`` is refused where CaDiCaL is
  missing or unpatched; an independent-seed portfolio could run there
  instead.
- **Beyond 24 CPUs**: ``-j64`` gains on hard files (above); what it costs
  on the rest, NUMA-aware forking, and handing the CNF to a distributed
  solver as the comparison to make before building more.
