Benchmarks
==========

How STP performs across the SMT-LIB benchmarks it can read, measured on a
fixed machine and recorded against a git commit, so the numbers can be
compared over time rather than only against each other.

Every campaign runs one statically linked binary over a corpus of
**160,610 files** — 137,509 non-incremental and 23,101 incremental, spanning
the nine logics STP accepts — with a 300 second timeout and a 30 GB memory
ceiling per instance.

.. raw:: html

   <link rel="stylesheet" href="_static/bench.css">
   <div class="bench" id="bench-root"></div>
   <script src="_static/bench.js" defer></script>

What is measured
----------------

Each run records the answer, wall-clock time and peak resident memory. Answers
are read from STP's own output and checked against the ``(set-info :status …)``
the benchmark carries; 96.9% of the non-incremental corpus states a known
answer, so most of it doubles as a correctness check.

An **answer mismatch is a soundness alarm**, not a performance result. Any
campaign reporting one is invalid until the cause is understood, which is why
the figure is shown above even when it is zero.

Instances are counted in one of these ways:

``solved``
   STP answered, and the answer agrees with the benchmark's stated status
   where one is given. Incremental files with several queries count as solved
   when every query was answered.

``timed out``
   The 300 second budget ran out.

``out of memory``
   The instance exceeded the 30 GB ceiling. Each solver runs in its own cgroup,
   so this is a property of the instance rather than of whatever else was
   running.

``unsupported``
   STP accepts the logic but not this particular input — uninterpreted
   functions in ``QF_AUFBV``, or nested array sorts. These are reported but
   excluded from the headline, because counting a capability gap as a
   performance failure would misdescribe both.

``error``
   STP crashed, or reported an error instead of an answer.

``mismatch``
   STP answered, but disagreed with the benchmark's stated status. See the
   soundness note above.

The tables also report **PAR-2**: the total wall-clock time in seconds, with
every unsolved instance charged twice the timeout. It rewards solving more
instances and solving them faster in a single number, and it is the measure
SMT-COMP uses.

Reproducing a campaign
----------------------

The binary that produced each campaign is archived by content hash, along with
the STP commit, the compiler, and the exact SAT solver library it was linked
against — identified by hash rather than by version string, since several
builds of the same version can be present on one machine and only one of them
was linked.

All of it is published, in `stp/benchmarks-data
<https://github.com/stp/benchmarks-data>`__: the harness that ran the campaign,
the frozen benchmark manifests, and the raw data this page summarises — per-run
wall time, CPU time and peak memory for all 160,610 instances, each run's
retained solver output, and the corpus index that gives the sha256 of every
benchmark measured. The binaries are `releases
<https://github.com/stp/benchmarks-data/releases>`__ of that repository, one
per binary, so a campaign can be re-run rather than merely inspected — check
what you download against the hash before you trust a measurement made with it.

The figures above are read from there live, so a new campaign appears here as
soon as it is published.

Two things are deliberately left out of the campaign list. A run over an ad-hoc
selection of files is an experiment rather than a result about STP, and a
campaign whose binary was not archived cannot be re-run by anyone, so neither
is published.
