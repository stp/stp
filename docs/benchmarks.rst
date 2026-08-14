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

How the numbers are kept honest
-------------------------------

Wall-clock measurements are only comparable when the machine is doing nothing
else, which on a real workstation is never quite true. Two things guard
against it.

The harness watches how much CPU is being used by processes that are *not*
part of the campaign, sampled every second. If that sustained foreign load
crosses a threshold while an instance is running, the timing is discarded and
the instance is re-run later — a momentary spike inside a five-minute solve is
noise, but sustained competition for cores is not.

The corpus lives on a spinning disk, so every input is made resident before
the clock starts. Measured across short runs, the gap between wall-clock and
CPU time is under a millisecond, which is to say the disk is not part of the
measurement.

Reproducing a campaign
----------------------

The binary that produced each campaign is archived by content hash, along with
the STP commit, the compiler, and the exact SAT solver library it was linked
against — identified by hash rather than by version string, since several
builds of the same version can be present on one machine and only one of them
was linked.

That last point is not hypothetical. A stale checkout of the SAT solver once
meant months of measurements were quietly made against a solver two years
older than intended, with nothing in the build output to say so.
