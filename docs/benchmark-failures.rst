:orphan:

Unsolved benchmarks
===================

Every instance of one logic that the latest campaign did not solve, with why.
Reached by clicking a logic on the :doc:`benchmarks` page.

.. raw:: html

   <link rel="stylesheet" href="_static/bench.css">
   <div class="bench" id="bench-fail-root"></div>
   <script src="_static/bench-failures.js" defer></script>

An instance appears here for one of five reasons. Only the first two are
necessarily faults in STP:

``mismatch``
   STP answered, and the answer contradicts the result the benchmark states.
   This is a soundness bug and invalidates the campaign it appears in.

``error``
   STP crashed, or reported an error instead of an answer.

``memout``
   The instance exceeded the campaign's memory ceiling. Each solver runs under
   its own cgroup limit, and an instance killed while other instances were
   competing for memory is re-run alone before being recorded, so this means
   the instance wanted that much memory to itself.

``timeout``
   The time budget ran out. On a hard instance that is an ordinary result
   rather than a defect.

``unsupported``
   The input uses something STP does not implement — uninterpreted functions
   in ``QF_AUFBV``, nested array sorts, or real arithmetic beyond ``to_fp``
   arguments. These are excluded from the solved counts and from PAR-2, since
   a missing feature is not a performance result.

What STP printed on each of these is kept. `stp/benchmarks-data
<https://github.com/stp/benchmarks-data>`__ carries the retained stdout and
stderr of every run, so a classification on this page can be checked, or
disputed, without re-running the campaign.
