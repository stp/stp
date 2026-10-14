Automatic SAT tuning
====================

``--sat-tuning=auto`` is the default. It selects SAT search and CNF settings
using the compiled backend selected for the run, the SMT-LIB ``set-logic``,
and the incremental session mode. Native API clients can supply the logic
through the ``logic`` option. A missing or unmeasured logic uses the baseline
policy. Automatic backend selection still uses STP's existing backend order.

Profiles
--------

The initial profiles come from full-corpus QF_BV and QF_ABV comparisons with
CaDiCaL 3.0.1 and incremental Kissat 4.0.4. They use a 24-second cutoff for
each complete SMT-LIB file and an 8 GiB address-space limit.

.. list-table:: Defaults supplied to unset options
    :header-rows: 1
    :widths: 15 15 15 55

    * - Backend
      - Logic
      - Session
      - Settings
    * - Kissat
      - QF_BV
      - Batch
      - ``sat-phase=0``, ``cnf-generation-effort=new-medium``
    * - CaDiCaL
      - QF_BV
      - Incremental
      - ``sat-rephase=0``
    * - Kissat
      - QF_BV
      - Incremental
      - ``search-bias=unsat``, ``cnf-generation-effort=new-medium``,
        ``kissat-factor=off``
    * - CaDiCaL
      - QF_ABV
      - Batch
      - ``search-bias=unsat``, ``cnf-generation-effort=gia-low``,
        ``cadical-factor=off``
    * - CaDiCaL
      - QF_ABV
      - Incremental
      - ``search-bias=sat``, ``sat-target=0``,
        ``cnf-generation-effort=new-medium``, ``cadical-factor=off``
    * - Kissat
      - QF_ABV
      - Incremental
      - ``search-bias=sat``, ``kissat-stable=2``, ``sat-target=0``,
        ``sat-rephase=0``, ``cnf-generation-effort=new-medium``,
        ``kissat-probe=false``, ``kissat-factor=off``

Other combinations use the baseline policy. The Kissat QF_ABV batch finalist
was slower than its baseline. The CaDiCaL QF_ABV batch profile uses
``gia-low`` after the pinned ABC mapper was changed to use an explicit stack
for its cut-reference walks, fixing the stack overflow on wide
division/remainder encodings.

Session detection
-----------------

``--incremental=on`` (or the bare ``--incremental``) and SMT-LIB
``(set-option :incremental true)`` select the incremental profile. ``off``
selects the batch profile even when the input pushes. In the default ``auto``
mode, the first observed push makes the session incremental. This also covers
the temporary frame used by ``check-sat-assuming``. Unsat-core requests that
require the persistent driver are also classified as incremental.

The SMT-LIB reader processes a stream in order. If a push follows an earlier
check, it affects the tuning of subsequent checks. It cannot inform an
earlier solve. The profile is selected before encoding or constructing a SAT
backend, and can change while checks still use fresh batch encodings. Once
the persistent driver exists, its profile stays fixed across checks, memory
relief rebuilds, and switches between solvers sharing a manager. The session's
reset paths retire that selection along with the persistent driver.

This classification describes the session, including its initial batch
checks. It does not change ``incremental-auto-engage-at`` or force earlier
persistent-driver engagement. The experiments used the existing engagement
policy; timings for forced engagement may differ.

Explicit options and diagnostics
--------------------------------

User options take precedence individually. Presence matters: an explicit
``--cnf-generation-effort=auto``, ``--search-bias=none``, or ``--sat-phase=-1``
is preserved even though it equals the baseline value. An explicit
``--kissat-probe=true`` keeps probing enabled. The factoring aliases
refer to one option, so an explicit ``--kissat-factor=on`` also overrides an
automatic ``cadical-factor=off``.

An explicit ``search-bias`` also owns the phase/mode policy of that named
configuration. Automatic phase, target and Kissat stable-mode choices are
suppressed in that case; individual explicit phase/mode options take
precedence over the named configuration as usual. Encoding and factoring
defaults can still come from the automatic profile.

Use ``--sat-tuning=off`` to reproduce baseline defaults or compare manual
configurations without automatic tuning. The SMT-LIB spelling is
``(set-option :sat-tuning off)``. Set it before the first check.

.. code-block:: bash

    stp --kissat -s input.smt2
    stp --cadical --incremental -s input.smt2
    stp --kissat --cnf-generation-effort=auto input.smt2
    stp --kissat --sat-tuning=off input.smt2

``-s`` reports the selected profile and the effective values of its options,
including explicit overrides, through STP's diagnostic stream. Backend
statistics also report the actual phase settings accepted by the SAT solver.

Automatic choices are kept separately from user options. The API's ``get``
and ``is_set`` continue to describe what the user supplied; an automatically
tuned option stays unset. After a check selects a profile,
``SolverOptions::resolved`` and ``SolverOptions::info().resolved`` include its
effective defaults. Copying options copies user choices and the tuning policy,
and a new solver selects its own profile from its logic and session.

Option timing rules also apply when resetting user choices would enable an
automatic default. In particular, ``SolverOptions::reset_all`` refuses the
whole reset if removing an explicit baseline value would change a search
control after its first-check window has closed.

Measurements
------------

The confirmed finalists reduced mean PAR2 from 1.759 to 1.577 seconds on
46,191 batch QF_BV files with Kissat; from 4.695 to 2.806 seconds on 1,272
files in the incremental QF_ABV directory with CaDiCaL; and from 4.469 to
3.780 seconds on the same directory with Kissat. On 15,148 batch QF_ABV
files, the CaDiCaL finalist reduced mean PAR2 from 0.717 to 0.685 seconds.
These measured commands set their tuning options from the start of the file.

The incremental directory contains 970 files with multiple checks and 302
with one check. On the multiple-check subset, the CaDiCaL finalist reduced
mean PAR2 from 4.025 to 2.120 seconds, and Kissat from 3.571 to 3.061 seconds.
Every comparison used the same files for all configurations and audited
captured answer sequences without a SAT/UNSAT disagreement. These are results
for explicit finalists, not a rerun of the automatic resolver; late pushes
and explicit user options can change which defaults it supplies.

A follow-up measured the automatic resolver with the updated incremental
profiles above on all 1,244 multiple-check QF_BV files and all 970
multiple-check QF_ABV files. It used three complete repetitions at the same
24-second cutoff and 8 GiB limit. The table averages each file's median PAR2
across those repetitions; lower is better.

.. list-table:: Automatic profiles, mean of per-file median PAR2 in seconds
    :header-rows: 1
    :widths: 25 15 30 30

    * - Logic
      - Files
      - CaDiCaL
      - Kissat
    * - QF_BV
      - 1,244
      - 2.261
      - 2.231
    * - QF_ABV
      - 970
      - 1.986
      - 1.666
    * - Combined
      - 2,214
      - 2.140
      - 1.983

Kissat completed 2,137 files in every repetition. CaDiCaL completed 2,132
files in at least two repetitions, and 2,131 in every repetition. The combined
Kissat score was 7.3 percent lower than automatic CaDiCaL and 6.9 percent
lower than the explicit CaDiCaL finalist's score of 2.131 seconds. The QF_BV
improvement was small; QF_ABV accounted for most of the combined improvement.
These profiles were selected using the measured corpus, so repeating it
checks timing stability without providing an independent holdout.

A separate single-pass check forced ``--incremental=on`` on 122 files:
all 58 QF_BV files with at least 32 checks and 64 selected QF_ABV files.
CaDiCaL's mean PAR2 was 18.225 seconds and Kissat's was 18.452 seconds.
On the QF_ABV sample alone the scores were 2.482 and 3.597 seconds,
respectively. Forced engagement has a different performance pattern and
needs separate profile experiments. The main table uses the existing
automatic engagement policy.
