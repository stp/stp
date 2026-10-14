Incremental Kissat in STP
=========================

STP can use an incremental extension of Kissat 4.0.4 for bitvector, array,
and floating-point problems. The backend supports permanent clause additions,
temporary assumptions, failed-assumption cores, and model queries across
repeated solves. These operations serve both SMT-LIB push/pop sessions and
STP's internal abstraction and array refinement loops.

Building the backend
--------------------

``USE_KISSAT`` defaults to ``OFF``. With ``ENABLE_AUTO_DOWNLOAD=ON``,
CMake fetches the pinned commit on the ``stp`` branch of
`stp/kissat <https://github.com/stp/kissat/tree/stp>`__, builds its static
library with the STP toolchain, and installs it into ``STP_DEP_DIR``.
The fork's ``master`` and ``upstream`` branches mirror upstream Kissat 4.0.4;
the incremental API and CMake build are commits on ``stp``.

.. code-block:: bash

    ./configure.sh release --ninja --name=build-kissat --auto-download \
        --no-cryptominisat --kissat
    cmake --build build-kissat -j4
    build-kissat/stp --kissat input.smt2

The equivalent CMake options are ``-DUSE_KISSAT=ON -DENABLE_AUTO_DOWNLOAD=ON``.
``Kissat_TAG`` can select another commit of the fork. The install records
its source revision; a shared dependency directory with another revision
must be replaced explicitly or a separate directory chosen.

``KISSAT_DIR`` selects a prebuilt checkout containing ``src/kissat.h`` and
``build/libkissat.a``. This explicit choice takes precedence over installed
copies and automatic downloads, including with ``STP_DEPS_LOCAL_ONLY=ON``.
For example:

.. code-block:: bash

    git clone --branch stp https://github.com/stp/kissat /path/to/kissat
    cd /path/to/kissat
    ./configure -fPIC -fexceptions
    make -j4

    cd /path/to/stp
    ./configure.sh release --ninja --name=build-kissat --auto-download \
        --no-cryptominisat --kissat-dir=/path/to/kissat

CMake checks the header and linked incremental API of a prebuilt library.
Native builds also run repeated SAT/UNSAT/SAT and clause-addition probes;
cross builds check that the API links. An unmodified upstream Kissat or the
older Kissat Extras fork does not provide this specific API.

CaDiCaL can stay enabled in the same binary. A Kissat-only build is also
supported: add ``--no-cadical --no-minisat --no-cryptominisat``.
``--sat-backend=kissat`` and the 3.x API's ``sat-backend`` option select the
same backend as ``--kissat``. Automatic selection retains the existing
preference for CryptoMiniSat, CaDiCaL and MiniSat when they are available.

Incremental SAT behavior
------------------------

The extension follows the restoration approach in Kissat Extras, based on
upstream 2.0.1, adapted to the current Kissat implementation. Upstream 4.0.4
already has an
``incremental`` option that retains both polarities of eliminated clauses;
the extension makes those records usable when clauses or assumptions revisit
an eliminated variable. It restores the complete extension rather than
tracking a smaller dependency closure. The learned clause database and
search phases survive.

Call ``kissat_set_option(solver, "incremental", 1)`` before the first solve.
``kissat_assume`` protects an assumption's variable from elimination and
substitution for that solve. Search decides the assumptions before ordinary
decisions, and detects a failed assumption without making the permanent
formula inconsistent. ``kissat_failed`` reports the assumptions reached
through the failure's reason graph. Assumptions and resource limits reset
after SAT, UNSAT, or UNKNOWN.

``kissat_protect`` and ``kissat_unprotect`` provide reference-counted
protection for variables that a client needs to keep. STP uses protection
for array indices and values. Preprocessing runs once per backend; subsequent
solves keep the learned clauses, inprocessing schedule, and stable restart
schedule. With ``incrementalreuse=1``, the next solve retains the shared
assumption prefix. Mode 2 can retain the entire search trail when the
assumptions are unchanged. New clauses unwind a retained trail only as far
as necessary; permanent units and elimination restoration require the root.
STP requests prefix reuse from its incremental driver and entire-trail reuse
from its refinement loops. ``--kissat-trail-reuse=false`` disables both hints.

Local search locks assumed variables to their required values and searches
over the remaining variables. A clause falsified entirely by locked variables
ends the walk and leaves the refutation to CDCL. Lucky model shortcuts are
still skipped while assumptions are active. Statistics expose restoration
counts, restored literals, reused solves, and retained decision levels.

The port also connects the registered termination callback to Kissat's
termination checks, including preprocessing and inprocessing. This allows
STP deadlines and external stop requests to interrupt an active search.

STP supplies per-instance allocation callbacks. A failed allocation becomes
the API's RESOURCE error; the allocation owner releases a partial solver
without traversing unfinished C structures. The CMake build enables C
exception unwinding. Prebuilt libraries used by a C++ client need
``-fexceptions`` too. Kissat's stdout reporter stays quiet; STP writes its
backend diagnostics through the normal diagnostic stream.

Factoring and variable identities
---------------------------------

Kissat's bounded variable addition creates external variable IDs. A caller
that later allocates another variable must allocate beyond those IDs too.
The STP adapter maps every STP variable to an external ID and consults
``kissat_maximum_variable`` before allocating a new one. Clauses,
assumptions, model queries, frozen variables, and phase hints use the same
mapping. Raw Kissat API clients must manage this namespace themselves or
disable ``factor``. In incremental mode, ``kissat_reserve`` reserves external
IDs even for variables that no clause mentions yet. The adapter reserves
its allocated IDs before a solve with factoring enabled.

``--kissat-factor=on|off|auto`` aliases the existing ``--cadical-factor``
control. ``--search-bias=unsat`` selects Kissat's focused search;
``--search-bias=sat`` uses its SAT configuration. Kissat's embedded Kitten
symbols have a ``kissat_`` prefix, so its archive can coexist with CaDiCaL's
different embedded Kitten implementation.
``--kissat-stable=0|1|2`` explicitly chooses focused, switching, or stable
search and overrides the search-bias hint; its default of -1 follows the hint.

Search profiles
---------------

``--sat-tuning=auto`` applies measured :doc:`automatic SAT defaults
<sat-tuning>` for supported backend, logic and session combinations. Explicit
options take precedence. ``--sat-tuning=off`` selects the baseline policy for
manual experiments such as the earlier profiles below.

The incremental benchmark experiments selected
``--kissat --search-bias=sat --kissat-factor=off`` for short sessions.
Focused search (``--search-bias=unsat``) also performed well at longer
cutoffs. For files with one query,
``--kissat --cnf-generation-effort=new-medium`` improved the encoding policy
used in those experiments. The automatic CNF policy contains settings
specific to CaDiCaL, so choosing a SAT backend can also require choosing an
encoding policy.

Probing controls
----------------

``--kissat-probe=true|false`` controls Kissat's probing preprocessing and
probe-based inprocessing. Its baseline default is ``true``. The automatic
incremental QF_ABV profile supplies ``false`` when this option is unset;
an explicit ``true`` preserves the user's choice. The SMT-LIB spelling is
``(set-option :kissat-probe false)``. Set it before the first check.

Disabling probing retains CDCL search and scheduled variable elimination.
It also skips the initial preprocessing route that requires probing. This
can reduce the cost of repeated array refinement without disabling the
incremental SAT API or changing the problem's meaning.

Decision phase controls
-----------------------

CaDiCaL and Kissat expose four expert options for controlled search
experiments. Each defaults to ``-1``, which preserves the backend's policy,
including any settings selected by ``--search-bias``. An explicit value
overrides the corresponding setting in the named search configuration.

.. list-table:: Phase options
    :header-rows: 1
    :widths: 25 75

    * - Option
      - Values
    * - ``--sat-phase``
      - ``0`` prefers false initially; ``1`` prefers true initially.
    * - ``--sat-forcephase``
      - ``0`` permits saved and target phases; ``1`` always chooses the initial phase.
    * - ``--sat-rephase``
      - ``0`` disables phase resetting; ``1`` enables it. CaDiCaL also accepts
        ``2`` to reset phases only during stable search.
    * - ``--sat-target``
      - ``0`` disables target phases; ``1`` uses them during stable search;
        ``2`` also uses them during focused search.

Set these options before the first check. The C++ and SMT-LIB interfaces use
the same option names, for example ``(set-option :sat-phase 0)``.
Other SAT backends reject explicit phase overrides. Use ``-s`` to print the
effective settings to the diagnostic stream.

.. code-block:: bash

    stp --kissat --search-bias=sat --sat-phase=0 -s input.smt2
    stp --cadical --sat-phase=0 --sat-forcephase=1 input.smt2

``scripts/benchmark-sat-backends.py`` records complete-session PAR2 and
supports frozen, resumable comparisons. Its
``scripts/benchmark-default-sat-backends.json`` preset selects the four SAT
backends with their defaults. ``scripts/sweep-sat-options.py`` screens
CaDiCaL and Kissat configurations, refines their CNF and factoring settings,
and evaluates fixed finalists against the defaults on the full selected logic.

Satsuma preprocessing
---------------------

Kissat supports the optional :doc:`Satsuma CNF preprocessing <satsuma>`
pipeline. Configure with ``-DUSE_KISSAT=ON -DUSE_SATSUMA=ON`` and select
``--kissat --satsuma=lex`` or ``--kissat --satsuma=fix`` at runtime.
Satsuma uses the same variable and clause interfaces as ordinary STP clause
loading. It is restricted to complete batch encodings; incremental sessions
and refinement queries bypass preprocessing, including with Kissat.

Testing
-------

The CI job builds STP with Kissat alone and with CaDiCaL alongside it.
The unit tests cover assumptions, cores, variable identities under factoring,
clause additions after a solve, interruption, and trail reuse. Query tests
exercise push/pop, model checking, arrays, and abstraction with Kissat.
Satsuma tests additionally cover both preprocessing modes, original models,
symmetry and the incremental/refinement bypass.

The fork also has its own Debug and Release CI jobs. Its CMake test runs
exhaustive differential checks of incremental results, models and cores;
the original configure/make test suite continues to run separately.

Current scope
-------------

The backend implements the incremental SAT contract needed for refinement.
It does not expose theory propagation callbacks, clause exchange, search
reset, or control of probe-based inprocessing. STP uses its existing
fallbacks for optional backend capabilities. Restoring the entire extension
can cost more than restoring only the variables a new clause needs.
Incremental proof output is outside the scope of this port.
