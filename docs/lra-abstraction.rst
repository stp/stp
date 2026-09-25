LRA arithmetic and search controls
==================================

These experimental batch-query controls independently vary arithmetic state,
row insertion order and SAT search history. All four default to ``0``.

* ``--lra-extension-mode=0`` chooses automatically: ordinary batch UF
  refinement rebuilds the arithmetic context. ``1`` always extends in place.
  ``2`` always rebuilds the context. ``3`` extends in place, then resets both
  arithmetic assignments and bases, preserving all allocated IDs and their
  interleaved column/row order. SAT search persists in each of these modes.
* ``--lra-row-order=0`` retains registry order. ``1`` reverses new arithmetic
  rows, ``2`` inserts sparse rows first, and ``3`` inserts dense rows first.
  Ties retain registry order. This changes construction of the exact and
  floating tableaux; it preserves Boolean atom creation and CNF order.
  Each later extension orders its newly added rows using the same policy.
* ``--lra-extension-restart-float-basis=1`` restores the advisory slack basis
  after extensions, retaining structural-variable assignments and IDs. The
  exact tier is retained. Mode ``3`` takes precedence and resets assignments
  in both tiers. Experimental resets do not consume numerical-recovery
  budgets; their work is measured separately.
* ``--lra-extension-restart-sat=1`` copies the Boolean formula into a fresh
  CaDiCaL instance after each permanent extension. CaDiCaL copies irredundant
  clauses, units, options, preprocessing state and witness reconstruction;
  redundant learned clauses, activities and saved phases are discarded.
  This keeps the formula's models and external variable identities, but
  does not undo preprocessing or replay the original clause order. Solve
  assumptions are reapplied normally and the query deadline is retained.

Nondefault controls require batch solving; persistent-session modes are
rejected. SAT search reset requires CaDiCaL with factoring disabled
(``--cadical-factor=off``). The controls still use exact
model and conflict checking. ``context_reuses``, ``arithmetic_state_resets``,
``float_basis_resets`` and ``sat_search_resets`` show which paths ran.
``total_exact_pivots``, ``total_float_checks``, ``total_float_pivots``,
``total_float_check_ns`` and ``total_float_sync_ns`` include retired arithmetic
contexts as well as the final context. The other work fields describe the
final context only, and can omit work when rebuilding is enabled.
