; Core-aware verdict caching: the first check is unsat and its failed
; assumptions all lie in the FIRST pushed level (the base bounds x below
; ten, the level demands more than twenty; the deeper level is
; irrelevant), so the frontend records unsat on that level's cache entry.
; Popping the irrelevant level and pushing a different one keeps the core
; levels intact, and the second check must answer from the cache without
; solving -- the --stats line below is printed by that shortcut, and no
; driver solve line appears for it. Popping into the core invalidates the
; entry (it is erased with the level), and the final check really solves,
; satisfiably.
; RUN: %solver -s --incremental %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental-auto-engage-at 1 %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (bvult x #x0a))
(push 1)
(assert (bvugt x #x14))
(push 1)
(assert p)
; CHECK: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert q)
; CHECK: Incremental: unsat answered from a cached core, no solve
; CHECK: ^unsat
(check-sat)
(pop 1)
(pop 1)
; CHECK: ^sat
(check-sat)
