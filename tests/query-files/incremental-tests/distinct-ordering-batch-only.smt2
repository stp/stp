; The ordering rewrite does not reach the persistent driver, and must not.
;
; Batch rebuilds the formula from the stored assertions at every solve, so the
; guard is re-decided each time and an assertion arriving after one check-sat
; simply stops the rewrite applying at the next. The driver's clauses are
; persistent: a chain encoded into a block would stay in force when a later
; assertion destroyed the symmetry that justified it, and there is no round
; at which that could be noticed. The containment is structural -- the driver
; has its own path and never enters the batch pipeline -- and this pins it,
; because it is the kind of separation a refactor removes by accident.
;
; The middle solve is where a leak would be a wrong answer rather than a
; missing stats line: a is compared there, so an inherited a < b < c would
; contradict a > b and report unsat, and the answer is sat. The last solve
; pops that comparison away and asserts something unrelated instead, and the
; group is orderable again -- the decision is per solve, in both directions.
;
; RUN: %solver -s --incremental=off %s 2>&1 | %OutputCheck --check-prefix=BATCH %s
; RUN: %solver -s --incremental=on %s 2>&1 | %OutputCheck --check-prefix=DRIVER %s
;
; BATCH: Ordered 1 symmetric distinct group\(s\)
; BATCH: ^sat
; BATCH: SYMMETRIC-DONE
; BATCH-NOT: Ordered
; BATCH: ^sat
; BATCH: COMPARED-DONE
; BATCH: Ordered 1 symmetric distinct group\(s\)
; BATCH: ^sat
;
; DRIVER-NOT: Ordered
; DRIVER: ^sat
; DRIVER: SYMMETRIC-DONE
; DRIVER-NOT: Ordered
; DRIVER: ^sat
; DRIVER: COMPARED-DONE
; DRIVER-NOT: Ordered
; DRIVER: ^sat
;
(set-logic QF_BV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const keep (_ BitVec 8))
(assert (distinct a b c))
(check-sat)
(echo "SYMMETRIC-DONE")
(push 1)
(assert (bvugt a b))
(check-sat)
(echo "COMPARED-DONE")
(pop 1)
(assert (bvult keep #x10))
(check-sat)
