; Incremental ordering rides a whole-stack root assumption. Its AIG and CNF
; definitions may persist, but the root itself is assumed only for the solve
; whose complete active formula passed the occurrence guard.
;
; The middle solve is the soundness case: a is compared there, so the group is
; no longer symmetric. The first solve's a < b < c chain must be retracted;
; retaining it would contradict a > b and incorrectly answer unsat. Once that
; comparison is popped, the unrelated keep assertion is eliminated by scoped
; preprocessing, the group is orderable again, and the first block is reused.
;
; RUN: %solver -s --incremental=off %s 2>&1 | %OutputCheck --check-prefix=BATCH %s
; RUN: %solver -s --incremental=on %s 2>&1 | %OutputCheck --check-prefix=DRIVER %s
; RUN: %solver -s --check-sanity --incremental=on %s 2>&1 | %OutputCheck --check-prefix=DRIVER %s
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
; DRIVER: Ordered 1 symmetric distinct group\(s\) in an assumption-scoped incremental block
; DRIVER: Incremental: distinct-ordering round, block of 1 levels encoded
; DRIVER: ^sat
; DRIVER: SYMMETRIC-DONE
; DRIVER-NOT: Ordered
; DRIVER: Incremental: encoded
; DRIVER: ^sat
; DRIVER: COMPARED-DONE
; DRIVER: Ordered 1 symmetric distinct group\(s\) in an assumption-scoped incremental block
; DRIVER: Incremental: distinct-ordering round, block of 1 levels reused
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
