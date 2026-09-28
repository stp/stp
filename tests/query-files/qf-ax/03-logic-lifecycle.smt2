; QF_AX's automatic array-equality selection follows the logic lifecycle.
; reset-assertions retains it; reset clears it and restores the caller's prior
; option. Passing --array-equality explicitly therefore makes the final QF_ABV
; query legal, while the default run rejects it.
;
; RUN: not %solver --incremental=off %s 2>&1 | %OutputCheck --check-prefix=DEFAULT %s
; RUN: not %solver --incremental=on  %s 2>&1 | %OutputCheck --check-prefix=DEFAULT %s
; RUN: %solver --incremental=off --array-equality %s 2>&1 | %OutputCheck --check-prefix=EXPLICIT %s
; RUN: %solver --incremental=on  --array-equality %s 2>&1 | %OutputCheck --check-prefix=EXPLICIT %s
; DEFAULT: ^sat
; DEFAULT: ^sat
; DEFAULT: without --array-equality
; DEFAULT-NOT: REACHED-END
; EXPLICIT: ^sat
; EXPLICIT: ^sat
; EXPLICIT: ^sat
; EXPLICIT: REACHED-END
;
(set-logic QF_AX)
(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun b () (Array I E))
(assert (= a b))
(check-sat)

(reset-assertions)
(declare-sort I 0)
(declare-sort E 0)
(declare-fun a () (Array I E))
(declare-fun b () (Array I E))
(assert (= a b))
(check-sat)

(reset)
(set-logic QF_ABV)
(declare-fun x () (Array (_ BitVec 1) (_ BitVec 1)))
(declare-fun y () (Array (_ BitVec 1) (_ BitVec 1)))
(assert (= x y))
(check-sat)
(echo "REACHED-END")
