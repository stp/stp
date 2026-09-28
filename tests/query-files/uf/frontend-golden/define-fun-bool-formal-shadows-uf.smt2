; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^"REACHED-END"
;
; Boolean formals obey the same binder-before-global-namespace rule as
; bit-vector formals.
(set-logic QF_UFBV)
(declare-fun predicate (Bool) Bool)
(define-fun identity ((predicate Bool)) Bool predicate)
(assert (not (identity true)))
(check-sat)
(echo "REACHED-END")
