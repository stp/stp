; With the default :global-declarations false, reset-assertions drops both
; declarations.  Reusing the old application must fail before another
; check-sat is issued.
;
; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^\(error ".*f.*"\)
; CHECK-NOT: REACHED-END
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 4)) (_ BitVec 4))
(declare-const x (_ BitVec 4))
(assert (distinct (f x) (f x)))
(check-sat)
(reset-assertions)
(assert (= (f x) (f x)))
(check-sat)
(echo "REACHED-END")
