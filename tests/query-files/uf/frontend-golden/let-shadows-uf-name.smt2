; A local binder is resolved before the global UF namespace.  The same name
; remains an applicable function outside the let expression.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^"REACHED-END"
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (let ((f #x03)) (bvadd f #x01)) #x04))
(assert (= (f x) (f x)))
(check-sat)
(echo "REACHED-END")
