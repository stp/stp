; Boolean parameters in define-fun are part of the ordinary SMT-LIB surface,
; including with UF support disabled.  This is also the form emitted for a
; Bool-domain function model, so the printer's output must reparse.
;
; RUN: %solver %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^"REACHED-END"
;
(set-logic QF_BV)
(define-fun mand ((a Bool) (b Bool)) Bool (and a b))
(define-fun g ((x0 Bool) (x1 (_ BitVec 2))) Bool
  (ite (and (= x0 true) (= x1 #b01)) true false))
(declare-const p Bool)
(declare-const w (_ BitVec 2))
(assert (mand p true))
(assert (g true #b01))
(assert (not (g p w)))
(check-sat)
(echo "REACHED-END")
