; RUN: not %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: not %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^\(error "get-value requires :produce-models true"\)
; CHECK-NOT: REACHED-END
; CHECK-NOT: define-fun
;
; UF certification needs an internal candidate in both modes, but that does
; not grant permission to publish get-value or get-model results when the
; caller left :produce-models disabled.
(set-option :produce-models false)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (f x) #x2a))
(check-sat)
(get-value ((f x)))
(get-model)
(echo "REACHED-END")
