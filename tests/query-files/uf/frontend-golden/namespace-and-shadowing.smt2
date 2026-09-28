; RUN: %solver --uninterpreted-functions --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s | %OutputCheck %s
; CHECK: ^sat
; CHECK: REACHED-END
;
; UF declarations, scalar symbols and define-fun macros share the SMT-LIB
; top-level namespace; redeclaration-is-fatal pins what happens when two of
; them want the same name. This is the other side of it: nested let binders
; are not top-level declarations, so they shadow normally and resolve before
; UF application hash-consing, no matter that the shadowed name is a UF's.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(define-fun m ((q (_ BitVec 8))) (_ BitVec 8) q)
(assert (= (let ((x #x01)) (let ((x #x02)) (f x))) (f #x02)))
(assert (= (m x) x))
(check-sat)
(echo "REACHED-END")
