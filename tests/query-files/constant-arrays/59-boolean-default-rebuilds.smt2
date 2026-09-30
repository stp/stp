; RUN: %solver --array-equality --check-sanity %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=on %s | %OutputCheck %s
; RUN: %solver --array-equality --check-sanity --incremental=off %s | %OutputCheck %s
; Substitution and FP preparation rebuild packed Boolean defaults. The
; rebuilt default must retain the public Bool element sort at both stages.
; fp.to_ubv gains a choice field when its unspecified cases are totalised.
(set-option :produce-models true)
(set-logic QF_ABVFP)
(declare-fun flags () (Array (_ BitVec 8) Bool))
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun p () (_ BitVec 8))
(declare-fun q () (_ BitVec 8))
(declare-fun r () (_ BitVec 8))
(define-fun all-cells ((value Bool)) Bool
  (= flags ((as const (Array (_ BitVec 8) Bool)) value)))
(assert (all-cells (and (distinct p q r)
                       (bvult ((_ fp.to_ubv 8) RTZ x) #x01))))
; CHECK: ^sat$
(check-sat)
(push 1)
(assert (= x ((_ to_fp 8 24) #x3f800000)))
; CHECK: ^sat$
(check-sat)
; CHECK: false
(get-value ((select flags #x00)))
(assert (select flags #xff))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; CHECK: ^sat$
(check-sat)
