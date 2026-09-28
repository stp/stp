; REQUIRES: cadical
; The adaptive late-FP retirement belongs to source array+FP sessions, not
; array-free QF_BVFP. The latter recovered five campaign solves by retaining
; its established trail. Totalising fp.to_ubv introduces an internal
; unspecified-value array, but that implementation detail must not make this
; source formula look like QF_ABVFP to the trail policy.
;
; Six BV checks establish the late-transition window. All four checks after
; FP arrives keep the trail: the complementary source-array test
; trail-reuse-kept-for-late-fp.smt2 retires on its fourth small FP check.
; RUN: %solver --cadical --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck %s
(set-logic QF_BVFP)
(declare-fun x () (_ BitVec 8))
(declare-fun f () (_ FloatingPoint 8 24))

(push 1)
(assert (= x #x01))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= x #x02))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= x #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= x #x04))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= x #x05))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= x #x06))
; CHECK: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (= ((_ fp.to_ubv 8) RNE f) #x00))
; CHECK: Incremental profile cbp/backend: check=7 .*rebuild-trail=0
; CHECK: ^sat
(check-sat)
; CHECK: Incremental profile cbp/backend: check=8 .*rebuild-trail=0
; CHECK: ^sat
(check-sat)
; CHECK: Incremental profile cbp/backend: check=9 .*rebuild-trail=0
; CHECK: ^sat
(check-sat)
; CHECK: Incremental profile cbp/backend: check=10 .*rebuild-trail=0
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
