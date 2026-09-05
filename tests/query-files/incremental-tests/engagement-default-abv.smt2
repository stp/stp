; QF_ABV uses the same measured solve-32 policy as QF_BV. Keep an actual
; array read live so this pins the declared and exercised fragment.
; RUN: %solver -s %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))
(push 1)

(assert (= (select a #x00) x))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xff))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xfe))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xfd))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xfc))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xfb))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xfa))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf9))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf8))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf7))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf6))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf5))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf4))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf3))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf2))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf1))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xf0))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xef))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xee))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xed))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xec))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xeb))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xea))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xe9))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xe8))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xe7))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xe6))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xe5))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xe4))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xe3))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)
(assert (bvult x #xe2))
; CHECK-NOT: Incremental: encoded
; CHECK: ^sat
(check-sat)

(assert (bvult x #xe1))
; CHECK: Incremental: encoded
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
