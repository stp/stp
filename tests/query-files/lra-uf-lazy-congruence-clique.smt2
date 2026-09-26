; RUN: %solver --SMTLIB2 -s %s 2>&1 | %OutputCheck %s
;
; Three arguments pinned to [0, 1] with three results that must differ. The
; first model may put all three arguments at 0, one collision group, or
; it may already separate some of them. Stating
; every disagreeing pair of a small group should settle this within one
; refinement round, using at most the three pairs. The deterministic
; UFLowering.LazySmallCollisionEmitsEveryPair unit test checks that a group
; of three really emits all three pairs, independently of model selection.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(assert (and (<= 0.0 a) (<= a 1.0)))
(assert (and (<= 0.0 b) (<= b 1.0)))
(assert (and (<= 0.0 c) (<= c 1.0)))
(assert (= (f a) 1.0))
(assert (= (f b) 2.0))
(assert (= (f c) 3.0))
; CHECK: rounds=(1 lemmas=0|2 lemmas=[1-3]) expanded=0 restarts=0
; CHECK: ^sat
(check-sat)
