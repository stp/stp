; RUN: %solver --SMTLIB2 --unconstrained-image-vars=1 -d %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 -d %s | %OutputCheck %s
;
; Satisfiable: v1 = 1 makes both sides of the comparison equal.
;
; With --unconstrained-image-vars the shared sign-extension of the
; single-use v is replaced by a fresh variable I with "I is a fixed point
; of re-extension" set aside as a conjunct. Then v1, single-use under the
; xor, turns the xor into a fresh variable, and I loses that parent. With
; the conjunct outside the mutable tree, I looked single-use, and the
; comparison rule gave it an extreme value that the set-aside conjunct
; excludes: a wrong unsat. Reduced from a fuzzer case.
;
; CHECK: ^sat$
(set-logic QF_BV)
(declare-fun v () (_ BitVec 84))
(declare-fun v1 () (_ BitVec 96))
(assert (bvult (_ bv0 1) (ite (bvsge ((_ sign_extend 12) v) (bvxor v1 (_ bv1 96) ((_ sign_extend 12) v))) (_ bv1 1) (_ bv0 1))))
(check-sat)
