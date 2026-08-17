; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |c| () (_ BitVec 8) #xFE)
; CHECK-L: (define-fun |n| () (_ BitVec 32) #x00000008)
; A chain of shared decrements: n is below 9 and none of n, n-1, ... n-7 is
; zero, which leaves 8 as the only value n can take.  Every constraint is
; load-bearing -- drop or shift any one of them and a smaller n becomes
; admissible -- so the pinned model value is a real check.
;
; This replaces the sample-cvc a127/a128/a163/a165/a166/a168-a171/a173/a175/
; a177-a182 family, which was one formula unrolled to seventeen depths, each
; file only checking that the answer was Invalid.
(set-logic QF_BV)
(set-option :produce-models true)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun n () (_ BitVec 32))
(declare-fun c () (_ BitVec 8))
(assert (= (concat #x000000 c) #x000000FE))
(assert (bvult n #x00000009))
(assert (let ((m1 (bvneg #x00000001)))
        (let ((d1 (bvadd n m1)))
        (let ((d2 (bvadd m1 d1)))
        (let ((d3 (bvadd m1 d2)))
        (let ((d4 (bvadd m1 d3)))
        (let ((d5 (bvadd m1 d4)))
        (let ((d6 (bvadd m1 d5)))
        (let ((d7 (bvadd m1 d6)))
          (and (not (= n  #x00000000))
               (not (= d1 #x00000000))
               (not (= d2 #x00000000))
               (not (= d3 #x00000000))
               (not (= d4 #x00000000))
               (not (= d5 #x00000000))
               (not (= d6 #x00000000))
               (not (= d7 #x00000000))))))))))))
(check-sat)
(get-model)
