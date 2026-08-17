; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The companion of decrement-chain-sat.smt2, one notch tighter: n below 8
; leaves the chain of eight disequalities nothing to pick.  Loosening the
; bound by one, or shifting any constant in the chain, makes it satisfiable
; again, so this pins the same reasoning from the other side.
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun n () (_ BitVec 32))
(declare-fun c () (_ BitVec 8))
(assert (= (concat #x000000 c) #x000000FE))
(assert (bvult n #x00000008))
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
(exit)
