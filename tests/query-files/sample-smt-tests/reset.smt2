; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :smt-lib-version 2.5)
(set-info :category "check")
(set-info :status sat)

; CHECK-NEXT: ^sat
(check-sat)

; Reset on empty. 
(reset)

(declare-fun v0 () (_ BitVec 10))

; Should clear away v0.
(reset)

; So that we can create it again!
(declare-fun v0 () (_ BitVec 1))

(assert (= (_ bv0 1) ((_ extract 1 1) (bvnor (_ bv0 2) (bvnor (_ bv2 2) (concat (_ bv0 1) v0))))))
(set-info :status unsat)
; CHECK-NEXT: ^unsat
(check-sat)

; CHECK-NEXT: ^unsat
(check-sat)

(reset)


(declare-fun v0 () (_ BitVec 1))
(assert (= (_ bv0 1) ((_ extract 1 1) (bvnor (_ bv0 2) (bvnor (_ bv2 2) (concat (_ bv0 1) v0))))))
; CHECK-NEXT: ^unsat
(check-sat)
; CHECK-NEXT: ^unsat
(check-sat)
(reset)

(push 1)
(push 1)
(declare-fun v0 () (_ BitVec 1))
(assert (= (_ bv0 1) ((_ extract 1 1) (bvnor (_ bv0 2) (bvnor (_ bv2 2) (concat (_ bv0 1) v0))))))
; CHECK-NEXT: ^unsat
(check-sat)

(reset)
; Should have cleared away everythiung, so should be able to create it again..
(declare-fun v0 () (_ BitVec 1))


(exit)
