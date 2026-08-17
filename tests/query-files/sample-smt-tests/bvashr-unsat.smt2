; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; 0b100 is -4, so shifting it right arithmetically gives 100, 110, then 111
; from two places on -- the sign bit fills from the left and never clears.
; 101 is therefore unreachable, and it sits one bit away from a value that is
; reachable, so getting the fill wrong turns this satisfiable.  Converted
; from sample-cvc-tests/bvashr-valid.cvc.
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun X () (_ BitVec 3))
(declare-fun Y () (_ BitVec 3))
(assert (= X #b100))
(assert (= (bvashr X Y) #b101))
(check-sat)
(exit)
