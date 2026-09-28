; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; A Real ite whose condition is a Bool-sorted uninterpreted-function
; application, over an argument that holds an ite of its own. Reading a value
; through this walks the counterexample to decide the inner condition, and
; that walk is where a stale condition oracle -- one captured on the solve's
; coordinator, which by then had been destroyed -- read ASTTrue and ASTFalse
; out of freed memory. A condition that had evaluated to FALSE was reported as
; not a Boolean constant, and the model refused a term it could value.
; CHECK-NEXT: ^sat$
(set-logic QF_UFLRA)
(declare-fun c1 () Bool)
(declare-fun y () Real)
(declare-fun g (Real) Bool)
(declare-fun h (Real) Real)
(declare-fun k (Real) Real)
(assert (> 4.0 (k (ite (g (* (+ (ite c1 y 4.0) y) 2.0)) (h 4.0) 4.0))))
(check-sat)
(exit)
