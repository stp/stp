; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; Zero-extension leaves the unsigned value alone, so widening x by a bit
; cannot change which side of 3 it falls on.
;
; This file used to apply sign_extend despite its name, and still answered
; unsat, because the threshold it compared against was 2: below 2 a two-bit
; value has its top bit clear, and that is exactly where the two extensions
; agree.  At 3 they part company -- x = 10 zero-extends to 2, which is below
; 3, and sign-extends to 6, which is not -- so the operator under test is now
; the one that decides the answer.  Absorbs zero-extend.smt.
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)
(declare-fun x () (_ BitVec 2))
(assert (xor (bvult ((_ zero_extend 1) x) (_ bv3 3)) (bvult x (_ bv3 2))))
(check-sat)
(exit)
