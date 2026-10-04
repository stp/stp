; RUN: %solver --incremental=on --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at=1 --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental=on -d --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
;
; The remainder's defining relation, the same defect as the square root's:
; fresh quotient and remainder inputs that one root alone used to constrain,
; with the registry naming the first root's proxy for every later one.
;
; x in [4.5, 5) over a divisor of 4 rounds the quotient to 1, so the
; remainder is x - 4 in [0.5, 1) and its IEEE encoding is at least
; 0x3F000000. Requiring it to be less is unsatisfiable; with the proxy
; standing for nothing the second query answered sat.
(set-logic QF_BVFP)
(declare-fun x () Float32)
(declare-fun y () (_ BitVec 32))
(declare-fun v () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(declare-fun w () (_ BitVec 32))
(push 1)
(assert (= (bvand y v) (fp.to_ieee_bv (fp.rem x ((_ to_fp 8 24) RNE 4.0)))))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (bvand z w) (fp.to_ieee_bv (fp.rem x ((_ to_fp 8 24) RNE 4.0)))))
(assert (fp.geq x ((_ to_fp 8 24) RNE 4.5)))
(assert (fp.lt x ((_ to_fp 8 24) RNE 5.0)))
(assert (bvult (bvand z w) #x3F000000))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
