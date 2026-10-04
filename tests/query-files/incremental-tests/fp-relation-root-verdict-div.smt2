; RUN: %solver --incremental=on --bb.fp-native-div=1 --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at=1 --bb.fp-native-div=1 --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental=on -d --bb.fp-native-div=1 --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
;
; The divide's defining relation, the third of the three native
; floating-point encodings that mint fresh inputs, reached through
; --bb.fp-native-div since it is off by default.
;
; x in [8, 12) over a divisor of 4 gives a quotient in [2, 3), whose IEEE
; encoding is at least 0x40000000. Requiring it to be less is unsatisfiable;
; with the proxy standing for nothing the second query answered sat.
(set-logic QF_BVFP)
(declare-fun x () Float32)
(declare-fun y () (_ BitVec 32))
(declare-fun v () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(declare-fun w () (_ BitVec 32))
(push 1)
(assert (= (bvand y v) (fp.to_ieee_bv (fp.div RNE x ((_ to_fp 8 24) RNE 4.0)))))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (= (bvand z w) (fp.to_ieee_bv (fp.div RNE x ((_ to_fp 8 24) RNE 4.0)))))
(assert (fp.geq x ((_ to_fp 8 24) RNE 8.0)))
(assert (fp.lt x ((_ to_fp 8 24) RNE 12.0)))
(assert (bvult (bvand z w) #x40000000))
; CHECK-NEXT: ^unsat
(check-sat)
(exit)
