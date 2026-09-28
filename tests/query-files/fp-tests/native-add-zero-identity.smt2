; RUN: %solver --bb.fp-native-arith=true %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-arith=true --disable-simplifications %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
;
; Adding +0 is exact for every non-NaN operand -- fp.eq-exact, not
; bit-exact: -0 + +0 is +0, which fp.eq still identifies with -0. In the
; native adder this exercises the zero operand flowing through the general
; datapath (a zero significand adds exactly); there is no zero special
; case to hide behind.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.eq (fp.add RNE x ((_ to_fp 8 24) #x00000000)) x)))
(check-sat)
(exit)
