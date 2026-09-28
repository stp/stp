; RUN: %solver --bb.fp-native-arith=true -s %s 2>&1 | %OutputCheck %s
;
; With the native arithmetic flag, a formula whose floating-point content
; is entirely additions, multiplications, sign operations and predicates
; over symbols reaches the bit-blaster untouched: FloatBlast builds no
; SymFPU circuit at all, and its statistics line says so.
;
; CHECK: FloatBlast: 0 SymFPU operations, 0 unpacks, 0 packs
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))
(assert (fp.lt (fp.add RNE (fp.mul RNE x y) (fp.neg z)) (fp.abs y)))
(assert (fp.gt (fp.mul RNE x x) z))
(assert (not (fp.isNaN x)))
(check-sat)
(exit)
