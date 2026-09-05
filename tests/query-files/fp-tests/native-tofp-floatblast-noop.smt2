; RUN: %solver --bb.fp-native-arith=true -s %s 2>&1 | %OutputCheck %s
;
; With the conversion arm, the fmcad12 shape -- narrow symbols widened,
; multiplied, added and compared in the wide format -- reaches the
; bit-blaster whole: FloatBlast builds no SymFPU circuit at all.
;
; CHECK: FloatBlast: 0 SymFPU operations, 0 unpacks, 0 packs
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 11 53))
(assert (fp.lt (fp.add RNE (fp.mul RNE ((_ to_fp 11 53) RNE x)
                                       ((_ to_fp 11 53) RNE y))
                           (fp.neg b))
               b))
(assert (not (fp.isNaN b)))
(check-sat)
(exit)
