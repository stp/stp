; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; A comparison of a mux is the mux of the comparisons, so this formula is
; unsatisfiable. The two sides take different routes to the bit-blaster: the
; left operand is a float-sorted ITE, which the widened gate admits as a
; packed view (the bit-blaster muxes the branches), while the right side is
; two comparisons of plain symbols. If the mux ever selected the wrong
; branch -- or the branches were packed in the wrong order -- the two sides
; would disagree and this would be sat. The flag-off run proves the identity
; with both sides on SymFPU, whose ITE arm unpacks both branches instead.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun z () (_ FloatingPoint 8 24))
(declare-fun c () Bool)
(assert (xor (fp.gt (ite c x y) z)
             (ite c (fp.gt x z) (fp.gt y z))))
(check-sat)
(exit)
