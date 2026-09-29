; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; A rotation by the width or more ends the parse; the grammar reported it and
; then took a null node for the rotated term.
(benchmark b :logic QF_BV :extrafuns ((x BitVec[8])) :formula (= (rotate_left[9] x) bv1[8]))
; CHECK-L: Rotate must be strictly less than the width.
; CHECK-NOT: ^sat
