; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
; RUN: %solver -r %s | %OutputCheck %s
;
; Read congruence underneath a surviving native comparison: equal indices
; select the same cell, so a non-NaN cell is greater-or-equal to itself and
; this formula is unsatisfiable, under read refinement and under eager
; Ackermannization (-r).
;
; A select from a float-element array is already the packed element bits, so
; the gate admits it and the comparison consumes them directly -- which means
; the array machinery rewrites the operand UNDERNEATH a surviving
; floating-point node. Every stand-in it mints for a read has to keep the
; element format; if one does not, the comparison arrives at the blaster with
; no format to compare in (see native-read-array-equality.smt2, which is the
; case where that was true).
;
; CHECK: ^unsat
(set-logic QF_ABVFP)
(declare-fun A () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun i () (_ BitVec 4))
(declare-fun j () (_ BitVec 4))
(assert (= i j))
(assert (not (fp.isNaN (select A i))))
(assert (not (fp.geq (select A i) (select A j))))
(check-sat)
(exit)
