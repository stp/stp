; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
; RUN: %solver -r %s | %OutputCheck %s
;
; A cell holding a NaN is greater than nothing, so this formula is
; unsatisfiable. Array cells are unconstrained bits, so the solver is free to
; choose any NaN payload for the cell -- the native isNaN test is field-based
; and does not care. fp.isNaN and fp.gt both blast natively over the same
; select here, and the -r run puts an if-then-else chain underneath them.
;
; CHECK: ^unsat
(set-logic QF_ABVFP)
(declare-fun A () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun i () (_ BitVec 4))
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNaN (select A i)))
(assert (fp.gt (select A i) x))
(check-sat)
(exit)
