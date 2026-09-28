; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
; RUN: %solver -r %s | %OutputCheck %s
;
; Read-over-write underneath a surviving native comparison: selecting the
; cell just stored gives back the stored value, so a non-NaN v equals itself
; and this formula is unsatisfiable. The array transform expands the write
; chain into an if-then-else over the stored value and a fresh read variable,
; so the comparison's operand is rebuilt as a mux underneath it and both arms
; have to keep the element format.
;
; CHECK: ^unsat
(set-logic QF_ABVFP)
(declare-fun A () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun i () (_ BitVec 4))
(declare-fun v () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN v)))
(assert (not (fp.eq (select (store A i v) i) v)))
(check-sat)
(exit)
