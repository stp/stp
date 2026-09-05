; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; The SMT domain has ONE NaN: payloads are a detail of the encoding, so all
; NaNs are = to each other and this formula is unsatisfiable. This is the
; test for the both-NaN disjunct in the native encoding (BBeqFP) -- plain
; equality of the packed bits fails it, because the SAT solver simply picks
; two different payloads (or two different NaN signs) for x and y.
; fp.isNaN still lowers through SymFPU, and the third run proves that path
; agrees.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (fp.isNaN y))
(assert (not (= x y)))
(check-sat)
(exit)
