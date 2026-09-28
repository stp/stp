; source-sort-boundary pins RoundingMode and FloatingPoint as admitted DOMAIN
; sorts. This pins them as admitted RESULT sorts, which is a separate row of
; the same table: the declaration goes through, the application is congruent,
; and the refutation below needs both to be true.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s | %OutputCheck %s
; CHECK: ^unsat
; CHECK-NOT: unsupported domain sort
; CHECK-NOT: unsupported result sort
(set-logic QF_UFABVFP)
(declare-fun ok-fp ((_ BitVec 8)) (_ FloatingPoint 8 24))
(declare-fun ok-rm (RoundingMode) RoundingMode)
(assert (distinct (ok-rm RNE) (ok-rm RNE)))
(assert (distinct (ok-fp #x00) (ok-fp #x00)))
(check-sat)
(exit)
