; Unsupported UF signature sorts reject their declarations transactionally,
; and the admitted ones go through in the same session so that the boundary
; between the two is pinned from both sides.
;
; RoundingMode and FloatingPoint moved across that boundary and are now
; admitted; the rows for them are retained as positive ones rather than
; dropped, so a regression that re-rejected either sort would fail here as
; loudly as one that admitted Array.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: unsupported domain sort \(_ BitVec 0\) at argument 0 of bad-zero
; CHECK: unsupported domain sort \(Array \(_ BitVec 4\) \(_ BitVec 4\)\) at argument 0 of bad-array
; CHECK-NOT: of ok-fp
; CHECK-NOT: of ok-rm
; CHECK: ^unsat
; CHECK: ^"REACHED-END"
;
(set-logic QF_UFABVFP)
(declare-fun bad-zero ((_ BitVec 0)) Bool)
(declare-fun bad-array ((Array (_ BitVec 4) (_ BitVec 4))) Bool)
(declare-fun ok-fp ((_ BitVec 8)) (_ FloatingPoint 8 24))
(declare-fun ok-rm (RoundingMode) RoundingMode)
(assert (distinct (ok-rm RNE) (ok-rm RNE)))
(assert (distinct (ok-fp #x00) (ok-fp #x00)))
(check-sat)
(echo "REACHED-END")
(exit)
