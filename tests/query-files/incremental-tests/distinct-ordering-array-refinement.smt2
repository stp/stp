; A distinct-ordering block may contain ordinary lazy array reads even though
; no whole-array equality selected the exact-stack route. The ordered block is
; still assumption-scoped, but its reads must enter the ordinary congruence
; refinement loop. Disable the scoped word-level passes so equality propagation
; cannot prove this contradiction before that boundary is exercised.
;
; RUN: %solver -s --incremental=on --disable-cbitp --disable-equality --unconstrained-variable-elimination=0 --pure-literals=0 %s 2>&1 | %OutputCheck %s
; CHECK: Ordered 1 symmetric distinct group\(s\) in an assumption-scoped incremental block
; CHECK: Incremental: distinct-ordering round
; CHECK: Incremental: array refinement converged after 1 rounds
; CHECK: ^unsat
;
(set-logic QF_ABV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const A (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const i (_ BitVec 8))
(declare-const j (_ BitVec 8))
(assert (distinct a b c))
(assert (= i j))
(assert (not (= (select A i) (select A j))))
(check-sat)
