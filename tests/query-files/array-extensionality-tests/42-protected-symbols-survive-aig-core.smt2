; RUN: %solver --array-equality --aig-core-simplification=1 %s | %OutputCheck %s
; CHECK: ^unsat
; The AIG propositional-core rewrite removes occurrences of a formula's
; symbols without recording any substitution, so it can leave an
; equality abstraction variable or a witness-read name with a single
; occurrence. Unconstrained-variable elimination then treats such a
; symbol as free: every one of its rules mutates the graph before
; recording the variable's replacement, so the substitution map's
; refusal to record a definition the array procedure depends on comes
; too late to undo the rewrite -- the defining equation is simply gone,
; and the solve dies either recovering the equality operands or in the
; refinement driver. Protected symbols must therefore never be reported
; unconstrained at all. Before that fix 19 of this directory's tests
; aborted under this option; the query below is the smallest of them.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(assert (= a b))
(assert (not (= (select a i) (select b i))))
(check-sat)
