; RUN: %solver --SMTLIB2 -s --uf-propagate-equalities=on %s 2>&1 | %OutputCheck %s
;
; The pass is asked for by name because AUTO declines it on a Real query --
; it measures as a loss there; see uf-prelowering-auto-real.smt2. What this
; file pins is that it is still correct when a caller asks for it anyway,
; which is what ON is for. The crash below is the reason that matters: a
; pass that dies on Real content would be a defect at any default.
;
; A Real symbol substituted by a Real *term*, which is the case that reaches
; the rewrite rather than only the candidate search: `a` goes to `b + 1`, so
; the application holding it has to be rebuilt around the new argument.
;
; Rebuilding is where a Real term is most easily lost. The widths a
; bit-vector node is put back together with are a FatalError to ask a Real
; for, so the rebuild has to go through CreateNode instead -- and that is
; only sound because an interior node's source sort is derived from its
; operator and children rather than stored: REAL_ADD is Real by its kind,
; and an application by the sort of the function in its first position,
; which the rewrite keeps as it found it.
;
; The verdict is what proves it worked. `unsat` needs the rebuilt
; `(g (+ b 1))` to be the same application as `(g a)`; a rebuild that came
; back as an untyped or differently-sorted term would leave the two apart
; and the query satisfiable.
; CHECK: UF: pre-lowering substituted 1 symbol\(s\) and 1 application\(s\) and 1 asserted atom\(s\) in 1 round\(s\), 0 application\(s\) remain
; CHECK: ^unsat$
(set-logic QF_UFLRA)
(declare-fun g (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= a (+ b 1.0)))
(assert (= (g a) 5.0))
(assert (not (= (g (+ b 1.0)) 5.0)))
(check-sat)
