; RUN: %solver --SMTLIB2 -s --uf-propagate-equalities=on %s 2>&1 | %OutputCheck %s
;
; The pass is asked for by name because AUTO declines it on a Real query --
; it measures as a loss there; see uf-prelowering-auto-real.smt2. What this
; file pins is that it is still correct when a caller asks for it anyway,
; which is what ON is for. The crash below is the reason that matters: a
; pass that dies on Real content would be a defect at any default.
;
; The pre-lowering pass over Real-sorted symbols. The pass was written for
; bit-vectors and every file in tests/query-files/uf exercises it there;
; a Real reaches it only through the Real path. Two things could go wrong,
; and this file is the plain case for both.
;
; The first is a crash: GetIndexWidth() is a FatalError on a mathematical
; Real, not a zero, so a pass that asks a symbol for one before deciding
; whether it is an array dies here rather than answering.
;
; The second is quieter, and is why the substitution count is checked rather
; than the verdict alone. A pass that simply declines to see Real symbols
; would still answer unsat -- the lazy congruence loop is behind it and would
; state the lemma instead -- while doing none of the work this pass exists
; for. So the counts are named, and CHECK-NOT holds the loop to having had
; nothing left to do.
;
; This is uf/19-equality-merges-applications.smt2 with the sort changed.
; CHECK: UF: pre-lowering substituted 2 symbol\(s\) and 0 application\(s\) and 1 asserted atom\(s\) in 1 round\(s\), 0 application\(s\) remain
; CHECK-NOT: installed congruence lemma
; CHECK: ^unsat$
(set-logic QF_UFLRA)
(declare-fun g (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (= x y))
(assert (= y z))
(assert (distinct (g x) (g z)))
(check-sat)
