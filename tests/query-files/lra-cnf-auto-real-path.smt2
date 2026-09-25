; RUN: %solver --SMTLIB2 -s --lra-presolve-monotone=0 %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 -s --lra-presolve-monotone=0 --cnf-generation-effort medium %s 2>&1 | %OutputCheck --check-prefix=FORCED %s
;
; Which CNF generator AUTO picks for a Real query, and that naming one still
; overrides the choice.
; Keep the arithmetic atoms: monotone elimination can solve this before CNF.
;
; The threshold is read one way for the Real path and another for bit-vectors,
; because the two want opposite ends of it. This skeleton is small -- well
; under cnf_auto_threshold, which is where nearly every Real query lands -- so
; the Real path takes VERY_LOW here, where a bit-vector query of the same size
; takes MEDIUM and keeps it. Above the threshold the Real path takes LOW
; instead, for the reason the flag was introduced; that end is not exercised
; here because it needs a skeleton of a few hundred thousand AIG nodes.
;
; The second run pins the override: --cnf-generation-effort is not AUTO, so
; none of this reasoning runs and the named effort is used as given.
; CHECK: chose very-low
; FORCED-NOT: chose very-low
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun b () Bool)
(assert (or b (< (+ x y) 3.0)))
(assert (or (not b) (> (- z y) 1.0)))
(assert (<= (+ x (* 2.0 z)) 8.0))
(assert (>= (+ y z) 0.5))
; CHECK: ^sat$
; FORCED: ^sat$
(check-sat)
(exit)
