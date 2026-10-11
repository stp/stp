; REQUIRES: cadical
; RUN: %solver --SMTLIB2 --cadical -s --lra-presolve-monotone=0 %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 --cadical -s --lra-presolve-monotone=0 --cnf-generation-effort medium %s 2>&1 | %OutputCheck --check-prefix=FORCED %s
; RUN: %solver --SMTLIB2 --cadical -s --lra-presolve-monotone=0 --lra-adaptive-cnf=1 %s 2>&1 | %OutputCheck --check-prefix=ADAPTIVE %s
; RUN: %solver --SMTLIB2 --cadical -s --lra-presolve-monotone=0 --lra-float-driver=1 %s 2>&1 | %OutputCheck --check-prefix=FLOAT %s
;
; Which CNF generator AUTO picks for a batch QF_LRA query, and that naming
; one or enabling the adaptive selector still overrides the fixed default.
; Keep the arithmetic atoms: monotone elimination can solve this before CNF.
;
; The adaptive selector keeps the old size-based Real route on this tiny
; skeleton and chooses very-low. The batch default instead takes new-medium.
;
; CHECK: batch QF_LRA default chose new-medium
; CHECK: "total_float_checks":0
; FORCED-NOT: batch QF_LRA default chose new-medium
; ADAPTIVE: chose very-low
; FLOAT: batch QF_LRA default chose new-medium
; FLOAT: "total_float_checks":[1-9][0-9]*
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
; ADAPTIVE: ^sat$
; FLOAT: ^sat$
(check-sat)
(exit)
