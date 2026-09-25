; RUN: %solver --SMTLIB2 --lra-presolve-unconstrained=1 %s | %OutputCheck %s
;
; The unconstrained-elimination presolve runs on the root the UF lowering has
; already rewritten, where an application has become a result symbol. Those
; symbols are not free variables: congruence ties two of them together when
; their applications' arguments agree, and the lowering states that as lemmas
; it adds during the solve, not as conjuncts this pass can see. Witnessing one
; to make an atom over it false therefore forced a disagreement congruence
; forbids, and this satisfiable query came back unsat.
;
; (> x x) is false, so the third application is f(false), which must differ
; from f(not (< 6/8434 x)); that forces (< 6/8434 x) false, and then the first
; assertion forces f(false) > f(true). An uninterpreted f can do that.
; CHECK-NEXT: ^sat$
(set-logic QF_UFLRA)
(declare-fun x () Real)
(declare-fun f (Bool) Real)
(assert (distinct (< (/ 6 8434) x)
                  (>= (f (< (/ 6 8434) x)) (f (not (< (/ 6 8434) x))))))
(assert (distinct (f (and (> x x) (not (< (/ 6 8434) x))))
                  (f (not (< (/ 6 8434) x)))))
(check-sat)
(exit)
