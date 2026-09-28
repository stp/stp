; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --lra-model-reconstruction=on %s | %OutputCheck %s
;
; An active UF view declines model reconstruction, even when it is asked for
; by name. Once f is lowered, x and y each occur in one row only, so a pass
; removing dead definitions would take both rows out and leave x and y to be
; replayed afterwards. The congruence lemma this query needs, that (= x y)
; forces (= (f x) (f y)), arrives after the first model and constrains
; exactly those two, so it would be judged against values the arithmetic
; never chose.
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun t () Real)
(assert (= x (+ t 1)))
(assert (= y (+ t 1)))
(assert (not (= (f x) (f y))))
; CHECK: ^unsat
(check-sat)
