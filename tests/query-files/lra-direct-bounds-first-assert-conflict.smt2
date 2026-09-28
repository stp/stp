; RUN: %solver --SMTLIB2 --lra-direct-bounds=2 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --lra-direct-bounds=1 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; With the float driver, the exact core is brought up to the float trail one
; batch per decision level. When the first assert of a new batch conflicted
; at once, the adapter dropped the batch's record but not the level it had
; pushed on the core. The search then backtracked only to the level below,
; where no remaining batch was deep enough to pop, so the core stayed in
; Conflict: every later sync was refused and the final check gave up with
; "float final check produced no usable verdict", answering unknown.
; Direct bounds put a variable's scaled bounds on the variable itself, which
; is what makes a first-assert conflict likely here.
;
; Reduced from a FuzzSMT QF_LRA file.
; CHECK-NEXT: ^sat$
(set-logic QF_LRA)
(declare-const x1 Real)
(declare-const x Bool)
(declare-const x7 Bool)
(declare-const x5 Real)
(declare-fun v () Real)
(declare-fun v6 () Real)
(declare-fun v61 () Real)
(assert (let ((e6367 (and x7 (and (< 1.0 x5) (= (>= (* v (- 1)) (ite x 0.0 (* 6 (- v61)))) (>= v6 (ite (distinct (- v61) (* v (- 1))) (* 12 (- v61)) 0.0))))))) (=> (= (= (- v61) (* v (- 1))) (= (< (ite x7 0.0 (ite (> 0.0 0.0) 0.0 v6)) 0.0) (distinct (>= v 0.0) (distinct (ite (> 0.0 0.0) 0.0 (ite (> (- v v6 0.0) (* 6 (- v61))) v (* 12 12 v61))) (ite (distinct (+ v6 x5) (* v (- 1))) (ite (distinct v61 x1 (ite (> 0.0 (* 3 (- v61))) v (* 12 12 v61))) (ite (> v v61) x5 (ite (distinct v61 (* 6 (- v61)) (- v6 (- v61))) (* 12 12 v61) (ite (distinct 0.0 (* 3 v61 3)) 0.0 (* 3 (- v61))))) (ite (distinct v61 (* 6 (- v61)) (- v6 (- v61))) (* 12 12 v61) (ite (distinct 0.0 (* 3 v61 3)) 0.0 (* 3 (- v61))))) v61) (ite (> 0.0 0.0) 0.0 v6))))) (= (distinct x (< (+ v6 (- v x5 (* 12 (- v61)))) x5)) (not (<= (ite (= v (* 6 (- v61))) 0.0 (ite (distinct v61 x1 (ite (> (- v v6 0.0) (* 6 (- v61))) v (* 12 12 v61))) (ite (> v v61) x5 (ite (distinct v61 (* 6 (- v61)) (- v6 (- v61))) (* 12 12 v61) (ite (distinct 0.0 (* 3 v61 3)) 0.0 (* 3 (- v61))))) (ite (distinct v61 (* 6 (- v61)) (- v6 (- v61))) (* 12 12 v61) (ite (distinct 0.0 (* 3 v61 3)) 0.0 (* 3 (- v61)))))) 0.0))) e6367)))
(check-sat)
(exit)
