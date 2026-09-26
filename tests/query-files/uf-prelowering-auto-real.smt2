; RUN: %solver --SMTLIB2 -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 -s --uf-propagate-equalities=on %s 2>&1 | %OutputCheck --check-prefix=FORCED %s
; RUN: %solver --SMTLIB2 --uf-propagate-equalities=off %s | %OutputCheck --check-prefix=ANSWER %s
;
; What AUTO decides for a Real query, and that naming the option still
; overrides the choice.
;
; The pre-lowering pass pushes top-level equalities through applications
; before lowering hides their arguments. It was written for and measured on
; QF_UFBV, where it is a large win. On the Real path it is a consistent loss
; -- across the QF_UFLRA families it costs between a third and a half of the
; runtime of the files slow enough to measure, and solves fewer of them --
; because those queries reach their answer through refinement rounds that
; the rewriting does not shorten. So AUTO, the default, declines it here.
;
; The pass announces itself under -s, which is what these lines read. The
; bit-vector half of the same decision is in uf-prelowering-auto-bv.smt2,
; where AUTO must still run it.
;
; x = 3.0 would send (f x) to (f 3.0) if the pass ran, so this query gives
; it something to do rather than testing a pass that would no-op anyway.
;
; CHECK-NOT: UF: pre-lowering
; FORCED: UF: pre-lowering
; ANSWER: ^sat$
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x 3.0))
(assert (> (f x) (f y)))
(assert (< y 3.0))
(check-sat)
(exit)
