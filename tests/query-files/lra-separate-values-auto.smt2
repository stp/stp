; RUN: %solver --SMTLIB2 --lra-separate-model-values=auto %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --lra-separate-model-values=on %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 --lra-separate-model-values=off %s | %OutputCheck %s
;
; What AUTO decides for --lra-separate-model-values, and that the answer does
; not depend on it.
;
; The pass moves variables inside the slack their asserted bounds leave so
; that fewer of them hold the same value by accident. It only pays where
; something reads the model by grouping values, and the lazy congruence
; round is the only such reader: it groups applications by the model values
; of their arguments, so a coincidence there manufactures a pair to
; constrain for a query that never asked those arguments to be equal.
;
; AUTO therefore asks whether the query has any such reader, which the
; coordinator already knows as its spread symbols -- the arguments of
; uninterpreted applications. This query has one, so AUTO runs the pass; the
; QF_LRA companion has none, so it does not.
;
; Measured over the non-incremental benchmarks, three-run medians: with a
; reader present the pass is worth two solves and 11.8% of PAR2; without one
; it gains nothing, costs two files and half a percent. A flat default
; either way takes one of those, which is why this is three-valued.
;
; What must hold in every mode is the verdict. Separation produces a
; different model of the same asserted bounds, never a different answer.
;
; CHECK: ^sat$
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (>= a 0.0))
(assert (<= a 10.0))
(assert (>= b 0.0))
(assert (<= b 10.0))
(assert (> (f a) (f b)))
(check-sat)
(exit)
