; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; A Boolean-valued application over Real arguments. The application is one
; opaque atom to the arithmetic while its arguments stay Real terms, so both
; halves have to agree about which of them anything downstream may value.
(set-logic QF_UFLRA)
(declare-fun q (Real) Bool)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (q x))
(assert (not (q y)))
; CHECK: ^unsat
(check-sat)
