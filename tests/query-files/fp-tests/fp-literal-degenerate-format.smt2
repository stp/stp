; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; The format implied by an (fp sign exponent significand) literal's component
; widths gets the same floor as the sort form: at least 2 exponent and 2
; significand bits. Regression test: (fp #b0 #b1 #b1) used to be accepted,
; building an eb = 1 format every other entrance rejects.
; CHECK: at least 2 exponent and 2 significand bits
(set-logic QF_FP)
(declare-fun p () Bool)
(assert (= p (fp.isNormal (fp #b0 #b1 #b1))))
(check-sat)
