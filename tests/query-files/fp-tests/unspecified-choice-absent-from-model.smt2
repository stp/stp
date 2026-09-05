; RUN: %solver %s | %OutputCheck %s
;
; fp.min/fp.max get their unspecified result from four free bits selected on
; the operands' sign bits, not from an array read. That is a different shape
; from the conversions' array (see unspecified-array-absent-from-model.smt2)
; and so a different route through the introduced-symbol filter: the cells are
; a plain scalar symbol, whose counterexample entry is keyed on the symbol
; itself rather than on a READ over it.
;
; Either way it is not the user's, and (get-model) must not answer with a
; symbol never declared, in a sort the input's signature does not contain.
; CHECK: ^sat
; CHECK-NOT-L: @fp_unspecified
; CHECK-L: (define-fun |x| () (_ FloatingPoint 8 24)
; CHECK-NOT-L: @fp_unspecified
(set-logic QF_FP)
(set-option :produce-models true)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNegative (fp.min (_ +zero 8 24) (_ -zero 8 24))))
(assert (fp.isPositive (fp.max (_ +zero 8 24) (_ -zero 8 24))))
(assert (fp.isNaN x))
(check-sat)
(get-model)
