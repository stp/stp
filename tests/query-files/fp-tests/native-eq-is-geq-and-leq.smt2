; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; For ordered (non-NaN) operands, fp.eq is exactly fp.geq-and-fp.leq, so
; this formula is unsatisfiable. All three predicates are now bit-blasted
; natively, which makes this an internal-consistency check: the equality's
; both-zero disjunct and the orderings' both-zero correction have to agree
; on the (+0, -0) pair, the only place where equal values have different
; packed bits. The flag-off run proves the identity all-SymFPU.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isNaN y)))
(assert (xor (fp.eq x y) (and (fp.geq x y) (fp.leq x y))))
(check-sat)
(exit)
