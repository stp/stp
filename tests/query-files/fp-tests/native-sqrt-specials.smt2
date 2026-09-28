; The native square root's special cases, every operand pinned by
; classification so it stays symbolic. Negative operands other than minus
; zero are invalid; minus zero returns itself.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-sqrt=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun pz () (_ FloatingPoint 3 4))
(declare-fun nz () (_ FloatingPoint 3 4))
(declare-fun pinf () (_ FloatingPoint 3 4))
(declare-fun ninf () (_ FloatingPoint 3 4))
(declare-fun nan () (_ FloatingPoint 3 4))
(declare-fun neg () (_ FloatingPoint 3 4))

(assert (and (fp.isZero pz) (fp.isPositive pz)))
(assert (and (fp.isZero nz) (fp.isNegative nz)))
(assert (and (fp.isInfinite pinf) (fp.isPositive pinf)))
(assert (and (fp.isInfinite ninf) (fp.isNegative ninf)))
(assert (fp.isNaN nan))
(assert (and (fp.isNormal neg) (fp.isNegative neg)))

(assert
  (or
    (not (and (fp.isZero (fp.sqrt RNE pz)) (fp.isPositive (fp.sqrt RNE pz))))
    (not (and (fp.isZero (fp.sqrt RNE nz)) (fp.isNegative (fp.sqrt RNE nz))))
    (not (fp.isInfinite (fp.sqrt RNE pinf)))
    (not (fp.isPositive (fp.sqrt RNE pinf)))
    (not (fp.isNaN (fp.sqrt RNE ninf)))
    (not (fp.isNaN (fp.sqrt RNE nan)))
    (not (fp.isNaN (fp.sqrt RNE neg)))))
(check-sat)
(exit)
