; The native divide circuit's special cases, with every operand pinned by
; classification so it stays symbolic and reaches the circuit rather than
; folding at the factory. Asserting the negation of the expected IEEE
; results makes a disagreement the only model.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-div=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: FloatBlast: 0 SymFPU operations, 0 unpacks, 0 packs, 0 direct add-isZero predicates (no-op: everything passed through natively)
; CHECK: ^unsat
;
(set-logic QF_FP)
(declare-fun pz () (_ FloatingPoint 3 4))
(declare-fun nz () (_ FloatingPoint 3 4))
(declare-fun pinf () (_ FloatingPoint 3 4))
(declare-fun ninf () (_ FloatingPoint 3 4))
(declare-fun nan () (_ FloatingPoint 3 4))
(declare-fun x () (_ FloatingPoint 3 4))

(assert (and (fp.isZero pz) (fp.isPositive pz)))
(assert (and (fp.isZero nz) (fp.isNegative nz)))
(assert (and (fp.isInfinite pinf) (fp.isPositive pinf)))
(assert (and (fp.isInfinite ninf) (fp.isNegative ninf)))
(assert (fp.isNaN nan))
(assert (and (fp.isNormal x) (fp.isPositive x)))

(assert
  (or
    ; zero over zero and infinity over infinity are invalid
    (not (fp.isNaN (fp.div RNE pz nz)))
    (not (fp.isNaN (fp.div RNE pinf ninf)))
    ; a NaN operand propagates
    (not (fp.isNaN (fp.div RNE nan x)))
    (not (fp.isNaN (fp.div RNE x nan)))
    ; division by zero is a signed infinity
    (not (fp.isInfinite (fp.div RNE x pz)))
    (not (fp.isPositive (fp.div RNE x pz)))
    (not (fp.isNegative (fp.div RNE x nz)))
    ; an infinite divisor gives a signed zero
    (not (fp.isZero (fp.div RNE x pinf)))
    (not (fp.isPositive (fp.div RNE x pinf)))
    (not (fp.isNegative (fp.div RNE x ninf)))
    ; an infinite dividend stays infinite
    (not (fp.isInfinite (fp.div RNE pinf x)))
    (not (fp.isNegative (fp.div RNE ninf x)))
    ; a zero dividend stays a signed zero
    (not (fp.isZero (fp.div RNE pz x)))
    (not (fp.isNegative (fp.div RNE nz x)))))
(check-sat)
(exit)
