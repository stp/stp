; RUN: %solver -d %s | %OutputCheck %s
;
; A division by an unconstrained float64 divisor, narrowed back to float32,
; reaches every float32 value, so RemoveUnconstrained replaces the whole
; quotient with a fresh variable (filtered through the numerator's
; classification) and never builds the divider circuit. The pinned numerator
; and pinned quotient collapse the rest at the word level.
;
; -d additionally constructs the model and checks it against this input,
; which exercises the witness divisor recorded for the eliminated u: the
; check evaluates the original division at u's reconstructed value.
;
; CHECK: ^sat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun u () (_ FloatingPoint 11 53))
(assert (= x ((_ to_fp 8 24) #x3f800000)))
(assert (= ((_ to_fp 8 24) RNE (fp.div RNE ((_ to_fp 11 53) RNE x) u)) ((_ to_fp 8 24) #x40400000)))
(check-sat)
(exit)
