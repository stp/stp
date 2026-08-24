; A binary-format addition can round to zero only when its finite operands
; have an exact real sum of zero. Exhaust the small (3,4) format and all five
; rounding modes by asking for a disagreement with that packed-value law.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-arith=1 -s %s 2>&1 | %OutputCheck --check-prefix=FUSED %s
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-arith=1 --bb.fp-native-add-iszero=0 %s | %OutputCheck --check-prefix=RESULT %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=RESULT %s
;
; FUSED: FP native add-isZero fused predicates: 1
; FUSED: ^unsat
; RESULT: ^unsat
;
(set-logic QF_FP)
(declare-fun rm () RoundingMode)
(declare-fun a () (_ FloatingPoint 3 4))
(declare-fun b () (_ FloatingPoint 3 4))

(define-fun finite ((x (_ FloatingPoint 3 4))) Bool
  (and (not (fp.isNaN x)) (not (fp.isInfinite x))))

(define-fun exact-zero-sum ((x (_ FloatingPoint 3 4))
                            (y (_ FloatingPoint 3 4))) Bool
  (and (finite x) (finite y)
       (or (and (fp.isZero x) (fp.isZero y))
           (and (not (fp.isZero x)) (not (fp.isZero y))
                (not (= (fp.isNegative x) (fp.isNegative y)))
                (fp.eq (fp.abs x) (fp.abs y))))))

(assert (not (= (fp.isZero (fp.add rm a b))
                (exact-zero-sum a b))))
(check-sat)
(exit)
