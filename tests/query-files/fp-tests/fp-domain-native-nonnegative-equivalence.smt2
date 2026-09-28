; Exhaustive small-format equivalence checks for the specialized known-sign
; datapaths. FMA is deliberately left on the ordinary SymFPU path and serves
; as the oracle: a*1+b is fp.add with one rounding, while a*b+0 is fp.mul for
; nonzero finite operands. Both semantic sign directions and all five IEEE
; rounding modes are covered. The (3,5) format is small enough to prove this
; exhaustively, including both packed encodings of zero in the additions.
;
; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-arith=1 --fp-domain-simplify=1 --bb.fp-native-domain=1 --bb.fp-native-known-sign=1 -s %s 2>&1 | %OutputCheck --check-prefix=NATIVE %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=SYMFPU %s
; NATIVE: FP native domain known-positive add paths: [1-9][0-9]*
; NATIVE: FP native domain known-negative add paths: [1-9][0-9]*
; NATIVE: FP native domain known-positive mul paths: [1-9][0-9]*
; NATIVE: FP native domain known-negative mul paths: [1-9][0-9]*
; NATIVE: ^unsat
; SYMFPU: ^unsat
;
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 3 5))
(declare-fun b () (_ FloatingPoint 3 5))
(declare-fun m () (_ FloatingPoint 3 5))
(declare-fun n () (_ FloatingPoint 3 5))
(declare-fun c () (_ FloatingPoint 3 5))
(declare-fun d () (_ FloatingPoint 3 5))
(declare-fun p () (_ FloatingPoint 3 5))
(declare-fun q () (_ FloatingPoint 3 5))
(declare-fun nativeAdd () (_ FloatingPoint 3 5))
(declare-fun oracleAdd () (_ FloatingPoint 3 5))
(declare-fun nativeNegativeAdd () (_ FloatingPoint 3 5))
(declare-fun oracleNegativeAdd () (_ FloatingPoint 3 5))
(declare-fun nativeMul () (_ FloatingPoint 3 5))
(declare-fun oracleMul () (_ FloatingPoint 3 5))
(declare-fun nativeNegativeMul () (_ FloatingPoint 3 5))
(declare-fun oracleNegativeMul () (_ FloatingPoint 3 5))
(declare-fun rm () RoundingMode)

(define-fun one () (_ FloatingPoint 3 5) (fp #b0 #b011 #b0000))
(define-fun minSub () (_ FloatingPoint 3 5) (fp #b0 #b000 #b0001))
(define-fun maxFinite () (_ FloatingPoint 3 5) (fp #b0 #b110 #b1111))
(define-fun minusMinSub () (_ FloatingPoint 3 5) (fp #b1 #b000 #b0001))
(define-fun minusMaxFinite () (_ FloatingPoint 3 5) (fp #b1 #b110 #b1111))

(assert (and
  (fp.leq (_ +zero 3 5) a) (fp.leq a maxFinite)
  (fp.leq (_ +zero 3 5) b) (fp.leq b maxFinite)
  (fp.leq minSub m) (fp.leq m maxFinite)
  (fp.leq minSub n) (fp.leq n maxFinite)
  (fp.leq minusMaxFinite c) (fp.leq c (_ -zero 3 5))
  (fp.leq minusMaxFinite d) (fp.leq d (_ -zero 3 5))
  (fp.leq minusMaxFinite p) (fp.leq p minusMinSub)
  (fp.leq minSub q) (fp.leq q maxFinite)))

; Each native result is named through a packed equality. The corresponding
; FMA equation forces an ordinary SymFPU result, after which a packed mismatch
; would witness a circuit error (including a wrong zero sign).
(assert (= nativeAdd (fp.add rm a b)))
(assert (= oracleAdd (fp.fma rm a one b)))
(assert (= nativeNegativeAdd (fp.add rm c d)))
(assert (= oracleNegativeAdd (fp.fma rm c one d)))
(assert (= nativeMul (fp.mul rm m n)))
(assert (= oracleMul (fp.fma rm m n (_ +zero 3 5))))
(assert (= nativeNegativeMul (fp.mul rm p q)))
(assert (= oracleNegativeMul (fp.fma rm p q (_ +zero 3 5))))
(assert (or (not (= nativeAdd oracleAdd))
            (not (= nativeNegativeAdd oracleNegativeAdd))
            (not (= nativeMul oracleMul))
            (not (= nativeNegativeMul oracleNegativeMul))))
(check-sat)
(exit)
