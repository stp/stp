; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; The specials matrix with ONE symbolic operand and one literal -- the shape
; the factory strength-reduces, and the only one of the three arrangements
; that reaches it. (Two literals fold before the rule; two symbols have no
; constant to classify against.) Each arm of the reduction is exercised
; against every class of symbolic operand:
;
;   fp.eq(x, NaN literal)  -> false          the NaN arm
;   fp.eq(x, +/-0 literal) -> fp.isZero(x)   the zero arm; must catch BOTH
;                                            zeros whichever zero is written
;   fp.eq(x, c)            -> (= x c)        the arm that lets equalities
;                                            propagate
;
; The three NaN literals differ in payload and sign, so the NaN arm is
; checked against each spelling. The zero rows are the ones that would break
; if the zero arm were ever "simplified" to a plain equality: a -0 literal
; against a +0 variable has to stay true.
;
; The required truth values are conjoined and negated, so any one of them
; going the wrong way makes this satisfiable.
;
; CHECK: ^unsat
(set-logic QF_FP)
(declare-fun pz () (_ FloatingPoint 8 24))
(declare-fun mz () (_ FloatingPoint 8 24))
(declare-fun pi () (_ FloatingPoint 8 24))
(declare-fun mi () (_ FloatingPoint 8 24))
(declare-fun nn () (_ FloatingPoint 8 24))

(assert (and (fp.isZero pz) (fp.isPositive pz)))
(assert (and (fp.isZero mz) (fp.isNegative mz)))
(assert (and (fp.isInfinite pi) (fp.isPositive pi)))
(assert (and (fp.isInfinite mi) (fp.isNegative mi)))
(assert (fp.isNaN nn))

(assert (not (and
  ; --- fp.eq, zero arm: either zero literal matches either zero variable ---
  (fp.eq pz ((_ to_fp 8 24) #x00000000))
  (fp.eq pz ((_ to_fp 8 24) #x80000000))
  (fp.eq mz ((_ to_fp 8 24) #x00000000))
  (fp.eq mz ((_ to_fp 8 24) #x80000000))
  ; --- fp.eq, NaN arm: false for every NaN spelling and every operand ---
  (not (fp.eq nn ((_ to_fp 8 24) #x7FC00000)))
  (not (fp.eq nn ((_ to_fp 8 24) #x7F800001)))
  (not (fp.eq nn ((_ to_fp 8 24) #xFFC12345)))
  (not (fp.eq pz ((_ to_fp 8 24) #x7FC00000)))
  (not (fp.eq pi ((_ to_fp 8 24) #x7F800001)))
  ; --- fp.eq, equality arm: infinities by sign, finite by value ---
  (fp.eq pi ((_ to_fp 8 24) #x7F800000))
  (fp.eq mi ((_ to_fp 8 24) #xFF800000))
  (not (fp.eq pi ((_ to_fp 8 24) #xFF800000)))
  (not (fp.eq mi ((_ to_fp 8 24) #x7F800000)))
  (not (fp.eq pi ((_ to_fp 8 24) #x3F800000)))
  (not (fp.eq pz ((_ to_fp 8 24) #x3F800000)))
  ; --- `=` against the same literals keeps the zeros apart and the NaNs
  ;     together, and must NOT pick up the fp.eq behaviour above ---
  (= pz ((_ to_fp 8 24) #x00000000))
  (not (= pz ((_ to_fp 8 24) #x80000000)))
  (not (= mz ((_ to_fp 8 24) #x00000000)))
  (= mz ((_ to_fp 8 24) #x80000000))
  (= nn ((_ to_fp 8 24) #x7FC00000))
  (= nn ((_ to_fp 8 24) #x7F800001))
  (= nn ((_ to_fp 8 24) #xFFC12345))
  (= pi ((_ to_fp 8 24) #x7F800000))
  (not (= pi ((_ to_fp 8 24) #xFF800000)))
  (not (= pz ((_ to_fp 8 24) #x7FC00000)))
)))
(check-sat)
(exit)
