; Row-derived magnitude-zero facts must reach native FP lowering without
; identifying -0 with +0. The first native run checks the answer, the second
; checks that each specialized consumer actually fires, and the last run is
; the ordinary SymFPU oracle for the same source formula.
;
; RUN: %solver --bb.fp-native-arith=1 --fp-domain-simplify=1 --fp-domain-sound-zero-facts=1 --bb.fp-native-domain=1 -s %s 2>&1 | %OutputCheck --check-prefix=NATIVE %s
; RUN: %solver --bb.fp-native-arith=1 --fp-domain-simplify=1 --fp-domain-sound-zero-facts=1 --bb.fp-native-domain=1 -s %s 2>&1 | %OutputCheck --check-prefix=COUNTERS %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=SYMFPU %s
;
; NATIVE: ^unsat
;
; SYMFPU: ^unsat
;
; COUNTERS: FP native domain zero-magnitude facts: 3
; COUNTERS: FP native domain zero cmp operands: [1-9][0-9]*
; COUNTERS: FP native domain zero classifications: [1-9][0-9]*
; COUNTERS: FP native domain zero add fast-paths: [1-9][0-9]*
; COUNTERS: FP native domain zero mul fast-paths: [1-9][0-9]*
; COUNTERS: FP native domain zero to-fp fast-paths: [1-9][0-9]*
;
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun n () (_ FloatingPoint 8 24))
(declare-fun u () (_ FloatingPoint 8 24))
(declare-fun q () (_ FloatingPoint 8 24))
(declare-fun rm () RoundingMode)

; All three variables are finite and semantically nonnegative; the lower
; bound deliberately still admits -0.
(assert (fp.leq (_ +zero 8 24) x))
(assert (fp.leq x (fp #b0 #x80 #b00000000000000000000000)))
(assert (fp.leq (_ +zero 8 24) y))
(assert (fp.leq y (fp #b0 #x80 #b00000000000000000000000)))
(assert (fp.leq (_ +zero 8 24) n))
(assert (fp.leq n (fp #b0 #x80 #b00000000000000000000000)))
(assert (fp.leq (_ +zero 8 24) u))
(assert (fp.leq u (fp #b0 #x80 #b00000000000000000000000)))

; A same-sign zero row soundly establishes zero magnitude for x and y. The
; sign predicates then choose the two different zero encodings without using
; structural equalities that preprocessing could substitute away.
(assert (fp.eq (fp.add RNE x y) (_ +zero 8 24)))
(assert (fp.eq (fp.add RNE u u) (_ +zero 8 24)))
(assert (fp.isNegative x))
(assert (fp.isPositive y))

; Refute the conjunction of all required zero identities/corner cases. A
; wrong result in any one specialized consumer makes this query satisfiable.
(assert
  (not
    (and
      ; Opposite signed zeros add to -0 only under RTN.
      (= (fp.add RTN x y) (_ -zero 8 24))
      (= (fp.add RNE x y) (_ +zero 8 24))
      (= (fp.add RNA x y) (_ +zero 8 24))
      (= (fp.add RTP x y) (_ +zero 8 24))
      (= (fp.add RTZ x y) (_ +zero 8 24))
      (= (= (fp.add rm x y) (_ -zero 8 24)) (= rm RTN))

      ; Equal-sign zeros keep that sign under every rounding mode.
      (= (fp.add RNE u u) u)
      (= (fp.add RNA u u) u)
      (= (fp.add RTP u u) u)
      (= (fp.add RTN u u) u)
      (= (fp.add RTZ u u) u)

      ; A signed zero is an fp.eq identity for every finite operand,
      ; including subnormals and either signed zero.
      (fp.eq (fp.add RNE x n) n)
      (fp.eq (fp.add RNA n y) n)
      (fp.eq (fp.add RTP x n) n)
      (fp.eq (fp.add RTN n y) n)
      (fp.eq (fp.add RTZ x n) n)
      (= (fp.add RNE x
            (fp #b0 #x00 #b00000000000000000000001))
         (fp #b0 #x00 #b00000000000000000000001))
      (= (fp.add RNE x
            (fp #b0 #xfe #b11111111111111111111111))
         (fp #b0 #xfe #b11111111111111111111111))

      ; Multiplication preserves sign XOR and is exact in every mode.
      (= (fp.mul RNE x (fp #b0 #x80 #b00000000000000000000000))
         (_ -zero 8 24))
      (= (fp.mul RNA x (fp #b1 #x80 #b00000000000000000000000))
         (_ +zero 8 24))
      (= (fp.mul RTP x (fp #b0 #x80 #b00000000000000000000000))
         (_ -zero 8 24))
      (= (fp.mul RTN x (fp #b1 #x80 #b00000000000000000000000))
         (_ +zero 8 24))
      (= (fp.mul RTZ x (fp #b0 #x80 #b00000000000000000000000))
         (_ -zero 8 24))
      (= (fp.mul RNE x (fp #b0 #x00 #b00000000000000000000001))
         (_ -zero 8 24))
      (= (fp.mul RNE x (fp #b0 #xfe #b11111111111111111111111))
         (_ -zero 8 24))

      ; Float-to-float conversion retains the zero sign exactly.
      (= ((_ to_fp 11 53) RTP x) (_ -zero 11 53))
      (= ((_ to_fp 5 11) RTP u) ((_ to_fp 5 11) RTZ u))

      ; Fast paths must not cross their finiteness guard.
      (fp.isNaN (fp.mul RNE x (_ +oo 8 24)))
      (fp.isNaN (fp.mul RNE x (_ NaN 8 24)))
      (fp.isInfinite (fp.add RNE x (_ +oo 8 24)))
      (fp.isNaN (fp.add RNE x (_ NaN 8 24)))

      ; Ordered/fp equality identify signed zeros; SMT equality and sign
      ; classifiers distinguish their encodings.
      (fp.eq x y)
      (not (= x y))
      (fp.leq x y)
      (fp.geq x y)
      (not (fp.lt x y))
      (not (fp.gt x y))
      (fp.isZero x)
      (fp.isZero y)
      (not (fp.isNormal x))
      (not (fp.isSubnormal y))
      (not (fp.isInfinite x))
      (not (fp.isNaN y))

      ; The specialized zero comparator still guards an unconstrained NaN,
      ; and orders either infinity on the correct side of zero.
      (=> (fp.isNaN q)
          (and (not (fp.lt q x))
               (not (fp.leq q x))
               (not (fp.gt q x))
               (not (fp.geq q x))
               (not (fp.lt x q))
               (not (fp.leq x q))
               (not (fp.gt x q))
               (not (fp.geq x q))
               (not (fp.eq x q))))
      (=> (and (fp.isInfinite q) (fp.isPositive q))
          (and (fp.gt q x) (fp.lt x q)))
      (=> (and (fp.isInfinite q) (fp.isNegative q))
          (and (fp.lt q x) (fp.gt x q))))))
(check-sat)
(exit)
