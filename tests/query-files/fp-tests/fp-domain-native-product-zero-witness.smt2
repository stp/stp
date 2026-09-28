; RUN: %solver --disable-equality --unconstrained-variable-elimination=0 --bb.fp-native-arith=1 --bb.fp-native-domain=1 --bb.fp-native-known-sign=1 -s %s 2>&1 | %OutputCheck --check-prefix=NATIVE %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=SYMFPU %s
;
; NATIVE: FP native domain zero-magnitude facts: 1
; NATIVE: ^unsat
; SYMFPU: ^unsat
;
; A product's own isZero assertion is useful as a fact for consumers, but it
; must remain a live witness that checks the computed magnitude. Treating the
; fact as permission to replace its producer by zero would make this formula
; spuriously satisfiable.
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 3 5))

(define-fun one () (_ FloatingPoint 3 5)
  (fp #b0 #b011 #b0000))
(define-fun two () (_ FloatingPoint 3 5)
  (fp #b0 #b100 #b0000))

(assert (and (fp.leq one x) (fp.leq x one)))
(assert (fp.isZero (fp.mul RNE two x)))
(check-sat)
(exit)
