; The control for native-sqrt-shares-one-relation-per-operand: two roots of
; two distinct operands are two relations, and sharing them would be
; unsound. The operands are asserted equal, which is as close as two terms
; get without being one, so the equality substitution is turned off to keep
; them distinct at the blaster.
;
; RUN: %solver --disable-equality --bb.fp-native-sqrt=true -s %s 2>&1 | %OutputCheck %s
;
; CHECK: fp-native: relational encodings minted: 2
; CHECK: fp-native: square roots sharing an earlier relation: 0
; CHECK: ^unsat
;
(set-logic QF_FP)
(define-sort FPN () (_ FloatingPoint 5 7))
(declare-fun x () FPN)
(declare-fun y () FPN)
(assert (= x y))
(assert (not (= (fp.sqrt RNE x) (fp.sqrt RNE y))))
(check-sat)
(exit)
