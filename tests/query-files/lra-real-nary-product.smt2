; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; SMT-LIB declares * and / :left-assoc, so (* a b c) abbreviates (* (* a b) c).
; CreateRealTerm takes + and - at any arity but these two only in pairs, and
; the reader handed the whole list over unfolded, so a three-factor product
; was refused as "invalid arithmetic arity" -- a file could not state what the
; C interface, which folds, accepted happily.
;
; Folding left is also what keeps the product inside the linear fragment: the
; two constants meet each other before the symbol does, so every binary node
; has the concrete operand exact linear multiplication asks for.
; CHECK-NEXT: ^sat$
(set-logic QF_LRA)
(declare-fun x () Real)
(assert (= (* 2.0 3.0 x) 30.0))
(assert (= (/ x 5.0 1.0) 1.0))
(check-sat)
(exit)
