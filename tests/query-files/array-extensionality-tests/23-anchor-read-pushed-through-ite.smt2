; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Reduced from an industrial benchmark. The equality's operand is an
; array if-then-else, and the assertion folds to true at parse time,
; so only the record's witness bundle keeps the formula alive; the
; simplifier then pushes the witness read through the if-then-else,
; and operand recovery must accept that pushed anchor shape.
(declare-const __ (_ BitVec 16))
(declare-const x Bool)
(declare-fun p () (Array (_ BitVec 5) (_ BitVec 32)))
(assert (let ((_def_14 (= p (ite x p (store p ((_ extract 6 2) (bvadd (_ bv1 32) ((_ zero_extend 16) __))) (_ bv0 32)))))) true))
(check-sat)
