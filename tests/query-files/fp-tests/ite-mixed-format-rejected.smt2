; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; An if-then-else whose branches are floats of different formats is
; ill-sorted, even though the formats can share one packed width:
; (_ FloatingPoint 8 24) and (_ FloatingPoint 24 8) are both 32 bits, so the
; width checks cannot tell them apart. Regression test: this used to parse
; and solve, deriving the then branch's format and silently reading the else
; branch's bits at it -- while = over the same pair was rejected.
;
; The condition is deliberately a constant: the factory folds such an
; if-then-else to one branch as the term is built, so only the parser's
; up-front check (not the type check on the built node) can see the pair.
; CHECK: ite branches must have the same sort
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 24 8))
(assert (fp.isNaN (ite true x y)))
(check-sat)
