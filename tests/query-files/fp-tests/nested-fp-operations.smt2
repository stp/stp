; RUN: %solver %s | %OutputCheck %s
;
; Floating-point operations nested several levels deep must simplify and
; answer correctly. Regression test: rebuilds inside the simplifier's
; child-simplification loop used to drop the per-node format, so anything
; deeper than one operation either overflowed the stack or answered unsat
; on satisfiable input (fixed in fbb96cd8; failed from depth 3).
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (fp.isZero x))
(assert (fp.isZero y))
; Depth 4: eq(add(add(mul(x,x), sub(y,y)), sub(x,y)), mul(x,y)) -- with both
; variables zero every level folds to a zero, and fp.eq ignores its sign.
(assert (fp.eq
          (fp.add RNE
                  (fp.add RNE (fp.mul RNE x x) (fp.sub RNE y y))
                  (fp.sub RNE x y))
          (fp.mul RNE x y)))
; CHECK: ^sat
(check-sat)
