; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
;
; The UF pre-lowering pass propagates a top-level equality through the
; applications below it, rebuilding the nodes it rewrites through the node
; factory rather than through the frontend. Substituting the literal for x
; leaves (* 4.0 3.0): a product whose operands are now both concrete.
;
; The frontend folds such a product, but HashingNodeFactory demanded
; *exactly* one concrete operand and called FatalError on anything else, so
; the rebuilt node aborted the process instead of becoming the constant 12.
; Every QF_UFLRA file in the cpachecker-bmc family reached this, and lost
; its answer to a fatal error rather than to a timeout.
;
; Both operands concrete is a constant; neither is the nonlinear case, and
; that one is still refused -- see lra-real-nonlinear-refused.smt2.
;
; CHECK-NEXT: ^sat$
(set-logic QF_UFLRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x 3.0))
(assert (= (f y) (* 4.0 x)))
(assert (> (f y) 0.0))
(check-sat)
(exit)
