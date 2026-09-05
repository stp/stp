; RUN: %solver %s | %OutputCheck %s
;
; An fp comparison whose operand is a compound term must keep its operand
; order. Regression test: SimplifyFormula sorts children before dispatching,
; and fp.lt/leq/gt/geq were missing from the do-not-sort list -- so
; (fp.gt (fp.add x x) 1.0) silently inverted once the left operand was a
; compound node (fixed in fbb96cd8: correct on (x > 1), wrong on (x+x > 1)).
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
; 0x3F800000 is 1.0f.
(assert (fp.gt (fp.add RNE x x) ((_ to_fp 8 24) #x3F800000)))
(assert (fp.lt x ((_ to_fp 8 24) #x3F800000)))
; Satisfiable: x = 0.75 gives x + x = 1.5 > 1.0 with x < 1.0. An inverted
; fp.gt makes the two asserts contradictory for every x.
; CHECK: ^sat
(check-sat)
