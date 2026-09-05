; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; distinct over arrays whose store value applies fp.max to a read of
; the other operand: simplifying the recovered array term used to
; drive the un-totalised fp.max into the float blaster and crash (a
; segfault without assertions, an assertion failure with them).
(set-logic QF_ABVFP)
(declare-fun x3 () (Array (_ BitVec 11) (_ FloatingPoint 11 53)))
(declare-fun x () (Array (_ BitVec 11) (_ FloatingPoint 11 53)))
(assert (distinct x3 (store x (_ bv0 11)
                       (fp.max (select x3 (_ bv0 11))
                               (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))))))
(check-sat)
