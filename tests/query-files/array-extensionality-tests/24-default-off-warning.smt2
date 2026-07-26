; RUN: %solver %s 2>&1 | %OutputCheck %s
; CHECK-L: Warning: Parsing a term that uses array extensionality. STP doesn't handle array extensionality (unless --array-equality is given).
; CHECK-NEXT-L: sat
; Without --array-equality an array equality still parses to a plain
; EQ node, and the full warning line -- which now names the option --
; is printed exactly once however many equalities the file contains:
; the CHECK-NEXT above proves the second assert (the operand-swapped
; equality) did not warn again. Both equalities sit under a true
; disjunct, so the verdict never depends on how the legacy path would
; treat a surviving array equality.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun x () (_ BitVec 2))
(assert (or true (= a b)))
(assert (or true (= b a)))
(assert (= x #b01))
(check-sat)
