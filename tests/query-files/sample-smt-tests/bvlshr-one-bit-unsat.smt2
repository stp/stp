; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
;
; An off-by-one in bvlshr made this satisfiable (#54): at one bit, a nonzero
; shift amount clears the operand, so sym3 = sym1 >> sym2 and
; sym1 = sym3 >> sym2 force sym1 to zero. Converted from the SMT-LIB 1
; working_54.smt, which carried it as assumptions with no formula.
(set-logic QF_BV)
(set-info :status unsat)
(declare-fun sym1 () (_ BitVec 1))
(declare-fun sym2 () (_ BitVec 1))
(declare-fun sym3 () (_ BitVec 1))
(assert (= (bvlshr sym1 sym2) sym3))
(assert (= (bvlshr sym3 sym2) sym1))
(assert (not (= sym2 #b0)))
(assert (not (= sym1 #b0)))
(check-sat)
(exit)
