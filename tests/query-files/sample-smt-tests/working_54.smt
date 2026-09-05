; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
;
; One of the two SMT-LIB1 files kept after the rest of the format was
; converted to SMT-LIB2. Between them they are all that still drives the
; SMT-LIB1 parser end to end, and the .smt extension that selects it, so they
; were chosen for coverage rather than history: this one is unsatisfiable and
; carries no :formula at all, only assumptions, while working_55.smt is
; satisfiable and ends with :formula true. See also working_55.smt.
(
benchmark temp20.smt
:source {Minkeyrink Solver}
:status unsat
:difficulty {1}
:category {crafted}
:logic QF_BV
:extrafuns ((sym1 BitVec[1]))
:extrafuns ((sym2 BitVec[1]))
:extrafuns ((sym3 BitVec[1]))


; Off-by-one in the bvlshr was causing the problem. Fixed in #54

:assumption (= (bvlshr sym1 sym2) sym3)
:assumption (= (bvlshr sym3 sym2) sym1)
:assumption (not (= sym2 bv0[1]))
:assumption (not (= sym1 bv0[1]))


)

