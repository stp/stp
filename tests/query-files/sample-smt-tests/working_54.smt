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

