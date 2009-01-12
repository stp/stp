(
benchmark temp20.smt
:source {Minkeyrink Solver}
:status unsat
:difficulty {1}
:category {industrial}
:logic QF_BV
:extrafuns ((sym1 BitVec[4]))
:extrafuns ((sym2 BitVec[1]))
:extrafuns ((sym3 BitVec[4]))

:assumption (= (bvlshr sym1 (zero_extend[3] sym2)) sym3)
:assumption (= (bvlshr sym3(zero_extend[3] sym2)) sym1)
:assumption (not (= sym2 bv0[1]))
:assumption (not (= sym1 bv0[4]))

)

