; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
(benchmark smt
  :status unsat
  :logic QF_BV

  :extrafuns ((x BitVec[2]))
  :formula (not (iff (bvslt (sign_extend[1] x) bv0[3]) (bvslt x bv0[2])))
)

