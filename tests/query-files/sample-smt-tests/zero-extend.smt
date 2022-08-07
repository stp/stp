; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat

(benchmark smt
 :status unsat
  :logic QF_BV

  :extrafuns ((x BitVec[2]))
  :formula (not (iff (bvlt (zero_extend[1] x) bv2[3]) (bvlt x bv2[2])))
)
