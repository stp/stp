; RUN: %solver --pure-literals=1 --exit-after-CNF %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(benchmark r
  :status sat
  :category { crafted }
  :difficulty { 0 }
  :logic QF_BV
  :extrafuns ((x BitVec[3]))
  :extrafuns ((y BitVec[3]))
  
  :extrafuns ((m BitVec[3]))
  :extrafuns ((p BitVec[3]))

  :assumption (or (bvslt x y ) (or (= (bvmul p m) bv3[3]) (= (bvadd p m) bv3[3])))
    :formula true
)
