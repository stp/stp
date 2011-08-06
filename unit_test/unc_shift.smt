(benchmark r
  :status sat
  :category { crafted }
  :difficulty { 0 }
  :logic QF_BV
  :extrafuns ((x BitVec[3]))
  :extrafuns ((y BitVec[3]))
  
  :extrafuns ((w BitVec[3]))
  :extrafuns ((z BitVec[3]))

  :extrafuns ((q BitVec[3]))
  :extrafuns ((r BitVec[3]))

  :assumption (= (bvshl x y )  (bv4[3]))
  :assumption (= (bvashr w z )  (bv4[3]))
  :assumption (= (bvshl q r )  (bv4[3]))


    :formula true
)
