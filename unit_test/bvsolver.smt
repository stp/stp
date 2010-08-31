(benchmark r
  :status sat
  :category { crafted }
  :difficulty { 0 }
  :logic QF_BV
  :extrafuns ((x BitVec[3]))
  :extrafuns ((y BitVec[3]))
  :extrafuns ((z BitVec[3]))

  :assumption (= (bvadd (bvadd (bvmul bv3[3] x) (bvmul bv4[3] y)) (bvmul bv2[3] z)) bv0[3])
  :assumption (= (bvadd (bvadd (bvmul bv2[3] x) (bvmul bv2[3] y)) (bvmul bv0[3] z)) bv6[3])
  :assumption (= (bvadd (bvadd (bvmul bv2[3] x) (bvmul bv4[3] y)) (bvmul bv2[3] z)) bv0[3])

  :formula true
)
