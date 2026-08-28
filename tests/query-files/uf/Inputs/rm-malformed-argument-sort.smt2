(set-logic QF_UFBVFP)
(declare-fun f (RoundingMode) (_ BitVec 4))
(assert (= (f #x0) #x2))
(check-sat)
