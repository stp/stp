; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; The smallest subnormal of (_ FloatingPoint 3 4) is 2^(1 - 3 - 3) = 1/32,
; and the largest subnormal 7/32.
(set-logic QF_FPLRA)
(assert (or (not (= (fp.to_real (fp #b0 #b000 #b001)) (/ 1 32)))
            (not (= (fp.to_real (fp #b1 #b000 #b111)) (- (/ 7 32))))))
(check-sat)
