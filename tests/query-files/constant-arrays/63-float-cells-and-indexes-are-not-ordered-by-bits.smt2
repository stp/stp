; RUN: %solver %s | %OutputCheck %s
; The canonical form compares and orders constants by their bits, which is
; only the comparison of values for bit-vectors and Booleans. Two NaNs with
; different bits are one float: two arrays that differ only in which NaN a
; cell holds are equal, and two stores at different NaN indexes are at one
; index, where reordering them would change which one wins.
(set-logic QF_ABVFP)
(push 1)
(assert (not (= (store ((as const (Array (_ BitVec 2) (_ FloatingPoint 5 11))) (_ +zero 5 11)) #b01 (fp #b0 #b11111 #b1000000000))
                (store ((as const (Array (_ BitVec 2) (_ FloatingPoint 5 11))) (_ +zero 5 11)) #b01 (fp #b0 #b11111 #b0000000001)))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; The zeros are two values.
(push 1)
(assert (not (= (store ((as const (Array (_ BitVec 2) (_ FloatingPoint 5 11))) (_ +zero 5 11)) #b01 (_ -zero 5 11))
                ((as const (Array (_ BitVec 2) (_ FloatingPoint 5 11))) (_ +zero 5 11)))))
; CHECK: ^sat$
(check-sat)
(pop 1)
; The later of two stores at NaN indexes wins.
(push 1)
(assert (not (= (select (store (store ((as const (Array (_ FloatingPoint 5 11) (_ BitVec 8))) #x00)
                                      (fp #b0 #b11111 #b0000000001) #x01)
                               (fp #b0 #b11111 #b1000000000) #x02)
                        (fp #b0 #b11111 #b0000000001))
                #x02)))
; CHECK: ^unsat$
(check-sat)
(pop 1)
