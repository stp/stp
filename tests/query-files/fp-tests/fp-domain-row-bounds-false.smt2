; RUN: %solver --fp-domain-row-bounds=1 -s %s 2>&1 | %OutputCheck %s
; CHECK: row-bound-rows, 1 row-bound-false
; CHECK: unsat
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (and (fp.leq (_ +zero 8 24) x)
             (fp.leq x (fp #b0 #b10000000 #b00000000000000000000000))))
(assert (fp.eq (fp.add RNE x
                       (fp #b1 #b10000001 #b00000000000000000000000))
               (_ +zero 8 24)))
(check-sat)
