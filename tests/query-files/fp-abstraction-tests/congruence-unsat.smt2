; RUN: %solver --fp-abstraction=true -s %s 2>&1 | %OutputCheck %s
;
; Two products over factors the formula makes equal -- fp.eq of two
; normals is bit equality, but it is not the syntactic sharing the records
; merge on -- and a claim that the products differ. The first candidate
; gives the two surrogates different values for equal operands, which is
; the congruence fact between the two records; asserted, the claim is
; unsat with nothing released.
; CHECK: 1 relational lemmas, 0 releases
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x1 (_ FloatingPoint 11 53))
(declare-const x2 (_ FloatingPoint 11 53))
(declare-const y (_ FloatingPoint 11 53))
(assert (fp.isNormal x1))
(assert (fp.isNormal y))
(assert (fp.eq x1 x2))
(assert (not (= (fp.mul RNE x1 y) (fp.mul RNE y x2))))
(check-sat)
