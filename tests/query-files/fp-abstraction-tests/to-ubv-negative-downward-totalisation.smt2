; RTN takes (-1,0) outside the unsigned range: the totalisation value can
; have bit 127 set, and equal semantic argument tuples share that value.
; RUN: %solver --incremental=on -d %s | %OutputCheck %s
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true -d %s | %OutputCheck %s
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true --fp-abstraction-ops=all -d %s | %OutputCheck %s
; CHECK: ^sat$
; CHECK: ^unsat$
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 5 11))
(declare-fun y () (_ FloatingPoint 5 11))
(declare-fun rm () RoundingMode)
(declare-fun rn () RoundingMode)
(assert (fp.lt ((_ to_fp 5 11) #xbc00) x))
(assert (fp.lt x (_ -zero 5 11)))
(assert (= rm RTN))
(assert (= rn rm))
(assert (fp.eq x y))
(assert (= ((_ fp.to_ubv 128) rm x) #x80000000000000000000000000000000))
(check-sat)
(push 1)
(assert (distinct ((_ fp.to_ubv 128) rm x) ((_ fp.to_ubv 128) rn y)))
(check-sat)
(pop 1)
