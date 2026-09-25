; Small negative values convert to defined unsigned zero in these modes.
; Exercise a symbolic mode and a target wider than a host integer.
; RUN: %solver -d %s | %OutputCheck %s
; RUN: %solver --fp-abstraction=true -d %s | %OutputCheck %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=all -d %s | %OutputCheck %s
; CHECK: ^unsat$
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 5 11))
(declare-fun rm () RoundingMode)
(assert (fp.lt ((_ to_fp 5 11) #xb800) x))
(assert (fp.lt x (_ -zero 5 11)))
(assert (or (= rm RTZ) (= rm RTP) (= rm RNE) (= rm RNA)))
(assert (distinct ((_ fp.to_ubv 128) rm x) (_ bv0 128)))
(check-sat)
