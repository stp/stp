; RUN: %solver --fp-abstraction=true --fp-abstraction-significand-bits=0 -s %s 2>&1 | %OutputCheck %s
;
; For a product of two normals and a z that is not NaN, one of t < z and
; z <= t holds whatever the product is. The abstraction's first candidate
; picks a surrogate value the exact product is not (the factors are held
; in intervals no identity rule pins, and the significand bands are off,
; so that it never is by chance), but the original formula holds for the
; candidate's x, y and z, which is what the replay finds: the candidate is
; a model and nothing is refined.
; CHECK: 1 inconsistent, 0 shape lemmas, 0 value lemmas, 0 relational lemmas, 0 releases, 0 rounds, 0 restarts, 1 model repairs
; CHECK: ^sat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(assert (fp.lt ((_ to_fp 8 24) RNE 1.1) x))
(assert (fp.lt x ((_ to_fp 8 24) RNE 1.2)))
(assert (fp.lt ((_ to_fp 8 24) RNE 1.3) y))
(assert (fp.lt y ((_ to_fp 8 24) RNE 1.4)))
(assert (not (fp.isNaN z)))
(assert (or (fp.lt (fp.mul RNE x y) z) (fp.leq z (fp.mul RNE x y))))
(check-sat)
