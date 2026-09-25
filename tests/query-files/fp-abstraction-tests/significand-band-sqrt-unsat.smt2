; RUN: %solver --fp-abstraction=true -s %s 2>&1 | %OutputCheck %s
;
; The root of x in [2, 2.2] is at least 1.414, and the claim puts it below
; 1.38: within the binade the exponent bands allow, so it is the
; significand band -- the squares of the result's top bits against x --
; that decides it, with no candidate checked and no root built.
; CHECK: 0 checks, .* 0 releases
; CHECK: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 11 53))
(assert (fp.leq ((_ to_fp 11 53) RNE 2.0) x))
(assert (fp.leq x ((_ to_fp 11 53) RNE 2.2)))
(assert (fp.lt (fp.sqrt RNE x) ((_ to_fp 11 53) RNE 1.38)))
(check-sat)
