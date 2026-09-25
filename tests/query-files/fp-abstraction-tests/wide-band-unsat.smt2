; RUN: %solver --fp-abstraction=true -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-significand-bits-wide=0 -s %s 2>&1 | %OutputCheck --check-prefix=NARROW %s
;
; Two binary128 factors held within 2^-12 of one, and the claim that their
; product reaches 1.001. The significand bands bound the product through a
; k x k multiplier over the operands' top k bits: at the 16 bits the wide
; format gets by default the band caps the product below 1.0003 and the
; claim is refuted on the rules alone, with no candidate checked; at the
; 8 bits of the narrow setting the band only says below 1.016, and the
; query has to refine its way to the same answer through value lemmas and a
; release.
; CHECK: FpAbstraction: 1 abstracted .* 0 checks
; CHECK: ^unsat
; NARROW: FpAbstraction: 1 abstracted .* 1 releases
; NARROW: ^unsat
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 15 113))
(declare-const y (_ FloatingPoint 15 113))
(assert (fp.leq ((_ to_fp 15 113) RNE 1.0) x))
(assert (fp.leq x ((_ to_fp 15 113) RNE 1.000244140625)))
(assert (fp.leq ((_ to_fp 15 113) RNE 1.0) y))
(assert (fp.leq y ((_ to_fp 15 113) RNE 1.000244140625)))
(assert (fp.geq (fp.mul RNE x y) ((_ to_fp 15 113) RNE 1.001)))
(check-sat)
