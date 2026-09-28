; --fp-abstraction-decline-pinned leaves exact an operation whose result
; the query equates directly with a constant: the product below is the
; witness-hunt signature, so it is lowered exactly while the flag is on,
; and the answer agrees with the default abstraction either way.
;
; RUN: %solver --fp-abstraction=true %s | %OutputCheck %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-decline-pinned %s | %OutputCheck %s
; CHECK: ^sat$
(set-logic QF_FP)
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert (= (fp.mul RNE a b) ((_ to_fp 8 24) #x40490fdb)))
(assert (fp.gt a ((_ to_fp 8 24) #x3f800000)))
(check-sat)
(exit)
