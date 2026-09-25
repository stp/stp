; An abstracted fp.to_sbv is decided by its exponent-band rules alone: x
; lies in [4, 7.9], so the signed conversion truncates into [4, 8], and a
; result above 16 is impossible without ever building the conversion's
; circuit. The same answer with the operation exact, and with the record
; hosted by the incremental driver.
;
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --fp-abstraction=true --fp-abstraction-ops=default,to_sbv,to_ubv -d %s | %OutputCheck %s
; CHECK: ^unsat$
(set-logic QF_BVFP)
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.geq x ((_ to_fp 8 24) #x40800000)))
(assert (fp.leq x ((_ to_fp 8 24) #x40FCCCCD)))
(assert (bvsgt ((_ fp.to_sbv 32) roundTowardZero x) (_ bv16 32)))
(check-sat)
(exit)
