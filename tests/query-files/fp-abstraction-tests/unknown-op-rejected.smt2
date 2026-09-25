; RUN: not %solver --fp-abstraction=true --fp-abstraction-ops=mul,nope %s 2>&1 | %OutputCheck %s
;
; An operation list the abstraction does not know is refused up front, not
; ignored.
; CHECK: --fp-abstraction-ops: unknown operation in 'mul,nope'
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNormal (fp.mul RNE x x)))
(check-sat)
