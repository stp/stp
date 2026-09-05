; RUN: %solver %s | %OutputCheck %s
;
; fp.min and fp.max are unspecified only on (+0, -0) and (-0, +0), and the
; choice is a function of the two operands' sign bits -- which is why the
; array supplying it is indexed on those two bits rather than on the whole
; packed pair.
;
; Narrowing an unspecified choice is only sound if it keeps the cases that
; SMT-LIB leaves separately open apart. This asserts all four at once:
; fp.min may take the negative zero for (+0, -0) while taking the positive
; one for (-0, +0), and fp.max may disagree with fp.min about both. If any
; pair had been collapsed into one cell the conjunction would be unsat.
(set-logic QF_FP)
(define-fun pz () Float32 ((_ to_fp 8 24) #x00000000))
(define-fun nz () Float32 ((_ to_fp 8 24) #x80000000))

(assert (fp.isNegative (fp.min pz nz)))
(assert (fp.isPositive (fp.min nz pz)))
(assert (fp.isPositive (fp.max pz nz)))
(assert (fp.isNegative (fp.max nz pz)))
; CHECK: ^sat$
(check-sat)
