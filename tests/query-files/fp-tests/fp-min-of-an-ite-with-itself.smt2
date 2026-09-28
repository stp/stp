; RUN: %solver %s | %OutputCheck %s
;
; (fp.min x x) is x. The factory folds that as the term is built, so what
; comes back is the operand -- here an ite, whose kind is not a floating-point
; one -- rather than a fresh fp.min node. The parser then stamped the format
; onto it regardless and aborted in SetExpWidth, on input that never needed
; solving. See tests/api/C/fp-identity-passthrough.cpp for the C API's half of
; the same bug.
;
; The ite's two branches are 1.0/1.0 and 1.0, which are both 1.0 for every
; rounding mode, so the min is 1.0 whichever way c goes and is never a NaN.
(set-logic QF_BVFP)
(declare-fun c () Bool)
(declare-fun r () RoundingMode)
(assert (fp.isNaN
          (fp.min
            (ite c
              (fp.div r
                (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)
                (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000))
              (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000))
            (ite c
              (fp.div r
                (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)
                (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000))
              (fp #b0 #b01111111111 #b0000000000000000000000000000000000000000000000000000)))))
; CHECK: ^unsat
(check-sat)
