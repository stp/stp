; get-value of a floating-point term the query never mentioned, under the
; incremental driver.
;
; Nothing asserted here is floating-point: the stack is two bit-vector
; equalities, and the float appears for the first time in the get-value. Its
; value is still a function of the model -- the carrier bits are pinned, so
; the answer is 1.0 and nothing else -- and the batch driver has always said
; so. The incremental driver answered:
;
;   Fatal Error: floating-point model evaluation has no solve encoding context
;
; It builds its floating-point encoding context lazily, on first use during
; encoding, and published it to the model machinery only when it had one. A
; stack with no float in it left that machinery holding NULL, which already
; means "no solve has run" -- the one thing it is fatal for -- so a query
; that had in fact been solved was answered as though it had not.
;
; The two RUN lines are the same question put to the two drivers, and the
; point is that they answer it the same way. Filed from the C API, where the
; abort was unconditional; it reaches the same place from here.
;
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck --check-prefix=CHECK %s
(set-logic QF_BVFP)
(set-option :produce-models true)
(declare-const s (_ BitVec 1))
(declare-const e (_ BitVec 5))
; A binary16 sign bit and exponent, pinned to the ones 1.0 packs with, by
; bit-vector equalities that name no float. Symbols rather than constants
; because a float built only out of constants folds before it is ever
; encoded, which is not the case the driver got wrong.
(assert (= s #b0))
(assert (= e #b01111))
; CHECK: ^sat$
(check-sat)
; (CHECK-L because the echoed term holds regex metacharacters. Only the value
; is pinned: the echo is STP's own node, not the term as written.)
; CHECK-L: (fp #b0 #b01111 #b0000000000) )
(get-value ((fp s e #b0000000000)))

; Answered, so nothing below the last match may be an error. These have to sit
; after the last CHECK: a CHECK-NOT is scoped to the region ending at the next
; CHECK, so one placed above them all would search the empty region before
; `sat` and pin nothing at all.
; CHECK-NOT: Fatal Error
; CHECK-NOT: STP Error
(exit)
