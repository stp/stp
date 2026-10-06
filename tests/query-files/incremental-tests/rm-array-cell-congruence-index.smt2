; A cell of an array of rounding modes whose pin has gone is not a
; don't-care when a later read's congruence still compares against it.
;
; The check-sat-assuming mints read variables for a at RTN and for b at
; that cell, both pinned to the five modes on the assumption only. The
; assertion reads b at v; under the eager Ackermannisation of the hosted
; floating-point abstraction that read is a chain over the earlier reads
; of b, (ite (= v a_RTN) b_(a_RTN) b_v), so the stale a_RTN is still an
; index the current solve compares against, now unpinned. The backend
; gave it 0b01100, the comparison failed for every v, and the model then
; published that pattern as a's cell at RTN: the printer refused it ("a
; RoundingMode cell of the model is not one of the five modes").
;
; Completing such a cell to a mode when the model is read out is not a
; fix: the solve had v = RNE, so completing a_RTN to RNE turns the
; comparison true, sends b at v to the stale cell, and publishes a model
; that falsifies the assertion -- -d reports "the model does not satisfy
; an asserted formula". The pin has to hold in the solve, so the driver
; now asserts the pin of every array-of-modes read variable it records
; as a permanent unit.
;
; The unused declaration of i is part of the reproduction: it shifts the
; node numbers the read variables are named by, and with them the bits
; the backend leaves. Which pattern a free cell gets is not ours to
; choose, so this pins the fixed behaviour -- every check sat and the
; model checked -- rather than a specific failure message.
; RUN: %solver --incremental --fp-abstraction=true --fp-abstraction-incremental=true -d %s | %OutputCheck %s
(set-option :produce-models true)
(declare-const i RoundingMode)
(declare-const j RoundingMode)
(declare-const k RoundingMode)
(declare-const v RoundingMode)
(declare-const a (Array RoundingMode RoundingMode))
(declare-const b (Array RoundingMode RoundingMode))
; CHECK: ^sat
(check-sat-assuming ((distinct (select b (select a RTN)) (select (store a k RTP) (select a v)))))
; CHECK-NEXT: ^sat
(check-sat)
(assert (distinct j (select a (select b v))))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: \(define-fun \|a\| \(\) \(Array RoundingMode RoundingMode\)
(get-model)
(exit)
