; A cell of an array of rounding modes must hold one of the five modes in
; every model, including after the formula that first read it is gone.
;
; The array transform reads (select a i) through a fresh five-bit
; variable and pins it to the five modes on the formula that minted it:
; here the check-sat-assuming's assumption. Under the hosted
; floating-point abstraction the driver Ackermannises eagerly, and a
; later model materialises a row for every read variable the persistent
; encoding still holds -- so after the assumption is gone the plain
; check-sats still publish the cell, though its pin went with the
; assumption. The backend left 0b11000 there, and the model printer
; refused it ("a RoundingMode cell of the model is not one of the five
; modes"); through the C API, lifting the same cell into the push-time
; model snapshot failed in CreateRMConst. The driver now asserts the pin
; of every array-of-modes read variable it records as a permanent unit.
;
; Which pattern a free cell gets is not ours to choose, so this pins the
; fixed behaviour -- every check sat, and the cell a mode -- rather than
; a specific failure message.
; RUN: %solver --incremental --fp-abstraction=true --fp-abstraction-incremental=true %s | %OutputCheck %s
(set-option :produce-models true)
(declare-const i RoundingMode)
(declare-const a (Array RoundingMode RoundingMode))
; CHECK: ^sat
(check-sat-assuming ((distinct RTP (select a i))))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: \(define-fun \|a\| \(\) \(Array RoundingMode RoundingMode\)
(get-model)
; CHECK: \(\(select a i\) (RNE|RNA|RTP|RTN|RTZ)\)
(get-value ((select a i)))
(exit)
