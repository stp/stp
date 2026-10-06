; A cell of an array of rounding modes that a later formula reads only
; through a store it does not need must still hold one of the five modes.
;
; The check-sat-assuming mints the read variable of a at i, and its pin
; to the five modes, on the assumption. The asserted formula reads the
; same cell through (store a j v): its transform hits the persistent row
; and is not pinned again for it, and FpTotalise pins only the read the
; formula names, (ite (= i j) v a_i), which with i = j is v. So the solve
; left a_i's bits free, yet the row is part of the solve and the model
; publishes the cell: the backend left 0b00101 there, and get-model
; refused it ("a RoundingMode cell of the model is not one of the five
; modes"). The driver now asserts the pin of every array-of-modes read
; variable it records as a permanent unit. -d checks the model against
; the stack.
;
; Which pattern a free cell gets is not ours to choose, so this pins the
; fixed behaviour -- both checks sat, the cell a mode, the model checked
; -- rather than a specific failure message. The second RUN line is the
; eager Ackermannisation the hosted floating-point abstraction uses,
; which hits the row the same way.
; RUN: %solver --incremental -d %s | %OutputCheck %s
; RUN: %solver --incremental --fp-abstraction=true --fp-abstraction-incremental=true -d %s | %OutputCheck %s
(set-option :produce-models true)
(declare-const a (Array RoundingMode RoundingMode))
(declare-const i RoundingMode)
(declare-const j RoundingMode)
(declare-const v RoundingMode)
; CHECK: ^sat
(check-sat-assuming ((distinct RTP (select (store a j v) i))))
(assert (= i j))
(assert (distinct RTN (select (store a j v) i)))
; CHECK-NEXT: ^sat
(check-sat)
; CHECK: \(define-fun \|a\| \(\) \(Array RoundingMode RoundingMode\)
(get-model)
; CHECK: \(select \|a\| \|i\|\) +(RNE|RNA|RTP|RTN|RTZ) +\)
(get-value ((select a i)))
(exit)
