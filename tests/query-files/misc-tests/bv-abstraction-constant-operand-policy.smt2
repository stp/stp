; A multiplication by a constant is a record like any other by default, with
; the value-blocking allowance the constant-operand cap gives it.
; --bv-term-abstraction-constant-operands=0 declines it instead: its exact
; encoding is the constant's shift-and-add, which propagates from the other
; operand, where a record spends a refinement round per candidate before
; escalating to that same circuit. Declining loses on both measured corpora
; as long as something else holds the wide products by constants, so the
; default admits them; the knob is for a corpus where nothing does. The
; width floor is at one bit here so that a 16-bit product qualifies.
;
; RUN: %solver --incremental=off -d -s -t --bv-term-abstraction=1 --bv-abstraction-width=1 --bv-term-abstraction-schemas=0 %s 2>&1 | %OutputCheck %s
; CHECK: kind=BVMULT width=16
; CHECK: ^sat$
;
; RUN: %solver --incremental=off -d -s -t --bv-term-abstraction=1 --bv-abstraction-width=1 --bv-term-abstraction-schemas=0 --bv-term-abstraction-constant-operands=0 %s 2>&1 | %OutputCheck --check-prefix=DECLINED %s
; DECLINED-NOT: kind=BVMULT
; DECLINED: ^sat$
;
; EXPECT: sat, sat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(assert (= (bvmul a #x000b) c))
(assert (bvugt c #x0100))
(assert (bvult a #x0100))
(check-sat)
