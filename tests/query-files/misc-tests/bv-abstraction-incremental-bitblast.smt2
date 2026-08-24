; Escalating an abstracted multiply a piece at a time.
; REQUIRES: minisat
;
; When the refinement gives up on a BVMULT it says what the operation is, and
; --bv-term-abstraction-inc-bitblast says only part of it: the bits up to and
; a little past the lowest one the candidate got wrong, leaving the rest for
; a later round if the query is not settled by then.
;
; That is sound for a product and for nothing else the abstraction takes. The
; low bits of a truncated product are a function of the operands' low bits
; alone -- carries travel upwards and never down -- so the narrowed encoding
; is a theorem about the whole multiplication. A quotient's low bits depend on
; the whole of both operands: 8/5 is 1, but the low two bits of 8 and 5 are 0
; and 1, and 0/1 is 0. So division and remainder escalate whole.
;
; Every piece reaches past a bit the candidate got wrong, and the bits below
; are already pinned exactly, so no candidate can disagree there and each
; piece therefore starts strictly above the last: the sequence climbs and the
; last one finishes it. 128 bits with a step of 32 takes four of them -- three
; partial and one that completes -- which is what this pins. Which bit each
; one reaches is the solver's business, since it is read off the candidate it
; was offered, so that is left alone; a fixture that pinned the boundaries
; broke the moment an unrelated default moved.
;
; It is off by default because its benefit has not been measured and each
; partial circuit repeats the encoding of the lower bits. The default leg
; below is the control: the same query escalating whole, to the same answer.
;
; -d re-derives the query under the published model, so both legs check the
; answer is a real one and not only that a line was printed. The candidate
; sequence decides whether these particular partial boundaries are visited,
; so this integration trace selects MiniSat explicitly.
;
; RUN: %solver --minisat --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-inc-bitblast=1 %s 2>&1 | %OutputCheck --check-prefix=PIECEWISE %s
; RUN: %solver --minisat --incremental=off -d -s --bv-eq-abstraction=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=WHOLE %s
; RUN: %solver --minisat --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; PIECEWISE-NOT: Fatal Error
; PIECEWISE-NOT: Assertion
; PIECEWISE: BV abstraction: encoding BVMULT up to bit [0-9]+ after
; PIECEWISE: BV abstraction: encoding BVMULT up to bit [0-9]+ after
; PIECEWISE: BV abstraction: encoding BVMULT up to bit [0-9]+ after
; PIECEWISE: BV abstraction: encoding BVMULT exactly after
; PIECEWISE: ^sat$
;
; WHOLE-NOT: up to bit
; WHOLE: BV abstraction: encoding BVMULT exactly after
; WHOLE: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun a () (_ BitVec 128))
(declare-fun b () (_ BitVec 128))
(assert (= (bvmul a b) #x00000000000000007ffffffc80000005))
(assert (bvugt a #x00000000000000000000000000000001))
(assert (bvugt b #x00000000000000000000000000000001))
(check-sat)
