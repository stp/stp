; An equality one side of which is a constant is not made a record by the
; equality abstraction: a comparison against a constant is one AND over the
; term's bits, which propagates, where a record is a free Boolean the
; congruence refinement pins a round at a time. With the width floor at one
; bit so that a 16-bit equality qualifies, the coverage line shows the
; candidate and no record, and the answer comes from the comparator.
;
; RUN: %solver --incremental=off -s -t --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck %s
; CHECK: Abstraction coverage \(candidates -> abstracted\): eq=2->1
; CHECK: ^sat$
;
; --bv-eq-abstraction-constant-side admits it as a record beside the
; symbolic one.
; RUN: %solver --incremental=off -s -t --bv-eq-abstraction=1 --bv-abstraction-width=1 --bv-eq-abstraction-constant-side=1 %s 2>&1 | %OutputCheck --check-prefix=RECORD %s
; RECORD: Abstraction coverage \(candidates -> abstracted\): eq=2->2
; RECORD: ^sat$
;
; EXPECT: sat, sat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(assert (= (bvmul a b) #x0100))
(assert (= (bvxor a c) (bvadd b c)))
(assert (bvugt a #x0010))
(check-sat)
