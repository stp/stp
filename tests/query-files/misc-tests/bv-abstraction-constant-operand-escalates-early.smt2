; An abstracted division, remainder or multiplication one of whose operands
; is a constant has an exact encoding that is the constant's shift-and-add
; -- the multiplier prunes its rows to the constant's set bits, and a
; division by a constant goes through its defining relation over such a
; product -- tens of thousands of clauses at 256 bits where a symbolic
; operand costs half a million. Ruling out one operand pair per round is a
; poor bargain against that, so such a record's value-blocking allowance is
; capped (--bv-term-abstraction-constant-operand-limit, one by default):
; the first refuted candidate is blocked and the second escalates. The
; schemas are off so that a blocking lemma is the only refinement short of
; escalation, and -d re-derives the answer under the published model.
;
; RUN: %solver --incremental=off -d -s -t --bv-term-abstraction=1 --bv-abstraction-width=1 --bv-term-abstraction-schemas=0 --bb.div-by-const-width=1 %s 2>&1 | %OutputCheck %s
; CHECK: BV abstraction: encoding BV(DIV|MOD|MULT) exactly after 1 blocking lemmas
; CHECK: kind=BVDIV width=16 state=exact blocking=1 schemas=0 exact=1 exact-bits=16 allowance=1
; CHECK: ^sat$
;
; Uncapped, the record draws on the ordinary allowance, here the round
; ceiling of three.
; RUN: %solver --incremental=off -d -s -t --bv-term-abstraction=1 --bv-abstraction-width=1 --bv-term-abstraction-schemas=0 --bv-term-abstraction-constant-operand-limit=0 --bv-term-abstraction-rounds=3 %s 2>&1 | %OutputCheck --check-prefix=UNCAPPED %s
; UNCAPPED: kind=BVDIV width=16 state=(open|exact) blocking=[0-9]+ schemas=0 exact=[01] exact-bits=(0|16) allowance=3
; UNCAPPED: ^sat$
;
; EXPECT: sat, sat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(assert (= (bvudiv a #x000b) c))
(assert (= (bvurem a #x000b) #x0007))
(assert (bvugt c #x0003))
(assert (bvult a #x00ff))
(check-sat)
