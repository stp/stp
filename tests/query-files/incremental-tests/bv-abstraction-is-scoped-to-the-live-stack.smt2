; A retracted operation is not refined against later candidates.
;
; Abstraction records are appended as the blaster makes them and dropped only
; by a rebuild, never by a pop, and encodeAbstractionNode deliberately puts
; every record's bits into CNF before each search so the scan can read them.
; So after the pop below, the multiplication's result inputs are still
; decision variables: the search assigns them freely, they disagree with the
; operands underneath, and the refinement pins them -- on an operation no live
; assertion contains any more.
;
; The six solves after the pop pin both of its operands to values that move
; every time, which is what makes the dormant record disagree rather than
; being carried along by phase saving. Before refinement was scoped to the
; live stack the record walked through its whole blocking allowance and then
; installed a permanent 33,968-clause exact multiplier on the fifth of them,
; paid for on every later solve in the session.
;
; The first leg checks both halves: that the record IS refined while its level
; is live -- the schema lemma before the first answer -- and that nothing
; escalates after it. -d re-derives every answer under the published model, so
; a leg whose scope was too narrow, leaving a live record unchecked, reports
; sat on a model the raw stack rejects and fails here rather than passing
; quietly.
;
; RUN: %solver --incremental=on -d -s --bv-term-abstraction=1 --bv-term-abstraction-rounds=4 %s 2>&1 | %OutputCheck --check-prefix=SCOPED %s
; RUN: %solver --incremental=on -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; SCOPED: BV abstraction: BVMULT
; SCOPED: ^sat$
; SCOPED-NOT: BV abstraction: encoding BVMULT exactly
;
; PLAIN: ^sat$
; PLAIN: ^sat$
; PLAIN: ^sat$
; PLAIN: ^sat$
; PLAIN: ^sat$
; PLAIN: ^sat$
; PLAIN: ^sat$
(set-logic QF_BV)
(declare-fun x () (_ BitVec 64))
(declare-fun y () (_ BitVec 64))
(declare-fun z () (_ BitVec 64))
(push 1)
(assert (= (bvmul x y) z))
(assert (bvugt z (_ bv5 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1000003 64)))
(assert (= y (_ bv65537 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1007922 64)))
(assert (= y (_ bv170266 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1015841 64)))
(assert (= y (_ bv274995 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1023760 64)))
(assert (= y (_ bv379724 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1031679 64)))
(assert (= y (_ bv484453 64)))
(check-sat)
(pop 1)
(push 1)
(assert (= x (_ bv1039598 64)))
(assert (= y (_ bv589182 64)))
(check-sat)
(pop 1)
(exit)
