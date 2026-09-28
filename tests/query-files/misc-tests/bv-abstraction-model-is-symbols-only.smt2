; A BV abstraction registers terms alongside symbols, and a model must carry
; only the symbols.
;
; --bv-term-abstraction replaces a wide term -- the BVMULT here -- with fresh
; combinational inputs and keys them by the term itself, so that refinement can
; read back the bits the solver chose for it. ConstructCounterExample iterates
; that same map and took every entry for a symbol. On an asserting build the
; first candidate for this query died there:
;
;   Assertion `symbol.GetKind() == SYMBOL' failed.
;   AbsRefine_CounterExample::ConstructCounterExample
;
; and with asserts compiled out it published the abstraction's own value for
; (bvmul x y) into the model instead. That is the worse half: a candidate is
; checked by evaluating the query under the model, TermToConstTermUsingModel
; answers from the model for any term it finds there, and so the check would
; have confirmed the candidate from the abstraction it was supposed to be
; testing rather than from x and y underneath it.
;
; -d makes that evaluation part of the run rather than something the answer
; merely implies: it re-derives the query under the published model, which for
; the BVMULT means multiplying the two symbols the model does carry.
;
; The second leg is the control. The verdict belongs to the query and not to
; the encoding that reached it, so both legs answer the same thing -- 0x21 is
; 3 * 11 and x is only required to be above one.
;
; RUN: %solver --incremental=off -d --bv-term-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Assertion
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: bogus
; ABSTRACTED: ^sat$
;
; PLAIN-NOT: Fatal Error
; PLAIN: ^sat$
;
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= (bvmul x y) #x21))
(assert (bvugt x #x01))
(check-sat)
