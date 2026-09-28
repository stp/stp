; RUN: %solver -d --fp-abstraction=1 --fp-abstraction-ops=all --array-equality %s | %OutputCheck %s
; CHECK: ^sat$
; The eager arm decides the equality and retires its record, so the array
; checker is not active, but the proxy is still the SAT solver's answer
; under the fp.to_sbv surrogate. The first candidate's surrogate is wrong
; and x5 satisfies the formula anyway; accepting that candidate by repair
; kept a proxy that is false while the exact operands agree, and -d
; failed with "an array equality's lowering is false in the model".
(set-logic QF_AUFBVFP)
(declare-const x4 (Array (_ BitVec 13) (_ BitVec 7)))
(declare-const x5 Bool)
(declare-const x Float16)
(declare-fun f ((_ BitVec 9) (_ BitVec 13)) (_ BitVec 10))
(declare-fun r () RoundingMode)
(declare-fun a () (Array (_ BitVec 13) (_ BitVec 7)))
(assert (or x5 (= x4 (store (store a (_ bv0 13) (_ bv1 7)) ((_ sign_extend 9) ((_ fp.to_sbv 4) r x)) (select a ((_ sign_extend 3) (f (_ bv1 9) (_ bv0 13))))))))
(check-sat)
