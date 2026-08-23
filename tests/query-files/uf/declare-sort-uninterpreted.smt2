; (declare-sort S 0) introduces an uninterpreted sort. It has no operation but
; equality, so a query mentioning k terms of it is satisfiable exactly when it
; is satisfiable over a domain of k elements: STP gives it a bit-vector carrier
; wide enough that nothing the query can say distinguishes more elements than
; the carrier holds.
;
; This is the shape the hardware bounded-model-checking benchmarks use -- an
; opaque state sort, constants of it, and uninterpreted functions reading
; properties out of a state.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NOT: unsupported
; CHECK-NOT: error
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: REACHED-END
;
(set-logic QF_UFBV)
(declare-sort State 0)
(declare-fun tag (State) (_ BitVec 8))
(declare-fun ok (State) Bool)
(declare-fun s0 () State)
(declare-fun s1 () State)
(define-fun tagged ((s State)) Bool (= (tag s) #x01))
; A declared sort is usable as a define-fun result sort too, not only as a
; parameter's.
(define-fun same ((s State)) State s)

; Congruence over the uninterpreted sort: equal states have equal tags.
(push 1)
(assert (= (same s0) s1))
(assert (distinct (tag s0) (tag s1)))
(check-sat)
(pop 1)

; Two states can be distinct, and the functions over them are unconstrained.
(assert (distinct s0 s1))
(assert (tagged s0))
(assert (not (ok s1)))
(check-sat)
(echo "REACHED-END")
