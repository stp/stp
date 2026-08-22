; A floating-point UF argument that is also a float array index -- the case
; §6 of the design names as the one that proves the pass ordering.
;
; FpTotalise is deliberately not idempotent: feeding its output back through
; it would canonicalise a float array index a second time. UF lowering runs
; first and wraps the actual in FP_TO_IEEE_BV, so FpTotalise::canonicalIndex
; meets a boundary that is already there. It tolerates one explicitly; this
; is the query that exercises that tolerance rather than asserting it.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=on --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
; CHECK: ^sat
; CHECK: REACHED-END
;
(set-logic QF_UFABVFP)
(declare-fun f ((_ FloatingPoint 8 24)) (_ BitVec 4))
(declare-const a (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-const u (_ FloatingPoint 8 24))
(declare-const v (_ FloatingPoint 8 24))
(push 1)
(assert (= u v))
(assert (= (select a u) #x01))
(assert (distinct (f u) (f v)))
(check-sat)
(pop 1)
(push 1)
; Distinct indexes: the array read constrains nothing about f, and the two
; applications are free to differ.
(assert (not (= u v)))
(assert (= (select a u) #x01))
(assert (= (select a v) #x02))
(assert (distinct (f u) (f v)))
(check-sat)
(pop 1)
(echo "REACHED-END")
