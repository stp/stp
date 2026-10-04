; RUN: %solver --incremental=on --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
; RUN: %solver --incremental=on -d --bv-eq-abstraction=1 --bv-abstraction-width=8 %s | %OutputCheck %s
;
; The same stale proxy reached the array-equality final check, which is where
; the fuzzer found it: a reduction of a QF_ABVFP push/pop session.
;
; No push and no pop are needed. The driver blasts each conjunct of a level
; as its own root under its own literal, so a second check-sat over a grown
; stack is already a second root through one blaster. The square root here is
; an array index, the ite's second arm compares reads of a store at it, and
; the abstraction registers a proxy for the 12-bit read. Under the second
; root the relation was re-minted while the registry still answered with the
; first root's proxy, so the scalar name the solver chose for a read and the
; value its term evaluates to parted company, and the check that the complete
; array graph has reached a conflict-free fixed point aborted.
;
; Both queries are satisfiable: the ite's first arm needs only the two arrays
; to agree, and q is free.
(set-logic QF_ABVFP)
(declare-fun a () (Array Float32 (_ BitVec 12)))
(declare-fun b () (Array Float32 (_ BitVec 12)))
(declare-fun v () (_ BitVec 13))
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun f () Float32)
(declare-fun r () RoundingMode)
(assert (ite p
             (= a (store b ((_ to_fp 8 24) RNE 0.0) ((_ extract 12 1) v)))
             (bvuge (select a ((_ to_fp 8 24) RNE 0.0))
                    (select (store a (fp.sqrt r f)
                                   (select a ((_ to_fp 8 24) RNE 0.0)))
                            ((_ to_fp 8 24) RNE 0.0)))))
; CHECK: ^sat
(check-sat)
(assert q)
; CHECK-NEXT: ^sat
(check-sat)
(exit)
