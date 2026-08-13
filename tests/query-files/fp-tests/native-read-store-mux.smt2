; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
; RUN: %solver -r %s | %OutputCheck %s
;
; Regression test for https://github.com/stp/stp/issues/825.
;
; The classification's operand is a read over stores whose indexes stay
; symbolic, so the array transform expands it into a mux mixing a lowered
; packed circuit (the stored to_fp) with a float-stamped read variable. The
; mux must still derive the float sort from the branch that kept it -- it
; used to derive unknown and segfault in BBclassifyFP (makeTower over an
; empty operand vector).
;
; CHECK: ^sat
(set-logic QF_ABVFP)
(declare-const __ (_ BitVec 1))
(declare-const x7 (Array (_ BitVec 32) Float32))
(declare-const x  (Array (_ BitVec 32) Float32))
(assert (and (fp.lt (select x7 (_ bv2 32)) (ite (fp.lt (select x (_ bv0 32)) (select x ((_ zero_extend 31) __))) (_ +zero 8 24) (select x7 (_ bv3 32)))) (fp.leq (select x7 (_ bv0 32)) (select (store (store (store (store x7 (_ bv0 32) (select x7 (_ bv1 32))) (_ bv1 32) (select x7 (_ bv0 32))) (_ bv0 32) (select x (_ bv1 32))) ((_ zero_extend 31) __) (_ +zero 8 24)) (_ bv0 32)))))
(assert (fp.isNormal (select (store (store x7 (_ bv0 32) ((_ to_fp 8 24) ((_ zero_extend 31) __))) (_ bv1 32) (select x7 ((_ zero_extend 31) __))) ((_ zero_extend 31) __))))
(check-sat)
(exit)
