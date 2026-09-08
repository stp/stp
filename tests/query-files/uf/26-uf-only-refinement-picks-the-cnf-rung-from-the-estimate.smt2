; A solve whose only refinement is the uninterpreted-function loop chooses
; its CNF rung from the blast estimate, as a plain bit-vector query does.
; Left to the array-refinement fallback it was handed the size-based ABC
; rung, and on a large circuit that meant very-low: the vlsat3 files of
; QF_UFBV/20210312-Bouvier went from under a second to a 30s timeout.
;
; REQUIRES: cadical
;
; RUN: %solver --cadical -s --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; CHECK: cnf-auto: estimated [0-9]+ AND nodes, chose
; CHECK: ^sat$
;
; With an array read in the query the read refinement is in play and the
; ABC lowering keeps its own decision.
; RUN: %solver --cadical -s --uninterpreted-functions --incremental=off %S/Inputs/uf-with-array-read.smt2 2>&1 | %OutputCheck --check-prefix=ARRAY %s
; ARRAY-NOT: cnf-auto: estimated
; ARRAY: ^sat$
;
; EXPECT: sat, sat
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 16)) (_ BitVec 16))
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(assert (bvult (bvadd (f x) (f y)) (bvmul x y)))
(assert (distinct x y))
(check-sat)
