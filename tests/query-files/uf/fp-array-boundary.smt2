; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^unsat
;
(set-logic QF_ABVFP)
(declare-fun f (Bool (_ BitVec 8) (_ BitVec 8)) (_ BitVec 4))
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(declare-const j (_ BitVec 4))
(declare-const z (_ FloatingPoint 8 24))
(assert (= i j))
(assert (distinct
  (f (fp.isNaN z) (select a i) ((_ fp.to_ubv 8) RNE z))
  (f (fp.isNaN z) (select a j) ((_ fp.to_ubv 8) RNE z))))
(check-sat)
