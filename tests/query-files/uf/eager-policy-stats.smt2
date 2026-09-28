; The eager congruence policy reports what it decided under -s. Without this
; the only way to tell a declined declaration from one that had nothing to
; install is to edit a flag and compare wall clock.
;
; g has two applications over symbolic arguments, so it has one pair, is
; selected, and installs it. h has two applications whose first arguments are
; distinct constants: the estimate partitions on the positions that are
; constant in every application, so h's two applications land in different
; groups, it is charged nothing, and it is not a candidate at all -- which is
; right, because the pair it would have had is one the loop drops. It still
; counts toward the declarations considered, so the total reads 1 of 2.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on -s %s 2>&1 | %OutputCheck %s
; CHECK: UF: eager selected g \(2 applications, 1 pairs estimated, 1 enumerated, 0 impossible, 1 constraints\)
; CHECK: UF: eager total 1/2 declarations, 1 constraints, budget 1/256 spent
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun g ((_ BitVec 8)) (_ BitVec 8))
(declare-fun h ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvult (g x) (bvadd (g y) #x10)))
(assert (bvult (h #x01 x) (bvadd (h #x02 y) #x10)))
(check-sat)
