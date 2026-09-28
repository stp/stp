; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --uf-sort-width=2 %s | %OutputCheck %s
;
; Every index but i0 and i2 occurs only under a read, so no index reaches a
; SAT variable before refinement. The Real path refines reads through a
; progress transaction, which must bind such an index as the batch path does
; rather than fail on the missing binding. Width 2 leaves 4 values for 14
; indices, so the congruence axioms over those indices are live.
(set-logic QF_AUFLRA)
(declare-sort U 0)
(declare-fun a () (Array U U))
(declare-fun x () Real)
(declare-fun i0 () U)
(declare-fun i1 () U)
(declare-fun i2 () U)
(declare-fun i3 () U)
(declare-fun i4 () U)
(declare-fun i5 () U)
(declare-fun i6 () U)
(declare-fun i7 () U)
(declare-fun i8 () U)
(declare-fun i9 () U)
(declare-fun i10 () U)
(declare-fun i11 () U)
(declare-fun i12 () U)
(declare-fun i13 () U)
(assert (not (= (select a i0) (select a i1))))
(assert (not (= (select a i1) (select a i2))))
(assert (not (= (select a i2) (select a i3))))
(assert (not (= (select a i3) (select a i4))))
(assert (not (= (select a i4) (select a i5))))
(assert (not (= (select a i5) (select a i6))))
(assert (not (= (select a i6) (select a i7))))
(assert (not (= (select a i7) (select a i8))))
(assert (not (= (select a i8) (select a i9))))
(assert (not (= (select a i9) (select a i10))))
(assert (not (= (select a i10) (select a i11))))
(assert (not (= (select a i11) (select a i12))))
(assert (not (= (select a i12) (select a i13))))
(assert (or (= i0 i2) (> x 3.0)))
(assert (not (= (select a i0) (select a i2))))
(assert (< x 5.0))
(check-sat)
; CHECK: ^sat
