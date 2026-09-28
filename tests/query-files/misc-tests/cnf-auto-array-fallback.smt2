; Under array read refinement, `auto` keeps the older size-based choice made
; from the built ABC AIG's node count. The estimate-based resolution is for
; the eager encodings only: the in-house and Gia rungs are unmeasured under
; refinement, so a refining query must keep taking the ABC path whatever the
; estimate says.
;
; Twelve reads at distinct symbolic indexes, so the read count is past the
; eager-encoding regime and the solve actually refines.
;
; RUN: %solver --SMTLIB2 -s %s 2>&1 | %OutputCheck %s
;
; CHECK-NOT: estimated
; CHECK: ^cnf-auto: [0-9]+ AIG nodes, chose medium$
; CHECK: ^sat$
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 32)))
(declare-fun i0 () (_ BitVec 32))
(declare-fun i1 () (_ BitVec 32))
(declare-fun i2 () (_ BitVec 32))
(declare-fun i3 () (_ BitVec 32))
(declare-fun i4 () (_ BitVec 32))
(declare-fun i5 () (_ BitVec 32))
(declare-fun i6 () (_ BitVec 32))
(declare-fun i7 () (_ BitVec 32))
(declare-fun i8 () (_ BitVec 32))
(declare-fun i9 () (_ BitVec 32))
(declare-fun i10 () (_ BitVec 32))
(declare-fun i11 () (_ BitVec 32))
(assert (bvult (select a i0) (select a i1)))
(assert (bvult (select a i1) (select a i2)))
(assert (bvult (select a i2) (select a i3)))
(assert (bvult (select a i3) (select a i4)))
(assert (bvult (select a i4) (select a i5)))
(assert (bvult (select a i5) (select a i6)))
(assert (bvult (select a i6) (select a i7)))
(assert (bvult (select a i7) (select a i8)))
(assert (bvult (select a i8) (select a i9)))
(assert (bvult (select a i9) (select a i10)))
(assert (bvult (select a i10) (select a i11)))
(assert (bvugt (bvadd (select a i0) (select a i11)) #x00000010))
(check-sat)
