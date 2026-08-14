; RUN: %solver -d --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; The counterexample check decides each array equality from the cells
; the model published. Over a float *index* those cells are not where a
; source term says they are: the solve canonicalises float indexes and
; records against the lowered carrier access, so the operands have to be
; lowered the same way before a cell can be found.
;
; And once they are, one more thing has to hold, which is what this file
; exists for. A cell belongs to the *value* of its index, but a float
; constant interns apart from the plain bit-vector constant spelling its
; bits, so one index value reaches the walk under two node identities.
; Keyed by node that is two candidate cells: one finds the recorded
; value, the other finds nothing and completes to zero, and two equal
; arrays are reported as differing.
;
; This query is a reduced fuzz counterexample, kept rather than
; hand-written because a hand-written one did not reproduce it -- the
; two spellings arise from the interaction between the literal index,
; the symbolic one, and the store chain, not from any one of them.
; Dropping the normalisation of the cell keys turns it into "an array
; equality's lowering is true in the model, but the model gives the two
; operands the user equated different contents"; that mutation is what
; this file is checked against.
(set-logic QF_ABVFP)
(declare-fun a0 () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun a1 () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun a2 () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun v0 () (_ BitVec 8))
(declare-fun f0 () (_ FloatingPoint 8 24))
(assert (= (select a0 ((_ to_fp 8 24) #x3f800000)) v0))
(assert (distinct (store a2 f0 v0) (store a2 f0 #x00)))
(assert (= (store (store a0 f0 #x01) f0 v0) a1))
(check-sat)
