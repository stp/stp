; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --array-equality --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; Equal arrays have equal cells, so a non-NaN cell is greater-or-equal to
; itself and this formula is unsatisfiable -- with whole-array equality
; deciding the array reasoning and a native comparison over the reads.
;
; With array equality active every read is abstracted to a fresh variable
; (ArrayTransformer, "ext_read") rather than expanded, and that variable is
; the comparison's operand from then on. It therefore has to carry the
; element format, exactly as the read-refinement path's stand-in does: both
; operands here are abstracted at once, so there is no other side to take the
; format from, and without it this query aborts on the blaster's source-sort
; assertion instead of answering.
;
; CHECK: ^unsat
(set-logic QF_ABVFP)
(declare-fun A () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun B () (Array (_ BitVec 4) (_ FloatingPoint 8 24)))
(declare-fun i () (_ BitVec 4))
(assert (= A B))
(assert (not (fp.isNaN (select A i))))
(assert (not (fp.geq (select A i) (select B i))))
(check-sat)
(exit)
