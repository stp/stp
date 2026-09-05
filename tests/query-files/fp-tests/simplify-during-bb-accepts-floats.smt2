; RUN: %solver --bb.simplify-during-bb on %s | %OutputCheck %s
;
; --bb.simplify-during-bb re-simplifies a term when bit-blasting a child
; turns it constant. Its child dispatch classified every child as either
; BITVECTOR_TYPE or BOOLEAN_TYPE and otherwise ran assert(false); exit(-1).
;
; That misses the boundary invariant the same file's getConsts documents:
; FloatBlast removes floating-point *operations* but deliberately leaves
; float symbols and constants as their packed-bit leaves, still reporting
; FLOATINGPOINT_TYPE so the model can recover the sort. symfpu's unpack
; builds BVEXTRACTs straight over such a leaf, so one reaches the dispatch
; in any query where a float symbol survives simplification.
;
; The flag is off by default, so this answered `sat` without it and aborted
; with it: SIGABRT where assertions are live, and a silent exit 255 under
; NDEBUG, which is worse. Both operands stay symbolic and unconstrained so
; nothing folds them away before the bit-blaster.
(set-logic QF_FP)
(declare-const a Float32)
(declare-const b Float32)
(assert (fp.lt a b))
; CHECK: ^sat$
(check-sat)
