; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: unsupported domain sort \(Array \(_ BitVec 8\) \(_ BitVec 8\)\) at argument 0 of bad-array
; CHECK: unsupported domain sort UnknownSort at argument 0 of bad-unknown \(unknown
; CHECK: unsupported domain sort \(_ BitVec 0\) at argument 0 of bad-zero
; CHECK: unsupported result sort \(Array \(_ BitVec 8\) \(_ BitVec 8\)\) of bad-result
; CHECK-NOT: of ok-fp
; CHECK-NOT: of ok-rm
; CHECK: ^sat
; CHECK: REACHED-END
;
; The RoundingMode and FloatingPoint rows are now on the admitted side of the
; boundary: each is retained as a declaration that goes through and is
; applied, so that the sorts' positions here are pinned rather than merely
; unmentioned. Array and (_ BitVec 0) stay exactly where they were.
(set-logic QF_UFABVFP)
(declare-fun bad-array ((Array (_ BitVec 8) (_ BitVec 8))) Bool)
(declare-fun bad-unknown (UnknownSort) Bool)
(declare-fun bad-zero ((_ BitVec 0)) Bool)
(declare-fun bad-result (Bool) (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun ok-rm (RoundingMode) Bool)
(declare-fun ok-fp ((_ FloatingPoint 8 24)) Bool)
(declare-fun p (Bool (_ BitVec 8)) Bool)
(assert (= (p true #x00) (p true #x00)))
(assert (= (ok-rm RTZ) (ok-rm RTZ)))
(assert (= (ok-fp (fp #b0 #b10000000 #b00000000000000000000000))
           (ok-fp (fp #b0 #b10000000 #b00000000000000000000000))))
(check-sat)
(echo "REACHED-END")
