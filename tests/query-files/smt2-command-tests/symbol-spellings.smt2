; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-const |x| (_ |BitVec| 8))
(define-const assert |Bool| |true|)
(declare-const get-option Bool)
(declare-const define-sort Bool)
(assert (|and| assert get-option define-sort (|=| x (_ |bv42| 8))))
(assert (|=| (|bvadd| x #x01) #x2b))
; Locals can shadow theory symbols; quoted and unquoted references agree.
(define-fun identity ((true Bool)) Bool |true|)
(assert (not (identity false)))
(assert (let ((and false)) (not |and|)))
; CHECK: ^sat$
(check-sat)
(reset)
(set-logic QF_UF)
; Bit-vector theory names are ordinary symbols in this signature.
(declare-const bvand Bool)
(declare-const BitVec Bool)
(assert (and |bvand| BitVec))
; CHECK: ^sat$
(check-sat)
(reset)
(set-logic QF_FP)
(declare-const f |Float32|)
(assert (|fp.isZero| f))
(assert (|=| f (_ |+zero| 8 24)))
; CHECK: ^sat$
(check-sat)
