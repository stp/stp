; RUN: not %solver --array-equality %s 2>&1 | %OutputCheck %s
; CHECK: constant-array defaults cannot contain UF applications, Real terms or array-equality conditions
; An array equality hidden in an ITE guard is unsupported even when the
; default's own element sort is a bit-vector.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))
(assert (= (select ((as const (Array (_ BitVec 8) (_ BitVec 8)))
                   (ite (= a b) x (bvadd x #x01)))
                  #x00)
           #x01))
(check-sat)
