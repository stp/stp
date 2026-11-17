; Every name declare-fun accepts has to come back out of the model, and a
; quoted symbol may hold UTF-8 and SMT-LIB whitespace. The function model used
; to print a name only when every byte was printable ASCII, and failed the
; check with an internal error on any other. The second function's name holds
; a tab.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat$
; CHECK: ^\(define-fun \|f\tg\| \(\(x0 \(_ BitVec 8\)\)\) \(_ BitVec 8\)
; CHECK: ^\(define-fun \|fé\| \(\(x0 \(_ BitVec 8\)\)\) \(_ BitVec 8\)

(set-logic QF_UFBV)
(set-option :produce-models true)
(declare-fun x () (_ BitVec 8))
(declare-fun |fé| ((_ BitVec 8)) (_ BitVec 8))
(declare-fun |f	g| ((_ BitVec 8)) (_ BitVec 8))
(assert (= (|fé| x) #x01))
(assert (= (|f	g| x) #x02))
(check-sat)
(get-model)
