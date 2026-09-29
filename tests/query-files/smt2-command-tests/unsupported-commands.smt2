; Commands STP cannot answer must respond "unsupported" and leave the rest of
; the script to be processed. Previously each of these was a syntax error that
; abandoned everything after it.
; RUN: %solver %s | %OutputCheck %s
(set-option :produce-unsat-assumptions true)
; CHECK-NEXT: ^unsupported
(set-option :produce-proofs true)
; CHECK-NEXT: ^unsupported
(set-option :produce-unsat-cores true)
(set-option :produce-assignments true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun p () Bool)
(assert (and (= x #x1) (= x #x2)))
; CHECK-NEXT: ^unsat
(check-sat)
; get-unsat-assumptions is supported now; after a plain check-sat there
; are no assumptions, so the core is the empty list.
; CHECK-NEXT: ^\(\)$
(get-unsat-assumptions)
; CHECK-NEXT: ^unsupported
(declare-sort S 0)
(reset-assertions)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
