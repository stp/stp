; Commands STP cannot answer must respond "unsupported" and leave the rest of
; the script to be processed. Previously each of these was a syntax error that
; abandoned everything after it.
; RUN: %solver %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun p () Bool)
(assert (and (= x #x1) (= x #x2)))
; CHECK-NEXT: ^unsat
(check-sat)
; CHECK-NEXT: ^unsupported
(get-proof)
; CHECK-NEXT: ^unsupported
(get-unsat-core)
; get-unsat-assumptions is supported now; after a plain check-sat there
; are no assumptions, so the core is the empty list.
; CHECK-NEXT: ^\(\)$
(get-unsat-assumptions)
; CHECK-NEXT: ^unsupported
(get-assignment)
; CHECK-NEXT: ^unsupported
(declare-sort S 0)
(reset-assertions)
(declare-fun x () (_ BitVec 4))
(assert (= x #x1))
; CHECK-NEXT: ^sat
(check-sat)
