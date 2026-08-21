; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: already denotes an ordinary symbol
; CHECK: uninterpreted function .f. is already declared
; CHECK: already denotes a define-fun
; CHECK: ^sat
; CHECK: REACHED-END
; CHECK-NOT: syntax error
;
; UF declarations, scalar symbols, and define-fun macros share the SMT-LIB
; top-level namespace. A nonzero-arity declaration over any of them is
; rejected nonfatally and leaves the prior owner intact. (The reverse
; direction -- a zero-arity declare-fun, declare-const or define-fun over a
; UF name -- is a UF-free shape and keeps the legacy syntax error; see the
; *-known-name-pinned and zero-arity-uf-name-pinned files.) Nested let
; binders still shadow normally and resolve before UF application
; hash-consing.
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-fun x ((_ BitVec 8)) (_ BitVec 8))
(declare-fun f ((_ BitVec 8)) Bool)
(define-fun m ((q (_ BitVec 8))) (_ BitVec 8) q)
(declare-fun m ((_ BitVec 8)) (_ BitVec 8))
(assert (= (let ((x #x01)) (let ((x #x02)) (f x))) (f #x02)))
(check-sat)
(echo "REACHED-END")
