; Only the whole asserted term contributes a core label. Nested :named
; annotations define symbols, even when simplification gives the same AST.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
(set-option :produce-unsat-cores true)
(set-logic QF_BV)
(assert (not (! true :named nested)))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\)$
(get-unsat-core)

(reset-assertions)
(assert (! (! false :named inner) :named |outer label|))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|outer label\|\)$
(get-unsat-core)

; Empty and reserved-word labels must remain valid quoted SMT-LIB symbols.
(reset-assertions)
(assert (! false :named ||))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|\|\)$
(get-unsat-core)

(reset-assertions)
(assert (! false :named |assert|))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|assert\|\)$
(get-unsat-core)
