; Source occurrences survive splitting, duplicate elimination and new scopes.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_BV)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (! (and p q) :named bundle))
(assert (! p :named duplicate))
(assert (! r :named irrelevant))
(push 1)
(assert (! (not p) :named negative))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|bundle\| \|negative\|\)$
(get-unsat-core)
(pop 1)

; The same shared conjunct now contributes to a different assumption query.
; CHECK-NEXT: ^unsat$
(check-sat-assuming ((not q) r))
; CHECK-NEXT: ^\(\|bundle\|\)$
(get-unsat-core)
; CHECK-NEXT: ^\(\(not \|q\|\)\)$
(get-unsat-assumptions)

; A source at the same stack position must receive its current label.
(push 1)
(assert (! (not p) :named replacement))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|bundle\| \|replacement\|\)$
(get-unsat-core)
(pop 1)
(reset-assertions)
(declare-const p Bool)
(assert (! p :named first))
(assert (! p :named second))
(assert (! (not p) :named opposite))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|first\| \|opposite\|\)$
(get-unsat-core)
