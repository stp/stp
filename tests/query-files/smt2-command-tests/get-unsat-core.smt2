; Named cores project the driver's failed assumptions, including on the first
; check in the default mode. The irrelevant assertion must not appear.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
(set-option :produce-unsat-cores true)
; CHECK-NEXT: ^true$
(get-option :produce-unsat-cores)
(set-logic QF_BV)
(declare-const p Bool)
(declare-const q Bool)
(assert (! p :named positive))
(assert (! q :named irrelevant))
(assert (! (not p) :named negative))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|positive\| \|negative\|\)$
(get-unsat-core)
; Reading the same core again does not consume it.
; CHECK-NEXT: ^\(\|positive\| \|negative\|\)$
(get-unsat-core)
; A repeated check retains the original assertion labels.
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|positive\| \|negative\|\)$
(get-unsat-core)

; Unnamed assertions contribute to the refutation but have no output entry.
(reset-assertions)
(declare-const p Bool)
(assert p)
(assert (! (not p) :named needs-background))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|needs-background\|\)$
(get-unsat-core)

; When the unnamed background is already unsatisfiable, the core is empty.
(reset-assertions)
(assert false)
(assert (! true :named unused))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\)$
(get-unsat-core)
