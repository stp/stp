; Global declarations keep the definitions introduced by :named, but core
; membership follows the lifetime of assertions, including in batch mode.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
; RUN: %solver --incremental=off %s | %OutputCheck %s
(set-option :global-declarations true)
(set-option :produce-unsat-cores true)
(set-logic QF_BV)
(declare-const p Bool)
(assert (! p :named base))
(push 1)
(assert (! (not p) :named temporary))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|base\| \|temporary\|\)$
(get-unsat-core)
(pop 1)
; CHECK-NEXT: ^sat$
(check-sat)
(push 1)
(assert (! (not p) :named replacement))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|base\| \|replacement\|\)$
(get-unsat-core)

; The names still denote p and (not p), but asserting those aliases does not
; label the new assertions. The production option survives reset-assertions.
(reset-assertions)
; CHECK-NEXT: ^true$
(get-option :produce-unsat-cores)
(assert base)
(assert replacement)
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\)$
(get-unsat-core)

; A full reset restores the option's default and permits labels to be reused.
(reset)
; CHECK-NEXT: ^false$
(get-option :produce-unsat-cores)
(set-logic QF_BV)
(set-option :produce-unsat-cores true)
(assert (! false :named base))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|base\|\)$
(get-unsat-core)
