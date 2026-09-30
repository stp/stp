; Both queries project one core: names and assumption terms are printed in
; their respective responses, and unrelated entries are omitted from both.
; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_BV)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (! p :named positive))
(assert (! r :named irrelevant))
; CHECK-NEXT: ^unsat$
(check-sat-assuming ((not p) q))
; CHECK-NEXT: ^\(\|positive\|\)$
(get-unsat-core)
; CHECK-NEXT: ^\(\(not \|p\|\)\)$
(get-unsat-assumptions)
; Reading the projections in the other order gives the same answers.
; CHECK-NEXT: ^\(\(not \|p\|\)\)$
(get-unsat-assumptions)
; CHECK-NEXT: ^\(\|positive\|\)$
(get-unsat-core)

; A contradiction entirely among the assumptions needs no assertion labels.
; CHECK-NEXT: ^unsat$
(check-sat-assuming (q (not q)))
; CHECK-NEXT: ^\(\)$
(get-unsat-core)
; CHECK-NEXT: ^\(\|q\| \(not \|q\|\)\)$
(get-unsat-assumptions)

; An ordinary check supersedes the assumptions from the previous check.
(assert (not p))
; CHECK-NEXT: ^unsat$
(check-sat)
; CHECK-NEXT: ^\(\|positive\|\)$
(get-unsat-core)
; CHECK-NEXT: ^\(\)$
(get-unsat-assumptions)
