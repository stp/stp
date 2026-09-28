; A preparation trial that exceeds its size budget is rejected together with
; the definitions it harvested.  Keeping those definitions while retaining
; the original formula falsely records a symbol as eliminated, even though
; encoding that formula creates bits for the symbol.  An
; identical next check would then invalidate and rebuild the cached piece.
; RUN: %solver --incremental --disable-cbitp --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental --disable-cbitp --incremental-profile --check-sanity %s 2>&1 | %OutputCheck --check-prefix=PROFILE %s
(set-logic QF_BV)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(declare-fun f () Bool)

(push 1)
(assert (and (xor b c) (or d (and e f))))
; CHECK-NEXT: ^sat
; PROFILE: Incremental profile work: check=1 .*prepare-rejected=1 .*context-definitions=0 .*context-entries=0
; PROFILE: ^sat
(check-sat)

; CHECK-NEXT: ^sat
; PROFILE: Incremental profile work: check=2 .*prepare-hits=1 .*prepare-misses=0 .*prepare-invalidated=0 .*prepare-rejected=0 .*context-definitions=0 .*context-entries=0
; PROFILE: ^sat
(check-sat)
(pop 1)
(exit)
