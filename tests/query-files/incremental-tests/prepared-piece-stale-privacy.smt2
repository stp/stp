; Prepared pieces may eliminate a level-private definition and cache the
; result.  Screening a new raw equality invalidates the older entry, but raw
; nodes are screened only once.  Re-pushing the first equality can therefore
; create a new elimination after its one screening; when the second equality
; is then re-pushed, both definitions are live and neither is private.  Cache
; hits must revalidate privacy against the current stack.  The substitution
; context happens to preserve the UNSAT answer in this small case, so the
; profile assertion checks the invalidation itself.
; RUN: %solver --incremental --disable-cbitp --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental --disable-cbitp --incremental-profile --check-sanity %s 2>&1 | %OutputCheck --check-prefix=PROFILE %s
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))

(push 1)
(assert (= x #x01))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (= x #x00))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)

; Recreate the first cache entry after the second equality invalidated it.
(push 1)
(assert (= x #x01))
; CHECK-NEXT: ^sat
(check-sat)

; Re-push the already-screened second equality while the first stays live.
(push 1)
(assert (= x #x00))
; CHECK-NEXT: ^unsat
; PROFILE: Incremental profile work: check=4 .*prepare-invalidated=1
; PROFILE: ^unsat
(check-sat)
(pop 1)
(pop 1)
(exit)
