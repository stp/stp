; Refusing a level for want of capacity is a judgement about the LIVE stack,
; not about the session. The charge against the cap is refunded when a level
; pops -- cbpRollbackCallerTo restores it from the checkpoint -- so the
; refusal it caused has to be released with it.
;
; It was not. The refusal set the same session-wide latch the futility leash
; sets, which nothing ever clears, so one excursion past the cap turned the
; pass off for good: a session that went deep once and then worked at depth
; two for the rest of its life never propagated another bit. The engine's own
; state was rolled back correctly the whole time; only the verdict on it was
; permanent. The trail already restores callCbpOff for exactly this reason.
;
; The cap admits the base (seven nodes) and one pushed level and refuses the
; second, which would be the ninth.
; After the pop there is room again, and the replacement level must be fed.
; RUN: %solver --incremental --incremental-profile --incremental-cbp-feed-cap 8 -s --check-sanity %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --incremental-profile --incremental-cbp-feed-cap 8 -s --check-sanity %s 2>&1 | %OutputCheck %s
(set-logic QF_BV)
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(assert (bvult (bvmul (bvadd a b) (bvadd a c)) #x40))
(push 1)
(assert (bvugt (bvmul (bvadd a b) (bvadd a c)) #x01))
(push 1)
(assert (bvugt (bvmul (bvadd a b) (bvadd a c)) #x02))
; the second pushed level does not fit
; CHECK: cbp off at level 2 \(stack over the feed cap\)
; CHECK: check=1 .*cbp-feed-rejected=1
(check-sat)
(pop 2)
(push 1)
(assert (bvugt (bvmul (bvadd a b) (bvadd a c)) #x05))
; the refused level is gone and its charge with it: feed the replacement
; CHECK: check=2 .*cbp-fed-levels=1
(check-sat)
(exit)
