; A pushed conjunct that DEFINES a harvested substitution must never be
; rewritten under its own entry: substituting x -> t into (= x t) yields
; TRUE and the constraint silently vanishes -- no equation, no
; elimination record, no model replay. On an array session the raw-stack
; model check then reads a default for x, declares every candidate
; bogus, and the refinement loop spins forever finding no violated
; congruence axiom (the driver now dies with a FatalError on that
; combination instead of hanging). Three pins:
;
; 1. The session completes at all, definers inside multi-conjunct levels
;    and as single-conjunct levels both preserved.
; 2. A defining equation binds for real: get-value reads the defined
;    value through the model, not a default.
; 3. Re-pushing an OPPOSITE definition after a pop answers from the live
;    branch: the model channel's seeds are withdrawn per solve, and a
;    stale seeding from the popped branch must not shadow the new one.
; RUN: %solver -s --incremental --check-sanity %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental-auto-engage-at 1 --check-sanity %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun i () (_ BitVec 4))
(declare-fun p () Bool)
(declare-fun q () (_ BitVec 8))
(declare-fun r () (_ BitVec 8))
; base array content keeps every solve on the refinement path, whose
; model check is what a dropped definer breaks
(assert (bvult (select a #x0) #xff))
; a level that IS its definer, and a level holding one among other
; conjuncts
(push 1)
(assert (= i #x3))
(push 1)
(assert p)
(assert (bvult (select a i) #x80))
(push 1)
(assert (or (not p) (bvule (select a i) #x7f)))
; CHECK: ^sat
(check-sat)
; the defining equation binds i for real
; CHECK: \( \|i\|  #x3 \)
(get-value (i))
(pop 1)
(pop 1)
(pop 1)
; a private definition is eliminated and replayed; after the pop, the
; OPPOSITE branch's definition must win over the retracted one
(push 1)
(assert (= q (bvadd r #x01)))
(assert (bvult r #x01))
; the whole level eliminates: q by its equation, r because the bound
; simplifies to a definition (r = 0)
; CHECK: 2 eliminated
; CHECK: ^sat
(check-sat)
; CHECK: \( \|q\|  #x01 \)
(get-value (q))
(pop 1)
(push 1)
(assert (= q (bvadd r #x02)))
(assert (bvult r #x01))
; CHECK: 2 eliminated
; CHECK: ^sat
(check-sat)
; a stale seeding of the popped branch would still answer #x01 here
; CHECK: \( \|q\|  #x02 \)
(get-value (q))
(pop 1)
(exit)
