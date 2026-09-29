; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true %s | %OutputCheck %s
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true -d %s | %OutputCheck %s
;
; A record is minted by the encoding unit that first meets its operation
; -- here the forced first solve's exact-stack block -- and is then reused
; by every later per-level piece through the rewrite memo. Its proxy
; definitions and rule tiers must ride EVERY unit that mentions it: if
; they ride only the minting unit, that unit's retraction (or a backend
; rebuild dropping its cone) leaves live surrogates with no meaning, and
; the final check below -- the same product pinned to a value its
; operands cannot give -- answers sat instead of unsat.
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^sat
; CHECK: ^unsat
(set-logic QF_BVFP)
(set-option :global-declarations true)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const t (_ FloatingPoint 8 24))
(push 1)
(assert (= t (fp.mul RNE x y)))
(assert (fp.isNormal x))
(assert (fp.isNormal y))
(check-sat)
(push 1)
(assert (fp.gt x (fp #b0 #x7f #b00000000000000000000000)))
(assert (fp.gt y (fp #b0 #x7f #b00000000000000000000000)))
(check-sat)
(push 1)
(assert (fp.gt t (fp #b0 #x7f #b00000000000000000000000)))
(check-sat)
(push 1)
(assert (fp.lt t (fp #b0 #x76 #b00000000000000000000000)))
(check-sat)
(exit)
