; SOUNDNESS. The relief rebuild's whole-base pass answered sat on an unsat
; query, at default flags on QF_BV, whenever the rebuild happened to land on
; a check whose pushed level mentioned a base-defined variable.
;
; The pass harvests u -> v+1 from the base and deletes the equation. A live
; pushed level mentioning u makes u untouchable, so the loop that splits the
; harvest keeps (= u (bvadd v #x01)) asserted rather than eliminating it.
; RemoveUnconstrained then runs, and it decides from the FORMULA alone: v's
; only remaining occurrence is inside that map VALUE, which it cannot see. It
; drops (bvult v #x02) as v's last constraint and records a witness for v.
;
; What is re-encoded is therefore (= u (bvadd v #x01)) with v unconstrained.
; The rebuilt base is strictly WEAKER than the raw base it replaced: u is
; free, and (= u #xff) -- unsatisfiable under v < 2, since u is then 1 or 2 --
; is satisfied by v = 254. Nothing restores it, because the restore path is
; for content screened AFTER the rebuild and this level was already live.
;
; The fix closes the untouchable set under the substitution map's right-hand
; sides, to a fixpoint, before the unconstrained pass runs.
;
; Confirmed unsat by STP's own batch pipeline, Bitwuzla, cvc5 and Z3. Ten dead
; rounds is not arbitrary: the valve must fire on the final check, when the u
; level is the live one. --incremental-reencode-limit 1 only makes a small
; session reach the valve; the path is the default one.
; RUN: %solver --incremental --incremental-reencode-limit 1 --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --incremental-reencode-limit 1 --check-sanity %s | %OutputCheck %s
(set-logic QF_BV)
(declare-fun u () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
(declare-fun y1 () (_ BitVec 8))
(declare-fun y2 () (_ BitVec 8))
(declare-fun y3 () (_ BitVec 8))
(declare-fun y4 () (_ BitVec 8))
(declare-fun y5 () (_ BitVec 8))
(declare-fun y6 () (_ BitVec 8))
(declare-fun y7 () (_ BitVec 8))
(declare-fun y8 () (_ BitVec 8))
(declare-fun y9 () (_ BitVec 8))
(declare-fun y10 () (_ BitVec 8))
; the pass harvests this and deletes it; v's only other occurrence is the bound
(assert (= u (bvadd v #x01)))
(assert (bvult v #x02))
; dead rounds accumulate the mass the relief valve measures
(push 1)
(assert (bvugt (bvmul y1 y1) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y2 y2) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y3 y3) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y4 y4) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y5 y5) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y6 y6) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y7 y7) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y8 y8) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y9 y9) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
(assert (bvugt (bvmul y10 y10) #x03))
; CHECK: ^sat
(check-sat)
(pop 1)
; the valve fires on THIS check, so u is untouchable and v is not
(push 1)
(assert (= u #xff))
; CHECK: ^unsat
(check-sat)
(pop 1)
(exit)
