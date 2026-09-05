; Two oracles for one candidate cannot be asked before the candidate is real.
;
; With an active whole-array equality the complete array checker owns the array
; graph, so a conflict-free fixed point over a certified assignment has to make
; the lowered root true as well: there is no second array procedure to hand a
; disagreement to, and STP says so.
;
;   Fatal Error: CallSAT_ResultCheck: the complete array checker and the
;   bit-blasted/model-evaluation path disagree on the same candidate
;
; Under --bv-term-abstraction that stopped holding, and not because either
; oracle was wrong. An abstracted comparison is a free Boolean until refinement
; pins it to its operands, so model evaluation of the root can read false from
; a comparison the query needs true while the array graph, which the comparison
; is nothing to do with, settles conflict-free. The disagreement is between the
; two oracles and the abstraction, not between the two oracles.
;
; Refining the abstraction first -- inside the call that materialized the
; candidate, before either oracle -- removes the case: by the time the two are
; asked, every abstraction agrees with the operands it stands for.
;
; The float comparison here is what gets abstracted; the two RoundingMode
; arrays are what give the checker a graph to settle.
;
; RUN: %solver --incremental=off -d --array-equality --bv-term-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d --array-equality %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_ABVFP)
(declare-const x (_ FloatingPoint 3 5))
(declare-const p (Array (_ BitVec 1) RoundingMode))
(declare-const q (Array (_ BitVec 1) RoundingMode))
(assert (fp.isSubnormal (fp.div RNA x (fp #b1 #b010 #b0110))))
(assert (= p q))
(check-sat)
