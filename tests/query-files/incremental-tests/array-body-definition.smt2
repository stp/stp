; A pushed-level definition whose BODY carries an array read must reach
; the solver as a real asserted equation, never as a private-variable
; elimination. Eliminating it would (a) hand the model-replay channel a
; read whose registry row is not part of any active encoding, and (b)
; lean the context's cycle check on STPMgr::VarSeenInTerm, which does
; not look inside read-over-write terms. The equality harvests already
; refuse array bodies (recogniseDefinition); this pins the same rule for
; the piece-preparation harvest.
;
; The read is a store at i selected at j, so the node factory cannot
; fold it at parse time and a genuine READ(WRITE(...)) body reaches the
; harvest.
; RUN: %solver -s --incremental --check-sanity %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental-auto-engage-at 1 --check-sanity %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_ABV)
(declare-fun A () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i () (_ BitVec 8))
(declare-fun j () (_ BitVec 8))
(declare-fun v () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(push 1)
; x is private to this level and defined by an array-carrying body; the
; stats line pins that it is NOT counted as eliminated.
(assert (= x (select (store A i v) j)))
(assert (bvult v #x10))
; CHECK: 0 eliminated
; CHECK: ^sat
(check-sat)
(push 1)
; With the indices forced equal the read collapses semantically to v,
; so x must equal v; the equation only enforces that if it is really
; asserted (or restored) rather than dropped.
(assert (= i j))
(assert (distinct x v))
; CHECK: ^unsat
(check-sat)
(pop 1)
; CHECK: ^sat
(check-sat)
(pop 1)
