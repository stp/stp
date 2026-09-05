; RUN: %solver --array-equality -d %s | %OutputCheck %s
; CHECK: ^sat
; A whole-array disequality buried inside a definition of x, checked
; against the model with -d.
;
; Counterexample evaluation memoises through CounterExampleMap, and
; TermToConstTermUsingModel recursed on a looked-up definition by
; reference into the map. Evaluating an array equality mid-walk enters
; ArraysEqualUsingModel, whose ModelQuery guard restores the map by
; whole-map assignment when it returns -- freeing every node, including
; the one the suspended outer frame was still aliasing. The evaluator
; now copies each entry out of the map before recursing on it.
;
; Today the equality below reaches the guard only after evaluation has
; finished, via recheckCertifiedEqualities, where no frame is
; suspended. Running PropagateEqualities before lowerArrayEqualities --
; which the array-equality substitution work does -- moves x's whole
; definition into the substitution map with the disequality still
; inside it, and this query then segfaulted under the reference.
(declare-fun x () (_ BitVec 8))
(declare-fun i () (_ BitVec 4))
(declare-fun A () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun B () (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= ((_ zero_extend 7) (ite (distinct (store A i (_ bv7 8)) B) (_ bv1 1) (_ bv0 1))) x))
(check-sat)
