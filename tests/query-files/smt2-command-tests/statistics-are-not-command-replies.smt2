; The regular output channel carries command responses; everything a solver
; says about itself belongs on the diagnostic channel. Most of STP's statistics
; were already on it -- "Difficulty Initially:" and every {Pass} counter -- but
; the per-pass node sizes, one of the three difficulty lines, and three
; refinement notes went to stdout, interleaved with the replies, where a client
; reading responses cannot do anything with them.
;
; stdout under -s must be exactly what it is without -s, and the statistics
; must still be produced.
;
; The SAT backend's own "c ..." lines are CaDiCaL's, not STP's, and are not
; what this checks.
; RUN: %solver -s %s 2>/dev/null | %OutputCheck %s
; CHECK-NOT: Node size is
; CHECK-NOT: Difficulty After
; CHECK: ^sat$
; CHECK: define-fun
;
; RUN: %solver -s %s 2>&1 | %OutputCheck --check-prefix=BOTH %s
; BOTH: Node size is
; BOTH: ^sat$
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(assert (= (bvmul x y) (_ bv12 8)))
(assert (bvult x y))
(check-sat)
(get-model)
(exit)
