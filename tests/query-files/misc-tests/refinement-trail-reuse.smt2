; Trail reuse across the batch pipeline's refinement rounds. Twelve reads of
; one array at free indices, each equal to a different constant: the first
; candidate puts several indices on the same value, every collision costs a
; congruence lemma and another solve on the same backend, and the query is
; satisfiable once the indices are spread apart. --refinement-trail-reuse
; keeps CaDiCaL's trail between those solves (ilb=2); the stats line says
; whether it engaged, and the verdict must not move either way. Both
; settings are given explicitly, so that a corpus sweep forcing one of them
; leaves this test's own expectations alone; the default is pinned by the
; UserDefinedFlags unit test. A CaDiCaL before 3.0 declines the whole-trail
; scope, so the engagement asserted here needs the 3.x line.
; REQUIRES: cadical, cadical-3
; RUN: %solver --cadical -s --refinement-trail-reuse=1 %s 2>&1 | %OutputCheck --check-prefix=KEPT %s
; RUN: %solver --cadical -s --refinement-trail-reuse=0 %s 2>&1 | %OutputCheck --check-prefix=FRESH %s
; KEPT: Refinement trail reuse: on
; KEPT: ^sat
; FRESH-NOT: Refinement trail reuse
; FRESH: ^sat
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun i0 () (_ BitVec 8))
(declare-fun i1 () (_ BitVec 8))
(declare-fun i2 () (_ BitVec 8))
(declare-fun i3 () (_ BitVec 8))
(declare-fun i4 () (_ BitVec 8))
(declare-fun i5 () (_ BitVec 8))
(declare-fun i6 () (_ BitVec 8))
(declare-fun i7 () (_ BitVec 8))
(declare-fun i8 () (_ BitVec 8))
(declare-fun i9 () (_ BitVec 8))
(declare-fun i10 () (_ BitVec 8))
(declare-fun i11 () (_ BitVec 8))
(assert (= (select a i0) #x01))
(assert (= (select a i1) #x02))
(assert (= (select a i2) #x03))
(assert (= (select a i3) #x04))
(assert (= (select a i4) #x05))
(assert (= (select a i5) #x06))
(assert (= (select a i6) #x07))
(assert (= (select a i7) #x08))
(assert (= (select a i8) #x09))
(assert (= (select a i9) #x0a))
(assert (= (select a i10) #x0b))
(assert (= (select a i11) #x0c))
(check-sat)
