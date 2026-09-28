; The same twelve reads with two indices forced equal by the arithmetic
; and their values forced apart: unsatisfiable, and a seeding that starts
; every index apart must not delay or move that answer. The hints are
; search advice; the congruence lemma is what refutes the query. Gated as
; array-index-hints.smt2 is.
; REQUIRES: cadical, cadical-3
; RUN: %solver --cadical -s --array-index-hints=decide %s 2>&1 | %OutputCheck --check-prefix=DECIDE %s
; RUN: %solver --cadical -s --array-index-hints=phase %s 2>&1 | %OutputCheck --check-prefix=PHASE %s
; RUN: %solver --cadical --array-index-hints=off %s | %OutputCheck --check-prefix=OFF %s
; DECIDE: Array index hints: decided, 12 indices over 1 arrays
; DECIDE: ^unsat
; PHASE: Array index hints: phased, 12 indices over 1 arrays
; PHASE: ^unsat
; OFF: ^unsat
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
; i0 and i1 are forced equal by the arithmetic, not by a substitution the
; simplifier would take, and the two reads disagree on the value there.
(assert (bvult i0 i1))
(assert (bvult i1 (bvadd i0 #x01)))
(check-sat)
