; RUN: %solver --lazy-write-reads=1 --lazy-write-reads-depth=2 %s | %OutputCheck %s
; RUN: %solver --lazy-write-reads=1 --lazy-write-reads-depth=2 -d %s | %OutputCheck %s
; RUN: %solver --lazy-write-reads=0 %s | %OutputCheck %s
; Reads at symbolic indexes over a write chain long enough, and read often
; enough, to be abstracted to refinement rows, with a constant array at the
; bottom. A row that misses every write falls through to the default. It
; used to fall through to a read of the constant array minted as a fresh
; variable: nothing tied that variable to the default, and its model entry
; was keyed on the read, which the factory folds to the default itself, so
; refinement could not finish and the solver aborted with "reached the end
; without proper conclusion".
(set-logic QF_ABV)
(declare-fun i0 () (_ BitVec 8))
(declare-fun i1 () (_ BitVec 8))
(declare-fun i2 () (_ BitVec 8))
(declare-fun i3 () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))
(declare-fun j0 () (_ BitVec 8))
(declare-fun j1 () (_ BitVec 8))
(declare-fun j2 () (_ BitVec 8))
(declare-fun j3 () (_ BitVec 8))
(declare-fun j4 () (_ BitVec 8))
(declare-fun j5 () (_ BitVec 8))
(declare-fun j6 () (_ BitVec 8))
(declare-fun j7 () (_ BitVec 8))
(declare-fun j8 () (_ BitVec 8))
(declare-fun j9 () (_ BitVec 8))
(declare-fun j10 () (_ BitVec 8))
(declare-fun j11 () (_ BitVec 8))
(declare-fun j12 () (_ BitVec 8))
(declare-fun j13 () (_ BitVec 8))
(declare-fun j14 () (_ BitVec 8))
(declare-fun j15 () (_ BitVec 8))
; Every cell is the default #x00 or a written #x02; none is #x01.
(push 1)
(assert (or (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j0) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j1) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j2) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j3) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j4) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j5) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j6) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j7) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j8) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j9) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j10) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j11) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j12) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j13) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j14) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j15) #x01)))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; The same with a symbolic default pinned to #x00.
(push 1)
(assert (= z #x00))
(assert (or (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j0) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j1) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j2) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j3) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j4) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j5) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j6) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j7) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j8) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j9) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j10) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j11) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j12) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j13) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j14) #x01) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j15) #x01)))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; Satisfiable: a read that misses every write reads the default.
(push 1)
(assert (or (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j0) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j1) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j2) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j3) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j4) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j5) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j6) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j7) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j8) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j9) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j10) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j11) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j12) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j13) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j14) #x07) (= (select (store (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) z) i0 #x02) i1 #x02) i2 #x02) i3 #x02) j15) #x07)))
(assert (= z #x07))
; CHECK: ^sat$
(check-sat)
(pop 1)
