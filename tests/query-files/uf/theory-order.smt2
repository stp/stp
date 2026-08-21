; RUN: %solver --uninterpreted-functions --uf-ackermann=off --array-equality --incremental=off -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=off --array-equality --incremental=on -s %s 2>&1 | %OutputCheck %s
; CHECK: Theory coordination: EXTCHK conflict; UFCHK and ordinary replay skipped
; CHECK: ^unsat
; CHECK: Theory coordination: EXTCHK skipped; UFCHK conflict; ordinary replay skipped
; CHECK: ^unsat
; CHECK: Theory coordination: EXTCHK accepted; UFCHK conflict; ordinary replay skipped
; CHECK: ^unsat
;
(set-option :global-declarations true)
(set-logic QF_AUFBV)
(declare-fun f ((_ BitVec 2)) (_ BitVec 2))
(declare-const a (Array (_ BitVec 2) (_ BitVec 2)))
(declare-const b (Array (_ BitVec 2) (_ BitVec 2)))
(declare-const i (_ BitVec 2))
(declare-const j (_ BitVec 2))
(declare-const k (_ BitVec 2))
(declare-const e1 (_ BitVec 2))
(declare-const e2 (_ BitVec 2))
(declare-const x (_ BitVec 2))
(declare-const y (_ BitVec 2))
; This store-equality shape is decided by an EXTCHK propagation conflict,
; not by initial preprocessing.
(assert (= (store a i e1) (store b j e2)))
(assert (distinct k i))
(assert (distinct k j))
(assert (distinct (select a k) (select b k)))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
(reset-assertions)
; Without active extensionality atoms, UFCHK owns the conflict directly.
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
(reset-assertions)
; This time EXTCHK accepts the candidate before UFCHK rejects it.
(assert (= (store a i e1) (store b j e2)))
(assert (= x y))
(assert (distinct (f x) (f y)))
(check-sat)
