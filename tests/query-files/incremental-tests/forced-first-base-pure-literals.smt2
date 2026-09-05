; Explicit first engagement runs one pure-literal pass over an array/FP-free,
; base-only formula before any permanent clause is emitted.  The chosen
; literals are model witnesses, not consequences: a later mention must restore
; the original base formula rather than assert the old choice.  The second
; scope chooses q=false and therefore forces p=true; the third scope makes the
; restored disjunction inconsistent.
; RUN: %solver --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck %s
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (or p q))

; CHECK: Incremental profile cbp/backend: check=1 .*driver-clauses=0 .*base-preprocesses=1 base-eliminations=2
; CHECK: ^sat
(check-sat)
; CHECK: \|p\| +true
; CHECK: \|q\| +true
(get-value (p q))

(push 1)
(assert (not q))
; The shared original is restored once even though both of its pure variables
; were eliminated.  An OR needs three AIG clauses and its permanent root one;
; the pushed literal itself is an assumption, so the exact driver total is 4.
; CHECK: Incremental profile cbp/backend: check=2 .*driver-clauses=4 .*base-preprocesses=0 base-eliminations=0
; CHECK: ^sat
(check-sat)
; CHECK: \|p\| +true
; CHECK: \|q\| +false
(get-value (p q))
(assert (not p))
; CHECK: ^unsat
(check-sat)
(pop 1)
(exit)
