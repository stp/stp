; The optional workload policies can be removed as a group without removing
; the persistent assumption core or either array decision procedure.
; RUN: %solver --incremental --incremental-core-only --incremental-profile --array-equality %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --incremental-core-only --incremental-profile --array-equality %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(set-option :produce-models true)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))
(assert (= x #b00))

(push 1)
(assert (= y (bvadd x #b01)))
(assert (= (select a x) #b10))
; CHECK: Incremental profile work: check=1 .*prepare-misses=0 .*context-definitions=0
; CHECK: Incremental profile cbp/backend: check=1 .*cbp-fed-levels=0 .*ext-preprocesses=0 .*base-preprocesses=0 .*policy=core extensionality=0 .*first-stack-preprocesses=0
; CHECK: ^sat
(check-sat)
; CHECK: \|x\| +#b00
; CHECK: \|y\| +#b01
(get-value (x y))
(pop 1)

; Extensionality is a correctness procedure, not an optional policy. It still
; owns this complete-stack round, but its speculative preprocessing is off.
(push 1)
(assert (= a b))
(assert (= (select b #b00) #b10))
; CHECK: Incremental profile cbp/backend: check=2 .*cbp-fed-levels=0 .*ext-preprocesses=0 ext-eliminations=0 .*policy=core extensionality=1
; CHECK: ^sat
(check-sat)
(pop 1)

(push 1)
(assert (= x #b11))
; CHECK: ^unsat
(check-sat)
(pop 1)
(exit)
