; The extensionality block cache: every generated symbol in an equality
; round is named deterministically by what it stands for, and the round's
; node spine is pinned against garbage collection -- so re-pushing the
; identical stack lowers to the identical node and the block's encoding is
; reused outright, while a changed stack still shares every unchanged
; subcircuit through the recycled names.
; RUN: %solver --incremental --array-equality -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --array-equality -s %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= (select a #x1) #x11))
(push 1)
(assert (= a b))
(assert (= (select b #x1) #x22))
; CHECK: levels encoded
; CHECK: ^unsat
(check-sat)
(pop 1)
; the identical stack again: the whole block is a cache hit
(push 1)
(assert (= a b))
(assert (= (select b #x1) #x22))
; CHECK: levels reused
; CHECK: ^unsat
(check-sat)
(pop 1)
; different content still answers correctly (and re-encodes)
(push 1)
(assert (= a b))
(assert (= (select b #x1) #x11))
; CHECK: levels encoded
; CHECK: ^sat
(check-sat)
(pop 1)
(exit)
