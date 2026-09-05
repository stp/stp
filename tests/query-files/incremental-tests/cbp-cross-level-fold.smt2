; A shallow level's content fixes an index expression by bit-level
; reasoning alone, and a deeper level's read over an ite-indexed write
; chain must collapse under that CROSS-LEVEL fixing: the driver's
; session-persistent constant-bit propagation maintains the live prefix in
; stack order, folds the deep level's write index to a constant, and the
; simplifying factory's chaseRead then penetrates the chain (the
; Industrial_Control_C timeout family's mechanism, where per-level
; preparation is structurally blind). The pinning facts assert what
; the substitution consumed, and popping the fixing level must retract
; every fold derived from it -- the final block is satisfiable only
; with the flag the other way.
; RUN: %solver --incremental --check-sanity -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --check-sanity -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --incremental-cbp-reset --check-sanity -s %s 2>&1 | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun A () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun flag () Bool)
(declare-fun v () (_ BitVec 8))
(push 1)
; Pins flag=true only through the bit-vector transfer functions: the
; ite's value is forced to 0x01 two bits at a time, and branch 0x02
; contradicts them.
(assert (= (bvand (ite flag #x01 #x02) #x03) #x01))
(push 1)
; Reads over a chain whose top write index is ite(flag,0x0A,0x05):
; with flag pinned, the index folds to 0x0A, chaseRead penetrates to
; the 0x05 write, and the conjunct collapses to TRUE before anything
; is keyed or transformed.
(assert (= (select (store (store A #x05 v) (ite flag #x0A #x05) #xFF)
                   #x05)
           v))
; CHECK: cbp adopted
; CHECK: ^sat
(check-sat)
(pop 1)
(push 1)
; A different read over the same pinned flag folds the same way.
(assert (= (select (store A (ite flag #x07 #x03) #x11) #x03) #x22))
; CHECK: ^sat
(check-sat)
(pop 1)
(pop 1)
; The pinning level is gone: the fold must be gone with it. This block
; is satisfiable ONLY with flag=false (index 0x03, read 0x11) -- a
; stale flag=true fold would turn it unsat.
(push 1)
(assert (= (select (store A (ite flag #x07 #x03) #x11) #x03) #x11))
(assert (distinct (select A #x03) #x11))
; CHECK: ^sat
(check-sat)
; Forcing the flag back makes it genuinely unsat.
(assert flag)
; CHECK: ^unsat
(check-sat)
(pop 1)
(exit)
