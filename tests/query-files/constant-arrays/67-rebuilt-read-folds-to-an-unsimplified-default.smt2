; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --incremental=on %s | %OutputCheck %s
; Each read's array simplifies to something the factory chases the read
; through to a constant array, so rebuilding the read on it yields the
; array's default. The simplifier treats a default as a leaf and had never
; simplified it, yet carried the rebuilt node on as though its operands were
; simplified, and an assertion that they were failed. The incremental driver
; reached this; the batch driver rewrites so few reads away before it
; simplifies.
(set-logic QF_ABV)
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun i () (_ BitVec 8))
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
; The condition is false, so the read is of the constant array.
(assert (= (select (ite (= (bvand x #x0f) #xff) a ((as const (Array (_ BitVec 8) (_ BitVec 8))) (select a (bvnot x)))) i) #x07))
; CHECK: ^sat$
(check-sat)
; The store's index is at most #x0f, so a read at #xff misses it and reads
; the default.
(assert (not (= (select (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) (select a (bvnot y))) (bvand y #x0f) #x00) #xff) (select a (bvnot y)))))
; CHECK: ^unsat$
(check-sat)
