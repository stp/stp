; RUN: %solver -d --array-equality %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; An equality between a chain of writes and the chain's own base is
; solved by rewriting rather than abstracted, so it mints no record and
; the consistency checker never sees it. That makes it the one place
; where a wrong answer has nothing behind it -- and re-evaluating the
; query cannot help, because the re-evaluation resolves the equality
; through the very rewriting it would have to check.
;
; The counterexample check therefore compares each lowering against the
; array cells the model publishes, for the operands the query actually
; equates. Under -d this file exercises that on a chain carrying both
; kinds of write: the innermost store to #b010 is shadowed by the
; outermost one and its conjunct is dropped, while the store to #b001
; is live and is what contradicts the read below.
;
; The contradiction sits deliberately on an inner live write rather
; than the outermost one. Making the shadowing test fire too eagerly --
; dropping conjuncts that are not shadowed -- then turns this query
; sat, and the recheck reports the lowering true in a model whose two
; operands differ at #b001.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 3) (_ BitVec 4)))
(assert (= (store (store (store a #b010 #x2) #b001 #x1) #b010 #x9) a))
(assert (= (select a #b001) #x5))
(check-sat)
