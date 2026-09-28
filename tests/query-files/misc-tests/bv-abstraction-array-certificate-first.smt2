; A refinement round leaves no theory certificate behind it.
;
; --bv-eq-abstraction replaces an equality by a free Boolean and pins it to the
; operands' bits only once a candidate model shows the two disagree. That made
; the abstraction one more refinement owner alongside the array-equality
; checker, and the driver consulted them in order: if the abstraction had
; something to say this round, its clauses went in and the search ran again --
; and the checker's conflict certificate for the very same candidate stayed
; pending, unencoded.
;
; The next candidate then arrived at a checker still holding the previous
; one's certificate, which it refuses outright:
;
;   Fatal Error: array-equality: a new candidate was checked before the prior
;   conflict certificates were encoded
;
; It is right to refuse. Encoding the certificate later would attach it to a
; conflict that is no longer the one in front of it, and dropping it loses a
; conflict the checker has already proved. So the round drains every owner
; that retained a lemma before it re-solves, and the abstraction is refined
; ahead of the checkers rather than after them -- a candidate that contradicts
; an abstraction is not an assignment of the query, and nothing downstream
; should be shown one.
;
; The store chain here is what puts the two owners in the same round: the
; equality between the two stores is abstracted, and the read inside the right
; hand side gives the checker an access to reason about.
;
; -d re-derives the query under the published model, so the leg checks the
; answer is a real one and not only that a line was printed.
;
; RUN: %solver --incremental=off -d --array-equality --bv-eq-abstraction=1 --bv-abstraction-width=1 %s 2>&1 | %OutputCheck --check-prefix=ABSTRACTED %s
; RUN: %solver --incremental=off -d --array-equality %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; ABSTRACTED-NOT: Fatal Error
; ABSTRACTED-NOT: Assertion
; ABSTRACTED: ^sat$
;
; PLAIN: ^sat$
;
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 2) (_ BitVec 2)))
(declare-const i (_ BitVec 2))
(assert (let ((w (store a i #b10))) (= w (store a (select w i) #b10))))
(check-sat)
