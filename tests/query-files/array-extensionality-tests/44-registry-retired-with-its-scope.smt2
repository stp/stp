; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^sat
; The equality registry is reachable only from the assertions that name
; its abstraction variables, but it was pinned to the manager's
; lifetime: nothing dropped a record when the scope that created it was
; popped. Because a record holds its construction operands, that kept
; the operand symbols in the manager's unique table too -- so p was
; still a declared array after the pop, the declaration below was lexed
; as a reference to it rather than a fresh name, and the run died with
;   (error "syntax error: line 9 syntax error  token: p")
; dropping the remaining commands with exit status 0. One answer went
; missing without a diagnostic.
;
; The same retention made every later solve re-conjoin the constraint
; bundle of every equality ever built: 640 popped-and-discarded array
; equalities followed by one trivial query took 34s, and 0.13s once the
; records are made solve-local.
(set-logic QF_ABV)
(push 1)
(declare-fun p () (Array (_ BitVec 4) (_ BitVec 8)))
(declare-fun r () (Array (_ BitVec 4) (_ BitVec 8)))
(assert (= p r))
(check-sat)
(pop 1)
(declare-fun p () (_ BitVec 8))
(assert (= p #x01))
(check-sat)
