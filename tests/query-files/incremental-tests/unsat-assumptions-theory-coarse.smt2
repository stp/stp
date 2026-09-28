; A refutation that used a theory lemma reports every assumption, not the
; subset that happened to fail.
;
; UF and array-equality rounds ride one block literal, and that literal is
; assumed without being recorded against any level -- it has no level to be
; recorded against. Asking the backend which assumptions failed would then
; name it, and every accessor drops a failed literal it cannot attribute, so
; the reported core would come back a strict *subset* of a real one. A core
; that is too small is not a smaller answer, it is a wrong one: the frontend
; caches "unsat at the deepest level in the core" and would go on answering
; unsat for a level that is satisfiable.
;
; So these rounds record coarsely, which reports the whole assumption set --
; always a correct core. Compare unsat-assumptions.smt2, where the same shape
; without a theory lemma drops the irrelevant assumption. The recording call
; itself now re-establishes this rather than trusting the routing: a granular
; record whose assumptions are not all attributable is downgraded.
;
; RUN: %solver --incremental --uninterpreted-functions %s | %OutputCheck %s
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun p () Bool)
(assert (= x y))
(check-sat-assuming ((distinct (f x) (f y)) p))
; CHECK: ^unsat
(get-unsat-assumptions)
; CHECK: ^\(.*\|p\|.*\)$
