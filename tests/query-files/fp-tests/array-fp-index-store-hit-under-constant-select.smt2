; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; A select at a *constant* NaN over a store at a symbolic NaN index, with the
; underlying cell pinned to a different value so the checker cannot agree by
; accident.
;
; The model evaluator used to decide whether to encode an array access by
; looking at that access's own index: a constant index is already canonical,
; so it declined. But the access here is a read over a write, and it is the
; *write's* index that needs canonicalising. Declining sent the read down the
; raw-carrier path, where x resolves to whichever NaN payload the SAT solver
; picked while the solve compared pack(unpack(x)) -- so the checker decided
; the write did not hit, read the pinned cell instead, and aborted the whole
; query with "counterexample bogus" on a satisfiable input.
;
; :produce-models is what runs the counterexample checker, and the pinned cell
; is what makes the checker resolve the write rather than agree either way;
; array-fp-index-store-hit-model.smt2 has neither and so cannot catch this.
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-fun a () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun x () (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (= (select (store a x #x01) (_ NaN 8 24)) #x01))
(assert (= (select a (_ NaN 8 24)) #x02))
(check-sat)
