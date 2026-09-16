; Distributing a constant over a sum writes one addend where there was one
; before, so a combination over many atoms can cost more to say than it
; saves. The limit is what bounds that, and a combination above it keeps the
; spelling it arrived with.
;
; Zero puts every combination above the limit, so nothing is rewritten and
; the query reaches the same answer through the terms it was given.
; RUN: %solver -s --linear-form=1 --linear-form-addend-limit=0 %s 2>&1 | %OutputCheck %s
; CHECK: Terms given a canonical form:0
; CHECK: ^unsat$
;
; The same query with the limit out of the way.
; RUN: %solver -s --linear-form=1 %s 2>&1 | %OutputCheck --check-prefix=ON %s
; ON: Terms given a canonical form:[1-9]
; ON: ^unsat$
(set-logic QF_BV)
(declare-fun p () (_ BitVec 32))
(declare-fun q () (_ BitVec 32))
(declare-fun r () (_ BitVec 32))
(assert
  (not (=
    (bvudiv (bvadd (bvmul (_ bv5 32) p) (bvadd q (bvmul (_ bv4294967295 32) r))) (_ bv7 32))
    (bvudiv (bvadd (bvmul (_ bv4294967295 32) r) (bvadd (bvmul (_ bv5 32) p) q)) (_ bv7 32)))))
(check-sat)
(exit)
