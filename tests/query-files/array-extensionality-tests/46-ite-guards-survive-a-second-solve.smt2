; RUN: %solver --array-equality %s | %OutputCheck %s
; CHECK: ^sat
; CHECK: ^unsat
; Unsat by cases on p: c is a if p and b otherwise, and both are
; asserted to differ from c at i. The bvmul/bvult constraints are
; satisfiable on their own and do nothing but keep preprocessing from
; taking the shortcut that hides the defect.
;
; Historically, the array if-then-else was eliminated into a fresh array d
; defined by
; c -> d = a and not(c) -> d = b, and d is cached across solves so a
; repeated solve reuses it and its two equality records. The guards
; were not cached with it: they were emitted only for if-then-elses the
; elimination loop rediscovered in the formula, and on the second solve
; the witness anchor -- pushed down into the if-then-else by the
; simplifier -- recovers through that cache straight to d, a SYMBOL,
; which can never appear in coneITEs. The loop exited immediately, d
; kept its records but lost its definition, and both proxies became
; free Booleans: this query answered sat.
;
; Splitting the assertions across the two check-sat commands is the
; whole point. 17-repeated-checksat-ite.smt2 asserts everything before
; the first one and re-runs it, which never re-prepares and so never
; exercises this at all.
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun b () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun c () (Array (_ BitVec 2) (_ BitVec 2)))
(declare-fun p () Bool)
(declare-fun i () (_ BitVec 2))
(declare-fun u () (_ BitVec 16))
(declare-fun w () (_ BitVec 16))
(declare-fun z () (_ BitVec 32))
(assert (= (ite p a b) c))
(check-sat)
(assert (= z (bvmul ((_ zero_extend 16) u) ((_ zero_extend 16) w))))
(assert (bvult ((_ extract 1 0) z) i))
(assert (distinct (select a i) (select c i)))
(assert (distinct (select b i) (select c i)))
(check-sat)
