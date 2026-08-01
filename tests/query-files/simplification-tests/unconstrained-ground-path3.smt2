; RUN: %solver %s | %OutputCheck %s
; CHECK: ^unsat
(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status unsat)

; The ground-path collapse back-propagates the predicate's constant down
; the chain to seed its samples. Here that walks all-ones into the
; squaring step, whose heuristic preimage is an integer square root, and
; isqrt64(2^64-1) overflowed its Newton seed to zero and then divided by
; it -- a SIGFPE during RemoveUnconstrained, before any decision was made.
;
; The shift is load-bearing: topLevel_other skips a variable whose
; sibling is the variable itself, so (bvmul x x) alone never reaches the
; collapse, and a shift by a constant has no per-kind rule of its own.
; The width must be exactly 64 for the back-propagated value to be the
; UINT64_MAX that overflows.
(declare-fun x () (_ BitVec 64))
(assert (= (bvmul (bvlshr x #x0000000000000001) (bvlshr x #x0000000000000001)) #xffffffffffffffff))

; Same crash reached with the constant back-propagated rather than
; written out: bvnot maps 0 to all-ones on the way down the chain.
(declare-fun y () (_ BitVec 64))
(assert (bvule (bvnot (bvmul (bvudiv y #x0000000000000003) (bvudiv y #x0000000000000003))) #x0000000000000000))

; Unsat either way: a square is 0 or 1 mod 4, never 3.
(check-sat)
(exit)
