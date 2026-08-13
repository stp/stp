; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
;
; A signed remainder written out as a - (a sdiv b) * b must be folded back
; into a srem b, and a remainder divided by its own divisor must fold to zero.
;
; This is the shape a translation-validation tool emits for the LLVM identity
; (x - (x sdiv 101) * 101) sdiv 101 == 0: the front end has no bvsrem in it,
; so without the two rewrites the query holds three independent signed
; divisions, each of which is bit-blasted into its own divider. Narrowed from
; 64 bits, where the un-rewritten form runs for minutes, to 24 bits, where it
; takes seconds -- enough to be conspicuous if either rewrite stops firing,
; but bounded if it does.
(set-logic QF_BV)
(declare-fun %p0 () (_ BitVec 24))
(declare-fun np_%p0 () Bool)
(declare-fun isundef_%p0 () (_ BitVec 1))
(assert
 (let ((?x26 (bvadd (bvmul (_ bv33554431 25) ((_ sign_extend 1) (bvmul (_ bv101 24) (bvsdiv %p0 (_ bv101 24))))) ((_ sign_extend 1) %p0))))
(let (($x20 (= (bvmul (_ bv101 48) ((_ sign_extend 24) (bvsdiv %p0 (_ bv101 24)))) ((_ sign_extend 24) (bvmul (_ bv101 24) (bvsdiv %p0 (_ bv101 24)))))))
(let (($x22 (and np_%p0 $x20)))
(let (($x33 (and (and np_%p0 $x22) (= ?x26 ((_ sign_extend 1) (bvadd %p0 (bvmul (_ bv16777115 24) (bvsdiv %p0 (_ bv101 24)))))))))
(let (($x39 (or (not $x33) (= (_ bv0 24) (bvsdiv (bvadd %p0 (bvmul (_ bv16777115 24) (bvsdiv %p0 (_ bv101 24)))) (_ bv101 24))))))
(let (($x41 (not $x39)))
(let (($x12 (= (_ bv0 1) isundef_%p0)))
(and $x12 $x41)))))))))
(check-sat)
