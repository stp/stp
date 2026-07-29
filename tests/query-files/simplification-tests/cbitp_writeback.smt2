; Constant bit propagation derives from the second assert that the
; bvadd/extract/concat chain is constant, making the multiplier #xFFFFFFFE.
; Writing those constants back lets the word-level simplifications collapse
; the query to false: x + x*#xFFFFFFFE = -x, the double negation cancels,
; and the third assert becomes (not (= x x)).
; RUN: %solver --exit-after-CNF %s | %OutputCheck %s
(set-logic QF_BV)
(set-info :status unsat)

(declare-fun x () (_ BitVec 32))

(assert (not (bvsgt #x00000000 x)))
(assert (= ((_ extract 31 31) x) #b0))
(assert (not (= x (bvneg (bvadd x (bvmul x (concat ((_ extract 31 1)
    (bvadd #xFFFFFFFF (concat (_ bv0 31) ((_ extract 31 31) x)))) #b0)))))))
(assert (= #b1111111111111111111111111111111 ((_ extract 31 1)
    (bvadd #xFFFFFFFF (concat (_ bv0 31) ((_ extract 31 31) x))))))

; CHECK-NEXT: ^unsat
(check-sat)
(exit)
