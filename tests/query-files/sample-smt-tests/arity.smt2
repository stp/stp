; RUN: %solver %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
; CHECK-NEXT: ^sat
(set-info :status sat)

; Test that operations with :left-assoc, :right-assoc, and :chainable are implemented.

; These operations are marked as :left-assoc (left associative),
; but are associative. 
; Check that three operands are handled properly.

(assert (= (bvadd #x1 #x2 #x3  ) #x6 ))
(assert (= (bvmul #x2 #x2 #x3  ) #xC ))
(assert (= (bvxor #x2 #x2 #x1  ) #x1 ))
(assert (= (bvor  #x2 #x2 #x3  ) #x3 ))
(assert (= (bvand #x2 #x2 #x3  ) #x2 ))

(assert (= (or true true false ) true ))
(assert (= (and true true true true ) true ))
(assert (= (xor true true true true ) false ))

; bvxnor is the complement of bvxor. 

(assert (= (bvxnor #b0011 #b0101 ) (bvnot (bvxor #b0011 #b0101))))

; Implies is special because it's marked as :right-assoc,
; but isn't associative. 
(assert (= (=> false false false ) (=> false (=> false false))))

; Check only solution of {a=true, b=true, c=false} is produced.
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (not (=> a b c)))
(assert (not (=> b c)))
(assert (not (=> a c)))

; Equals is chainable.
(assert (= (= #x1 #x1 #x1) (= #x2 #x2 #x2) (= #x3 #x3 #x3)))
(assert (= (= false false true) (= false false true) (= true false false) (= true true false) (= true false false) (= false true false)))
(assert (= (= true true true) (= false false false)))

(check-sat)
