; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-L: (define-fun |c| () (_ BitVec 8) #xFE)
; CHECK-L: (define-fun |n| () (_ BitVec 32) #x0000000D)
; The other branch of the sample-cvc a127/a163 family: n is in [12,16) and
; its low two bits, decremented once, are zero, which leaves 13 as the only
; value.  c is pinned through a widen-narrow-widen round trip, so the model
; also checks that the redundant extract of a concatenation survives.
; Replaces a164/a172/a174/a177-a180.
(set-logic QF_BV)
(set-option :produce-models true)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)
(declare-fun n () (_ BitVec 32))
(declare-fun c () (_ BitVec 8))
(assert (= (concat #x000000 ((_ extract 7 0) (concat #x000000 c))) #x000000FE))
(assert (bvult n #x00000010))
(assert (not (bvult n #x0000000C)))
(assert (not (= (bvand n #x00000003) #x00000000)))
(assert (= (bvadd (bvand n #x00000003) (bvneg #x00000001)) #x00000000))
(check-sat)
(get-model)
