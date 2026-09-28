; get-value answers an application the solve never reached, with the value the
; published interpretation gives it.
;
; The model a check-sat leaves behind is total: (get-model) prints a define-fun
; with an else branch, and that branch is what f takes at every argument the
; query did not mention. get-value used to refuse exactly those points while
; the model printed them, and -- worse -- while the same command list answered
; them whenever the application sat inside a larger term, because a nested
; application goes through the model evaluator and is completed there. The two
; halves of one command disagreed.
;
; An application the solve DID reach still answers with its certified value,
; which is the exact one, not the completion.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^\($
; CHECK-NEXT: ^\( \(\|f\| \|x\|\)  #x03 \)$
; CHECK-NEXT: ^\)$
; CHECK-NEXT: ^\($
; CHECK-NEXT: ^\( \(\|f\|  #xEE\)  #x00 \)$
; CHECK-NEXT: ^\)$
; A mixed list is one command and answers as one.
; CHECK-NEXT: ^\($
; CHECK-NEXT: ^\( \(\|f\| \|x\|\)  #x03 \)$
; CHECK-NEXT: ^\( \(\|f\|  #xEE\)  #x00 \)$
; CHECK-NEXT: ^\)$
; The completion agrees with the term path, which is what used to differ.
; CHECK-NEXT: ^\($
; CHECK-NEXT: ^\( \(bvadd  #x01 \(\|f\|  #xEE\)\)  #x01 \)$
; CHECK-NEXT: ^\)$
; An assertion invalidates the model, and then there is genuinely nothing to
; answer from -- the generic refusal, as before uninterpreted functions.
; CHECK-NEXT: ^unsupported$
; CHECK-NEXT: ^"REACHED-END"$
;
(set-option :produce-models true)
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(assert (= (f x) #x03))
(check-sat)
(get-value ((f x)))
(get-value ((f #xee)))
(get-value ((f x) (f #xee)))
(get-value ((bvadd (f #xee) #x01)))
(assert (= x #x01))
(get-value ((f #xee)))
(echo "REACHED-END")
(exit)
