; A RoundingMode value is published as a mode name, never as its raw 5-bit
; carrier: in the generated define-fun's signature, in its case values, in
; its else branch, and in the answer get-value gives for the application.
;
; The else branch is UFConcreteValue::zero of the codomain. All-zeros is not
; a one-hot mode and denotes nothing, so a defaulted RoundingMode case has to
; name a legal mode -- RNE -- rather than print a carrier that is not a term
; of the sort at all.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: define-fun \|k\| \(\(x0 \(_ BitVec 8\)\)\) RoundingMode
; CHECK: \(ite \(= x0  #x01\) RTZ RNE\)
; CHECK: \( \(\|k\| \|x\|\) RTZ \)
; CHECK: REACHED-END
; CHECK-NOT: #b00000
;
(set-option :produce-models true)
(set-logic QF_UFBVFP)
(declare-fun k ((_ BitVec 8)) RoundingMode)
(declare-const x (_ BitVec 8))
(assert (= x #x01))
(assert (= (k x) RTZ))
(check-sat)
(get-model)
(get-value ((k x)))
(echo "REACHED-END")
