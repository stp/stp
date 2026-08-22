; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: define-fun \|f\| \(\(x0 \(_ BitVec 8\)\)\) \(_ BitVec 8\)
; CHECK-NOT: ite
; CHECK: #x2A
; CHECK: \( \(\|f\| \(bvadd \|x\| \|y\|\)\)  #x2A \)
;
; f has one application, so no congruence lemma can ever equate its actual
; with anything and the compound argument needs no name. Without a name the
; addition leaves the formula entirely, and the certified interpretation is
; the constant the result took -- total, and in agreement with the single
; application, which is all any interpretation of f has to satisfy. The
; durable handle still answers get-value from that same certified result.
(set-logic QF_UFBV)
(set-option :produce-models true)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (= (f (bvadd x y)) #x2a))
(check-sat)
(get-model)
(get-value ((f (bvadd x y))))
