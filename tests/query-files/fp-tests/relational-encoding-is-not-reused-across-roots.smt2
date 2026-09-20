; A relational encoding mints fresh inputs and constrains them only through
; the relation it conjoins into the root it was minted under. BBTermMemo
; outlives a root, so without a per-root clear the second check-sat below
; gets the cached square root back with nothing constraining its (q, r) --
; free to take any value, and the query comes back sat.
;
; The fp-native-domain path clears the term memos on a root change for its
; own reasons, which is why this was only reachable with that flag off. One
; rounding mode is enough: nothing here needs two.
;
; RUN: %solver --incremental --bb.fp-native-domain=0 --bb.fp-native-sqrt=true %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --bb.fp-native-domain=1 --bb.fp-native-sqrt=true %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental --bb.fp-native-domain=0 --bb.fp-native-sqrt=false %s 2>&1 | %OutputCheck %s
;
; CHECK: ^sat
; CHECK-NEXT: ^unsat
;
(set-logic QF_FP)
(set-option :incremental true)
(declare-fun x () Float32)
(push 1)
(assert (fp.lt (fp.sqrt RNE x) ((_ to_fp 8 24) RNE 100.0)))
(check-sat)
(pop 1)
(push 1)
; the same root, under a root that never received its relation
(assert (= x ((_ to_fp 8 24) RNE 4.0)))
(assert (not (= (fp.sqrt RNE x) ((_ to_fp 8 24) RNE 2.0))))
(check-sat)
(exit)
