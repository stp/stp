; RoundingMode on both sides of the UF boundary at once, including one
; application used as another's actual, read back through a model and
; replayed against the raw stack.
;
; The interesting node is (f (k x)): the inner application's result is an
; introduced RoundingMode symbol, and it is the outer application's argument
; tuple. If it were not pinned, the outer function would be interpreted at a
; "mode" that is not one, and the printed define-fun would not be a term.
;
; --check-sanity replays every certified model against the raw stack, so a
; disagreement between the interpretation printed here and the one used to
; satisfy the assertions is a failure rather than something to notice by eye.
;
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=off --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --uf-ackermann=on --incremental=on %s 2>&1 | %OutputCheck %s
;
; -p prints the counterexample through its own path rather than through
; (get-model), so it is a second place a RoundingMode value could come out as
; its carrier. Everything below has to hold there too.
; RUN: %solver --uninterpreted-functions -p --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions -p --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK: define-fun \|r\| \(\) RoundingMode (RNE|RTZ|RTP|RTN|RNA)\)$
; CHECK: define-fun \|f\| \(\(x0 RoundingMode\)\) \(_ BitVec 4\)
; CHECK: define-fun \|k\| \(\(x0 \(_ BitVec 4\)\)\) RoundingMode
; CHECK: \( \(\|k\| \|x\|\) RTP \)
; CHECK: \( \(\|f\| \|r\|\)  #x5 \)
; CHECK: \( \(\|f\| \(\|k\| \|x\|\)\)  #x3 \)
; CHECK: REACHED-END
;
(set-logic QF_UFBVFP)
(set-option :produce-models true)
(declare-fun k ((_ BitVec 4)) RoundingMode)
(declare-fun f (RoundingMode) (_ BitVec 4))
(declare-const x (_ BitVec 4))
(declare-const r RoundingMode)
(assert (= (k x) RTP))
(assert (= (f r) #x5))
(assert (= (f (k x)) #x3))
(check-sat)
(get-model)
(get-value ((k x) (f r) (f (k x))))
(echo "REACHED-END")
