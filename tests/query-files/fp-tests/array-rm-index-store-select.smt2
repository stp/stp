; RUN: %solver %s | %OutputCheck %s
;
; RoundingMode as the index sort: the five modes name five cells, and
; store/select congruence works over them -- a select at the stored mode
; returns the stored value, and a select of the array's cell at a mode
; equal to a RoundingMode variable follows that variable. The mode
; encodings are one-hot and every RoundingMode term is pinned to them, so
; bit-level index equality coincides with the sort's '='.
(set-logic QF_ABVFP)
(declare-fun a () (Array RoundingMode (_ BitVec 8)))
(declare-const r RoundingMode)
(assert (= r RNE))
(assert (distinct (select (store a RNE #x11) r) #x11))
; CHECK: ^unsat
(check-sat)
