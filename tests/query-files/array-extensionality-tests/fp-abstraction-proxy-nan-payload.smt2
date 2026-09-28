; RUN: %solver -d --cadical --array-equality --fp-abstraction=1 --uf-bv-term-abstraction=on --bv-abstraction-width=8 --size-reducing-only --array-ackermann-budget=0 %s | %OutputCheck %s
; CHECK-NEXT: ^sat
; Reduced from a fuzzer failure. The floating-point abstraction replaces v
; by the float view of a packed proxy, so the value stored in a5 names the
; proxy's bits, NaN payload included, while the model's value of the view
; is the canonical NaN. Both are the one NaN value, so the array-equality
; checker must not stop with "a scalar name disagrees with its term".
(set-logic QF_ABVFP)
(declare-fun v () Float64)
(declare-fun a5 () (Array Float64 Float64))
(declare-fun a53 () (Array (_ BitVec 14) (_ BitVec 6)))
(declare-fun a () (Array Float64 (_ BitVec 2)))
(assert
  (ite (= (_ +zero 11 53) (select (store a5 v v) (_ +zero 11 53)))
       (ite (= (store a53 #b00000000000000 #b000000)
               (store a53 ((_ zero_extend 12) (select a (_ +zero 11 53)))
                      (select a53 #b00000000000000)))
            false
            (not (fp.isNormal (fp.sqrt RNE v))))
       false))
(check-sat)
