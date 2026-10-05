; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; Over an index sort small enough for the stores to cover half of it, the
; canonical form takes the most frequent cell value as the default, a tie
; going to the value with the smaller bits. Two different
; canonical constant arrays are folded to unequal, which is only sound
; because of that: without it, two forms of one array would differ.
; Without simplification nothing is normalised, the fold refuses forms it
; did not check, and the array-equality procedure decides each case.
(set-logic QF_ABV)
; Both cells #x07: the constant array #x07.
(push 1)
(assert (not (= (store (store ((as const (Array (_ BitVec 1) (_ BitVec 8))) #x00) #b0 #x07) #b1 #x07)
                ((as const (Array (_ BitVec 1) (_ BitVec 8))) #x07))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; Two cells #x07 and two #x00 over a two-bit index: a tie, so the default
; is #x00 however the array is spelled.
(push 1)
(assert (not (= (store (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x00) #b00 #x07) #b01 #x07)
                (store (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x07) #b10 #x00) #b11 #x00))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; Three of four cells #x07: the default becomes #x07.
(push 1)
(assert (not (= (store (store (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x00) #b00 #x07) #b01 #x07) #b10 #x07)
                (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x07) #b11 #x00))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; Different arrays.
(push 1)
(assert (= (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x00) #b00 #x07)
           (store ((as const (Array (_ BitVec 2) (_ BitVec 8))) #x00) #b01 #x07)))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; Boolean cells, every one true.
(push 1)
(assert (not (= (store (store ((as const (Array (_ BitVec 1) Bool)) false) #b0 true) #b1 true)
                ((as const (Array (_ BitVec 1) Bool)) true))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
; A Boolean index.
(push 1)
(assert (not (= (store (store ((as const (Array Bool (_ BitVec 8))) #x00) false #x07) true #x07)
                ((as const (Array Bool (_ BitVec 8))) #x07))))
; CHECK: ^unsat$
(check-sat)
(pop 1)
