; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^unsat
; A store over a constant array: the written cell reads the written value and
; every other cell reads the default.
(set-logic QF_ABV)
(declare-fun i () (_ BitVec 8))
(assert (or (not (= (select (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) #x05 #x2a) #x05) #x2a))
            (and (not (= i #x05))
                 (not (= (select (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) #x05 #x2a) i) #x00)))))
(check-sat)
