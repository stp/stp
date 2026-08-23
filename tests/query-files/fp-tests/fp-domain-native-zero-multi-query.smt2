; Zero-domain assumptions are solve-local and must be recollected as the root
; changes. Check the same push/pop sequence in batch rebuilds, the persistent
; incremental driver, and the ordinary SymFPU encoding.
;
; RUN: %solver --incremental=off --bb.fp-native-arith=1 --fp-domain-simplify=1 --fp-domain-sound-zero-facts=1 --bb.fp-native-domain=1 %s | %OutputCheck --check-prefix=NATIVE %s
; RUN: %solver --incremental=on --bb.fp-native-arith=1 --fp-domain-simplify=1 --fp-domain-sound-zero-facts=1 --bb.fp-native-domain=1 %s | %OutputCheck --check-prefix=NATIVE %s
; RUN: %solver --incremental=off --bb.fp-native-cmp=false %s | %OutputCheck --check-prefix=SYMFPU %s
;
; NATIVE: ^sat
; NATIVE: ^unsat
; NATIVE: ^unsat
; NATIVE: ^sat
; SYMFPU: ^sat
; SYMFPU: ^unsat
; SYMFPU: ^unsat
; SYMFPU: ^sat
;
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(declare-fun n () (_ FloatingPoint 8 24))

(assert (fp.leq (_ +zero 8 24) x))
(assert (fp.leq x (fp #b0 #x80 #b00000000000000000000000)))
(assert (fp.leq (_ +zero 8 24) y))
(assert (fp.leq y (fp #b0 #x80 #b00000000000000000000000)))
(assert (fp.leq (_ +zero 8 24) n))
(assert (fp.leq n (fp #b0 #x80 #b00000000000000000000000)))
(assert (fp.eq (fp.add RNE x y) (_ +zero 8 24)))
(check-sat)

(push 1)
(assert (not (fp.eq (fp.add RTP x n) n)))
(check-sat)
(pop 1)

(push 1)
(assert
  (not
    (fp.isZero
      (fp.mul RTN x (fp #b1 #x80 #b00000000000000000000000)))))
(check-sat)
(pop 1)

(check-sat)
(exit)
