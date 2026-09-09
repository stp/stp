; Every fact the pre-lowering rewrite uses is kept as the definition of the
; symbol it was used on, so a satisfiable query still has a model in which
; those symbols carry the values the query gave them, and (f x) is read back
; through the certified function model rather than through a symbol the
; rewrite removed. --check-sanity replays the parsed assertions against the
; published model and fails loudly if any of them evaluates to false.
;
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --check-sanity --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat$
; CHECK-L: ( |x|  #x05 )
; CHECK-L: ( |y|  #x05 )
; CHECK-L: ( (|f| |x|)  #x2A )
; CHECK-L: ( (|f| |y|)  #x2A )
; CHECK-L: ( |a|  #x2A )
;
; EXPECT: sat
(set-logic QF_UFBV)
(set-option :produce-models true)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(assert (= x #x05))
(assert (= y x))
(assert (= a (f x)))
(assert (= (f y) #x2a))
(assert (= b (bvadd a #x01)))
(check-sat)
(get-value (x))
(get-value (y))
(get-value ((f x)))
(get-value ((f y)))
(get-value (a))
