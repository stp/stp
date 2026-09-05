; ede9d4bd taught both counterexample walks to evaluate a term that *contains*
; an application. That reached the C API, which evaluates whatever term it is
; handed, but not (get-value ...), whose own argument filter still demanded a
; bare symbol or a bare application. The evaluator could answer these; the
; command would not ask. Now it does.
;
; The last row is the one worth having: f(#x07) is a durable node the solve
; never reached, so it has no certified value of its own and (get-value
; ((f #x07))) is still refused at the root. Inside a term it must complete
; through the certified seed and agree with f(x), because x is pinned to 7 and
; equal argument tuples give equal results.
;
; RUN: %solver --uninterpreted-functions --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on %s 2>&1 | %OutputCheck %s
;
; Terms echo as STP's interned nodes, so commutative operands come back in
; STP's canonical order rather than as written.
;
; CHECK: ^sat
; CHECK-L: ( (|f| |x|)  #x03 )
; CHECK-L: ( (bvadd  #x01 (|f| |x|))  #x04 )
; CHECK-L: ( (= (|f| |x|)  #x03) true )
; CHECK-L: ( (|g| |p|) true )
; CHECK-L: ( (not (|g| |p|)) false )
; CHECK-L: ( (and |q| (|g| |p|)) true )
; CHECK-L: ( (= (|k| |x|) RTZ) true )
; CHECK-L: ( (bvadd  #x01 (|f|  #x07))  #x04 )
; CHECK: REACHED-END
;
(set-option :produce-models true)
(set-logic QF_UFBVFP)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-fun g (Bool) Bool)
(declare-fun k ((_ BitVec 8)) RoundingMode)
(declare-const x (_ BitVec 8))
(declare-const p Bool)
(declare-const q Bool)
(assert (= x #x07))
(assert (= (f x) #x03))
(assert (= (k x) RTZ))
(assert (g p))
(assert q)
(check-sat)
(get-value ((f x)))
(get-value ((bvadd (f x) #x01)))
(get-value ((= (f x) #x03)))
(get-value ((g p)))
(get-value ((not (g p))))
(get-value ((and (g p) q)))
(get-value ((= (k x) RTZ)))
(get-value ((bvadd (f #x07) #x01)))
(echo "REACHED-END")
