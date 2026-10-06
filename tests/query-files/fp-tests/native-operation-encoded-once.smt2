; A floating-point operation is encoded one way: natively, or by SymFPU,
; never both. The lowering keeps an operation for its native circuit when a
; native consumer reaches it -- here fp.to_ieee_bv, which wraps every float
; array index -- and builds it in SymFPU for any other consumer, such as a
; stored value. A term that both reach was encoded twice: two circuits for
; one value, with nothing tying them together. In a Murxla query 13 Float32
; fp.rem terms encoded both ways cost 1.6M clauses and took a refutation
; from 30 seconds to past 15 minutes.
;
; r is reached first as an index, so its stored value reads the native
; circuit's bits. s is stored first, so SymFPU builds it, and the index
; that reaches it afterwards takes SymFPU's result instead of a second,
; native, remainder. Each fp.rem is now one circuit: one SymFPU operation
; and one native relation, where there were two of each.
;
; RUN: %solver -s %s 2>&1 | %OutputCheck %s
; RUN: %solver -d %s 2>&1 | %OutputCheck --check-prefix=MODEL %s
;
; CHECK: FloatBlast: 1 SymFPU operations, .* 1 native circuits read by SymFPU, 1 native consumers sent to SymFPU
; CHECK: fp-native: relational encodings minted: 1$
; CHECK: ^sat
; MODEL: ^sat
(set-logic QF_ABVFP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(declare-const a (Array (_ FloatingPoint 8 24) (_ FloatingPoint 8 24)))
(declare-const b (Array (_ FloatingPoint 8 24) (_ FloatingPoint 8 24)))
(declare-const c (Array (_ FloatingPoint 8 24) (_ FloatingPoint 8 24)))
(declare-const d (Array (_ FloatingPoint 8 24) (_ FloatingPoint 8 24)))
(define-fun r () (_ FloatingPoint 8 24) (fp.rem x y))
(define-fun s () (_ FloatingPoint 8 24) (fp.rem y z))
(assert (= (store a r r) b))
(assert (not (= (select b x) (select a x))))
(assert (= (store c z s) (store d s x)))
(check-sat)
(exit)
