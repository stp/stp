; (get-value (t1 ... tn)) answers ((t1 v1) ... (tn vn)) for any well-sorted
; terms, not only for variables. STP used to accept a bare symbol and answer
; "unsupported" for everything else, so no query could read the model value of
; an expression it had actually written.
;
; The model evaluator already decides all of these -- get-value simply refused
; to ask it. Each row below is a shape the evaluator handles: an arithmetic
; term, a predicate, an array read, an if-then-else, a compound floating-point
; term and a compound rounding-mode term. Values are pinned by construction so
; the output is deterministic.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
;
; The first half of each pair is STP's node for the term, not the text that
; was written: hash-consing and rewriting happen in the node factory as the
; parser builds each term, so the input spelling is gone before anything can
; be asked about it. Commutative operands come back in canonical order, a
; rewritten term comes back rewritten, and a folded term comes back as the
; constant it folded to -- see the (bvadd #x01 #x01) row below. Pairs are
; therefore matched positionally, response i to term i, which is what SMT-LIB
; asks of a caller; they cannot be matched by spelling.
;
; A term is echoed through the letizing printer, so a shared subterm is
; printed once. The chain of define-funs at the end builds a node whose tree
; expansion is exponential in the chain length; it must come back as a `let`.
;
; CHECK: ^sat
; CHECK-L: ( |x|  #x2A )
; CHECK-L: ( |p| true )
; CHECK-L: ( (bvadd  #x01 |x|)  #x2B )
; CHECK-L: ( (= |x|  #x2A) true )
; CHECK-L: ( (= |x|  #x00) false )
; CHECK-L: ( (select |a|  #x00)  #x07 )
; CHECK-L: ( (ite |p| |x|  #x00)  #x2A )
; A constant-folded query keeps its answer but loses its spelling.
; CHECK-L: (  #x02  #x02 )
; CHECK-L: ( |f| (fp #b0 #b10000000 #b10000000000000000000000) )
; CHECK-L: ( (fp.add RNE |f| |f|) (fp #b0 #b10000001 #b10000000000000000000000) )
; A floating-point predicate is a Boolean, and answers like one.
; CHECK-L: ( (fp.isNaN |f|) false )
; CHECK-L: ( |r| RTZ )
; A rounding-mode-sorted expression prints a mode name, not its bit carrier.
; CHECK-L: ( (ite |p| RTZ RNE) RTZ )
; CHECK-L: ( (fp.mul |r| |f| |f|) (fp #b0 #b10000010 #b00100000000000000000000) )
; A single command answers every term it was given, in the order asked.
; CHECK-L: ( |x|  #x2A )
; CHECK-L: ( (bvnot |x|)  #xD5 )
; CHECK-L: ( |p| true )
; A shared subterm is bound once rather than expanded at each use.
; CHECK: \(let \(\(\|\?let_k_0\|.*  #x05 \)
; An array has no SMT-LIB2 value spelling here; (get-model) prints the
; completed interpretation instead. It is refused, not evaluated -- reaching
; the Boolean branch of the printer with an array used to abort the process,
; in the default configuration.
; CHECK-L: unsupported
; CHECK: REACHED-END
;
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(declare-const p Bool)
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const f (_ FloatingPoint 8 24))
(declare-const r RoundingMode)
(define-fun g0 () (_ BitVec 8) x)
(define-fun g1 () (_ BitVec 8) (bvxor (bvand g0 x) (bvor g0 #x0f)))
(define-fun g2 () (_ BitVec 8) (bvxor (bvand g1 x) (bvor g1 #x0f)))
(define-fun g3 () (_ BitVec 8) (bvxor (bvand g2 x) (bvor g2 #x0f)))
(assert (= x #x2a))
(assert p)
(assert (= (select a #x00) #x07))
(assert (= f (fp #b0 #b10000000 #b10000000000000000000000)))
(assert (= r RTZ))
(check-sat)
(get-value (x))
(get-value (p))
(get-value ((bvadd x #x01)))
(get-value ((= x #x2a)))
(get-value ((= x #x00)))
(get-value ((select a #x00)))
(get-value ((ite p x #x00)))
(get-value ((bvadd #x01 #x01)))
(get-value (f))
(get-value ((fp.add RNE f f)))
(get-value ((fp.isNaN f)))
(get-value (r))
(get-value ((ite p RTZ RNE)))
(get-value ((fp.mul r f f)))
(get-value (x (bvnot x) p))
(get-value (g3))
(get-value (a))
(echo "REACHED-END")
