; (get-value (t1 ... tn)) answers ((t1 v1) ... (tn vn)) with each ti as the
; script spelled it (SMT-LIB 2.6, 4.2.6). STP used to print its own node for
; the term, and the node factory rewrites as the parser builds: (bvadd v v)
; came back as (bvmul #b000010 |v|), (bvsub v v) as a bare constant with no
; term at all, and (not (not p)) as |p| -- indistinguishable from the answer
; to p itself in the same command. A client could not attribute a value to
; its request except by position (issue #1288).
;
; No node can reproduce the request -- NOT(NOT x) cannot exist as a node --
; so the lexer keeps the text of each term and the response echoes that.
; Whitespace inside a term is normalised to single spaces and comments are
; dropped; quoted symbols, indexed identifiers and annotations come back as
; written.
;
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --incremental=on %s 2>&1 | %OutputCheck %s
; RUN: %solver --disable-simplifications %s 2>&1 | %OutputCheck %s
;
; CHECK: ^sat
; CHECK-NEXT-L: (
; CHECK-NEXT-L: ((bvadd v v) #b111110)
; CHECK-NEXT-L: ((bvsub v v) #b000000)
; CHECK-NEXT-L: ((not (not p)) true)
; CHECK-NEXT-L: ((concat ((_ extract 5 3) v) ((_ extract 2 0) v)) #b111111)
; CHECK-NEXT-L: )
; Two requests with the same value and the same node stay distinguishable.
; CHECK-NEXT-L: (
; CHECK-NEXT-L: (p true)
; CHECK-NEXT-L: ((not (not p)) true)
; CHECK-NEXT-L: )
; Layout inside the list is not echoed: a newline and a comment inside a term
; vanish, runs of spaces collapse. Bars and indexed identifiers are kept.
; CHECK-NEXT-L: (
; CHECK-NEXT-L: ((bvadd v v) #b111110)
; CHECK-NEXT-L: (|v| #b111111)
; CHECK-NEXT-L: ((_ bv1 6) #b000001)
; CHECK-NEXT-L: ((! v :named nm) #b111111)
; CHECK-NEXT-L: ((bvand v (bvnot v)) #b000000)
; CHECK-NEXT-L: )
; A define-fun alias is echoed as the alias, not its body.
; CHECK-NEXT-L: (
; CHECK-NEXT-L: (twice #b111110)
; CHECK-NEXT-L: ((twice) #b111110)
; CHECK-NEXT-L: )
; The command after a get-value list parses as before.
; CHECK-NEXT-L: "REACHED-END"
;
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun p () Bool)
(declare-fun v () (_ BitVec 6))
(define-fun twice () (_ BitVec 6) (bvadd v v))
(assert p)
(assert (= v #b111111))
(check-sat)
(get-value ((bvadd v v) (bvsub v v) (not (not p)) (concat ((_ extract 5 3) v) ((_ extract 2 0) v))))
(get-value (p (not (not p))))
(get-value (   (bvadd   v ; a comment inside the term
   v)   |v|  (_ bv1 6) (! v :named nm)
   (bvand    v    (bvnot v)) ))
(get-value (twice (twice)))
(echo "REACHED-END")
