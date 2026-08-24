; An abstracted multiply is refined with a fact about every pair of operands,
; not only by ruling out the pair the candidate holds.
;
; A blocking lemma excludes one point of a 2^(2W) space. At the default width
; floor that is one of 2^128 pairs, so a multiplication the search has to work
; through can need more rounds than there are operands to enumerate -- which
; is why the refinement gives up after a bounded number of them and encodes
; the operation exactly instead. The schemas are the other way out: each says
; something true of every pair, so each rules out a slice.
;
;   the low bit          t[0] = a[0] & b[0]
;   the trailing zeros   t[i] holds only if some bit of the operand at or
;                        below i does
;   a power of two       a = 2^k -> t = b << k
;   its negation         a = -2^k -> t = (-b) << k
;
; This query needs two of them. 0xfff0 is not a square modulo 2^64: it is
; divisible by 16 but not by 32, so any root is 4y with y odd, and an odd
; square is 1 modulo 8 where 0xfff0/16 is 7. Nothing in the preprocessor sees
; that -- constant bit propagation settles the easier "an even factor cannot
; give an odd product" before a single gate is built, so that query would
; prove nothing here -- and the multiply is written as a product of two
; variables held equal rather than as a square, so what reaches the
; abstraction is an ordinary BVMULT.
;
; The lemmas are theorems about the operation, so they can only rule out
; candidates the query rules out too. What that buys is a different route to
; the same verdict, and the three legs below are the three routes: with the
; schemas, without them, and without the abstraction at all. A schema that
; was merely usually true would show as a disagreement between the first leg
; and the other two.
;
; Which schema fires on which round is the solver's business -- it depends on
; the candidates it happens to offer -- so what is pinned is that one of them
; does, not which.
;
; RUN: %solver --incremental=off -s --bv-eq-abstraction=1 --bv-term-abstraction=1 %s 2>&1 | %OutputCheck --check-prefix=SCHEMAS %s
; RUN: %solver --incremental=off -s --bv-eq-abstraction=1 --bv-term-abstraction=1 --bv-term-abstraction-schemas=0 %s 2>&1 | %OutputCheck --check-prefix=NOSCHEMAS %s
; RUN: %solver --incremental=off %s 2>&1 | %OutputCheck --check-prefix=PLAIN %s
;
; SCHEMAS-NOT: Fatal Error
; SCHEMAS-NOT: Assertion
; SCHEMAS: BV abstraction: BVMULT [a-z-]+ lemma over operand [01]
; SCHEMAS: ^unsat$
;
; The opt-out leaves the blocking lemma as the only refinement there is, and
; the query is still refuted -- by the exact encoding the escalation reaches
; instead. Without this leg the run above would pass against a build whose
; schemas answer the query on their own but say the wrong thing.
; NOSCHEMAS-NOT: Fatal Error
; NOSCHEMAS-NOT: BVMULT [a-z-]+ lemma
; NOSCHEMAS: ^unsat$
;
; PLAIN: ^unsat$
;
(set-logic QF_BV)
(declare-fun x () (_ BitVec 64))
(declare-fun y () (_ BitVec 64))
(assert (= (bvmul x y) #x000000000000fff0))
(assert (= x y))
(check-sat)
