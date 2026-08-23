; (distinct t1 ... tn) over a sort with fewer than n values is unsatisfiable by
; pigeonhole. The parser expands distinct into C(n, 2) disequalities, so what
; would otherwise reach the solver is the binary-encoded form of it -- a shape
; whose cost to a CDCL search is out of all proportion to how it reads:
; sixteen operands over (_ BitVec 4) answer in 0.02s, seventeen take over seven
; minutes. The count is checked where the sort is known instead, in the parser.
;
; Pinned here, at each sort the guard knows: exactly saturating stays
; satisfiable and must not be folded, one more is refused, and a sort no
; writable operand count can exceed is left alone. The saturating groups also
; keep the pairwise reading of distinct honest, which is what arity1.smt2 was
; written for -- four operands over (_ BitVec 2) plus (= c0 c2) is unsat only
; if the expansion includes the non-adjacent pair.
;
; The refused side stops at the saturating count on purpose. A case that fails
; only by taking seven minutes would turn a regression of the fold into a hung
; CI job rather than a red one; sample-smt-tests/arity1.smt2 pins the refused
; side deterministically instead, under --max-num-confl 0.
;
; RUN: %solver --SMTLIB2 --incremental=off %s 2>&1 | %OutputCheck %s
; RUN: %solver --SMTLIB2 --incremental=on %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^unsat
; CHECK-NEXT: ^sat
; CHECK-NEXT: ^sat
; CHECK: REACHED-END
;
(set-logic QF_BV)

; sixteen values, sixteen operands: satisfiable, and it must not be folded.
(push 1)
(declare-const a0 (_ BitVec 4))
(declare-const a1 (_ BitVec 4))
(declare-const a2 (_ BitVec 4))
(declare-const a3 (_ BitVec 4))
(declare-const a4 (_ BitVec 4))
(declare-const a5 (_ BitVec 4))
(declare-const a6 (_ BitVec 4))
(declare-const a7 (_ BitVec 4))
(declare-const a8 (_ BitVec 4))
(declare-const a9 (_ BitVec 4))
(declare-const a10 (_ BitVec 4))
(declare-const a11 (_ BitVec 4))
(declare-const a12 (_ BitVec 4))
(declare-const a13 (_ BitVec 4))
(declare-const a14 (_ BitVec 4))
(declare-const a15 (_ BitVec 4))
(assert (distinct a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))
(check-sat)
(pop 1)

; four values, four operands: satisfiable, and still expanded pairwise -- the
; equality below is between operands that are not adjacent in the group.
(push 1)
(declare-const c0 (_ BitVec 2))
(declare-const c1 (_ BitVec 2))
(declare-const c2 (_ BitVec 2))
(declare-const c3 (_ BitVec 2))
(assert (distinct c0 c1 c2 c3))
(check-sat)
(assert (= c0 c2))
(check-sat)
(pop 1)

; one more than the sort holds: refused.
(push 1)
(declare-const d0 (_ BitVec 2))
(declare-const d1 (_ BitVec 2))
(declare-const d2 (_ BitVec 2))
(declare-const d3 (_ BitVec 2))
(declare-const d4 (_ BitVec 2))
(assert (distinct d0 d1 d2 d3 d4))
(check-sat)
(pop 1)

; two values, one bit down: two operands saturate it, three do not fit.
(push 1)
(declare-const b0 (_ BitVec 1))
(declare-const b1 (_ BitVec 1))
(assert (distinct b0 b1))
(check-sat)
(pop 1)
(push 1)
(declare-const b0 (_ BitVec 1))
(declare-const b1 (_ BitVec 1))
(declare-const b2 (_ BitVec 1))
(assert (distinct b0 b1 b2))
(check-sat)
(pop 1)

; Bool has two values, and reaches the other distinct rule.
(push 1)
(declare-const s Bool)
(declare-const t Bool)
(assert (distinct s t))
(check-sat)
(pop 1)
(push 1)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (distinct p q r))
(check-sat)
(pop 1)

; A width no writable operand count can exceed is left alone: this is
; unsatisfiable for an ordinary reason, not by cardinality.
(push 1)
(declare-const w0 (_ BitVec 32))
(declare-const w1 (_ BitVec 32))
(assert (distinct w0 w1))
(assert (= w0 w1))
(check-sat)
(pop 1)

; At 64 bits and above the guard returns early rather than compute 1 << width,
; which would be undefined. Both of these stay satisfiable.
(push 1)
(declare-const x0 (_ BitVec 64))
(declare-const x1 (_ BitVec 64))
(assert (distinct x0 x1))
(check-sat)
(pop 1)
(push 1)
(declare-const y0 (_ BitVec 128))
(declare-const y1 (_ BitVec 128))
(assert (distinct y0 y1))
(check-sat)
(pop 1)
(echo "REACHED-END")
