; RUN: %solver %s | %OutputCheck %s
;
; And the same query under --max-num-confl 0, a conflict budget no search can
; spend. Expanded into its ten disequalities this group is binary-encoded
; pigeonhole, which needs conflicts to refute, so a build that expands it
; reports its timeout verdict instead of an answer. Refused where the operand
; count is known, in the parser, it is the constant false and needs no search
; at all -- which is what makes this a deterministic check rather than a timed
; one, and why the directive below is the answer itself rather than the
; absence of that verdict.
;
; RUN: %solver --max-num-confl 0 %s | %OutputCheck %s
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
; CHECK-NEXT: ^unsat
(set-info :status unsat)

; distinct is pairwise

(declare-const u (_ BitVec 2))
(declare-const v (_ BitVec 2))
(declare-const w (_ BitVec 2))
(declare-const x (_ BitVec 2))
(declare-const y (_ BitVec 2))

; unsat by pigeon hole.	
(assert (distinct u v w x y))

(check-sat)
