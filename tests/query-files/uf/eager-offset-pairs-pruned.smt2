; A function applied at a sliding offset -- f(i), f(i+1), f(i+2), ... -- has no
; congruent pair at all: every premise is an equality between two bit-vectors
; that differ by a nonzero constant. The eager policy used to build all C(n,2)
; of them anyway, because it asked the *named* actuals, which are fresh symbols
; for compound terms and so only ever expose two literal constants.
;
; It now asks the lowered actuals, which the node factory already decides: it
; cancels the common addend and folds the equality to false. Every pair is
; therefore skipped and nothing is installed.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on -s %s 2>&1 | %OutputCheck %s
; CHECK: UF: eager selected f \(4 applications, 6 pairs estimated, 6 enumerated, 6 impossible, 0 constraints\)
; CHECK: UF: eager total 1/1 declarations, 0 constraints
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(declare-const i (_ BitVec 8))
(assert (distinct (f i)
                  (f (bvadd i #x01))
                  (f (bvadd i #x02))
                  (f (bvadd i #x03))))
(check-sat)
