; The eager policy charges a declaration for the pairs it will actually build,
; not for every pair it will look at.
;
; f's first argument is one of two literal tags, so its six applications split
; into two groups of three, and a pair drawn from different groups can never be
; congruent. Counting C(6, 2) charged fifteen where six are installed, which is
; enough to push a declaration past a budget it fits inside.
;
; The same partition bounds the walk as well as the charge: the nine
; cross-group pairs are neither charged nor enumerated, so a declaration made
; of many singleton groups cannot be charged nothing and still walked
; quadratically. Estimated, enumerated and emitted therefore all read six.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on -s %s 2>&1 | %OutputCheck %s
; CHECK: UF: eager selected f \(6 applications, 6 pairs estimated, 6 enumerated, 0 impossible, 6 constraints\)
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(declare-const d (_ BitVec 8))
(declare-const e (_ BitVec 8))
(declare-const g (_ BitVec 8))
(assert (distinct (f #x01 a) (f #x01 b) (f #x01 c)
                  (f #x02 d) (f #x02 e) (f #x02 g)))
(check-sat)
