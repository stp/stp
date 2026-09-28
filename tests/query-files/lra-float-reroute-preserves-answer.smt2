; RUN: %solver --SMTLIB2 %s | %OutputCheck %s
; RUN: %solver --SMTLIB2 -s --lra-float-driver=1 --lra-float-reroute=1 --lra-float-reroute-floor=0 %s 2>&1 | %OutputCheck --check-prefix=REROUTE %s
;
; The float-tier exact reroute must not change any answer: it re-solves a query
; on the exact driver, which certifies every float result, so the verdict is
; the one the float driver would have reached. The second run makes the reroute
; fire. A budget of 1 trips on any fill past the pristine count, and a floor of
; 0 drops the absolute size test that keeps small tableaux from rerouting. The
; fill is sampled only once every 64 float checks, so the query has to make at
; least that many: ten Real variables in [0,100], thirty disjunctions of
; three-term inequalities and a lower bound on their sum take a few hundred
; float checks on every backend before settling sat. The float driver is
; named explicitly because the backend sweeps also run this file with it off.
;
; CHECK: ^sat$
; REROUTE: re-solving on the exact driver
; REROUTE: ^sat$
(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(declare-fun x7 () Real)
(declare-fun x8 () Real)
(declare-fun x9 () Real)
(assert (and (<= 0 x0) (<= x0 100)))
(assert (and (<= 0 x1) (<= x1 100)))
(assert (and (<= 0 x2) (<= x2 100)))
(assert (and (<= 0 x3) (<= x3 100)))
(assert (and (<= 0 x4) (<= x4 100)))
(assert (and (<= 0 x5) (<= x5 100)))
(assert (and (<= 0 x6) (<= x6 100)))
(assert (and (<= 0 x7) (<= x7 100)))
(assert (and (<= 0 x8) (<= x8 100)))
(assert (and (<= 0 x9) (<= x9 100)))
(assert (or (<= (+ (* 7 x3) (* 8 x4) (* 3 x1)) 96) (>= (+ (* 9 x1) (* 5 x0) (* 1 x6)) 527)))
(assert (or (<= (+ (* 5 x8) (* 3 x9) (* 2 x5)) 184) (>= (+ (* 5 x3) (* 4 x0) (* 3 x4)) 617)))
(assert (or (<= (+ (* 6 x4) (* 7 x5) (* 9 x1)) 177) (>= (+ (* 5 x2) (* 2 x3) (* 9 x7)) 607)))
(assert (or (<= (+ (* 9 x0) (* 4 x4) (* 7 x8)) 266) (>= (+ (* 8 x9) (* 3 x4) (* 4 x6)) 612)))
(assert (or (<= (+ (* 1 x4) (* 8 x0) (* 5 x1)) 315) (>= (+ (* 3 x8) (* 4 x7) (* 2 x5)) 722)))
(assert (or (<= (+ (* 3 x3) (* 6 x7) (* 7 x4)) 351) (>= (+ (* 6 x5) (* 2 x8) (* 1 x3)) 534)))
(assert (or (<= (+ (* 6 x4) (* 3 x3) (* 5 x1)) 285) (>= (+ (* 2 x0) (* 5 x9) (* 6 x5)) 318)))
(assert (or (<= (+ (* 3 x5) (* 7 x4) (* 2 x9)) 200) (>= (+ (* 5 x9) (* 3 x3) (* 5 x7)) 690)))
(assert (or (<= (+ (* 1 x9) (* 6 x2) (* 1 x5)) 282) (>= (+ (* 5 x2) (* 2 x5) (* 8 x8)) 512)))
(assert (or (<= (+ (* 1 x6) (* 1 x3) (* 1 x1)) 136) (>= (+ (* 9 x9) (* 8 x2) (* 4 x0)) 629)))
(assert (or (<= (+ (* 7 x0) (* 4 x1) (* 8 x4)) 153) (>= (+ (* 8 x3) (* 1 x7) (* 4 x6)) 731)))
(assert (or (<= (+ (* 4 x7) (* 8 x3) (* 4 x6)) 66) (>= (+ (* 4 x0) (* 9 x4) (* 4 x8)) 537)))
(assert (or (<= (+ (* 6 x6) (* 1 x4) (* 6 x2)) 339) (>= (+ (* 8 x1) (* 7 x6) (* 2 x0)) 740)))
(assert (or (<= (+ (* 5 x3) (* 8 x2) (* 6 x5)) 265) (>= (+ (* 6 x8) (* 7 x3) (* 8 x4)) 376)))
(assert (or (<= (+ (* 7 x4) (* 3 x3) (* 5 x0)) 391) (>= (+ (* 8 x0) (* 7 x2) (* 7 x7)) 523)))
(assert (or (<= (+ (* 1 x0) (* 5 x3) (* 2 x2)) 252) (>= (+ (* 4 x6) (* 3 x3) (* 6 x0)) 875)))
(assert (or (<= (+ (* 1 x7) (* 2 x8) (* 1 x9)) 354) (>= (+ (* 3 x1) (* 1 x7) (* 6 x4)) 381)))
(assert (or (<= (+ (* 6 x8) (* 2 x0) (* 2 x4)) 328) (>= (+ (* 5 x7) (* 7 x6) (* 4 x3)) 798)))
(assert (or (<= (+ (* 2 x6) (* 6 x1) (* 9 x8)) 272) (>= (+ (* 4 x6) (* 5 x7) (* 8 x1)) 732)))
(assert (or (<= (+ (* 6 x1) (* 3 x8) (* 3 x2)) 126) (>= (+ (* 5 x5) (* 9 x7) (* 1 x9)) 472)))
(assert (or (<= (+ (* 9 x0) (* 2 x4) (* 8 x1)) 357) (>= (+ (* 9 x7) (* 4 x8) (* 7 x1)) 600)))
(assert (or (<= (+ (* 1 x5) (* 1 x3) (* 6 x2)) 328) (>= (+ (* 8 x7) (* 7 x4) (* 3 x9)) 557)))
(assert (or (<= (+ (* 3 x9) (* 7 x5) (* 2 x8)) 360) (>= (+ (* 6 x2) (* 4 x9) (* 6 x4)) 395)))
(assert (or (<= (+ (* 6 x1) (* 6 x6) (* 6 x2)) 139) (>= (+ (* 9 x4) (* 2 x0) (* 6 x8)) 400)))
(assert (or (<= (+ (* 2 x2) (* 2 x9) (* 3 x7)) 383) (>= (+ (* 7 x7) (* 4 x3) (* 8 x4)) 526)))
(assert (or (<= (+ (* 6 x4) (* 9 x5) (* 9 x3)) 281) (>= (+ (* 6 x6) (* 5 x8) (* 8 x9)) 721)))
(assert (or (<= (+ (* 3 x9) (* 9 x0) (* 8 x4)) 337) (>= (+ (* 7 x9) (* 1 x5) (* 3 x6)) 823)))
(assert (or (<= (+ (* 5 x1) (* 2 x7) (* 5 x5)) 297) (>= (+ (* 3 x3) (* 4 x7) (* 2 x1)) 606)))
(assert (or (<= (+ (* 7 x2) (* 9 x0) (* 9 x9)) 184) (>= (+ (* 3 x0) (* 2 x8) (* 4 x3)) 332)))
(assert (or (<= (+ (* 5 x5) (* 1 x1) (* 5 x8)) 362) (>= (+ (* 3 x2) (* 2 x9) (* 9 x6)) 673)))
(assert (>= (+ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) 400))
(check-sat)
(exit)
