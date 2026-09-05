; RUN: %solver %s 2>&1 | %OutputCheck %s
; CHECK-L: The body's array index or element sorts differ from the declared ones
; CHECK-L: sat
;
; A nullary array define-fun whose declared sort disagrees with its body's
; in sort *class* rather than width: RoundingMode's carrier is 5 bits, so
; (Array RoundingMode X) and (Array (_ BitVec 5) X) have identical widths
; and the width check cannot tell them apart. The class check reports the
; mismatch and -- mirroring the width-mismatch policy of the sibling
; productions -- still stores the alias and keeps parsing, so the
; check-sat below is answered.
(set-logic QF_ABVFP)
(declare-fun base () (Array (_ BitVec 5) (_ BitVec 8)))
(define-fun A0 () (Array RoundingMode (_ BitVec 8)) base)
(check-sat)
