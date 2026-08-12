; A definition whose replacement carries theory content -- an array read
; here -- must not be harvested: substituting it would smuggle READs into
; conjuncts whose transform decision was already made on the raw formula
; (the same bug class as judging arrayness before totalisation). The
; equation still constrains normally; only the rewrite is declined.
; RUN: %solver --incremental %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 %s | %OutputCheck %s
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun x () (_ BitVec 8))
; base-level definition with an array-read replacement
(assert (= x (select a #x01)))
(assert (bvult x #x10))
(push 1)
; x names a[1], which is below 16, so a[1] cannot exceed 32
(assert (bvugt (select a #x01) #x20))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(push 1)
(assert (bvult (select a #x01) #x08))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; the same shape as a pushed-level definition
(push 1)
(assert (= x (select a #x02)))
(assert (bvugt (select a #x02) #x20))
; a[2] = x < 16 again contradicts a[2] > 32
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
(exit)
