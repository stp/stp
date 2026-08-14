; Totalising a partial floating-point operation can introduce reads of an
; unspecified-value array into a formula that had no arrays at all -- so
; the driver must decide arrayness (transform AND refinement) from the
; PREPARED form, not the raw conjunct. Deciding from the raw conjunct sent
; the introduced READ straight into the bit-blaster (a crash), and would
; skip read congruence between unspecified results (a wrong answer).
; RUN: %solver --incremental %s | %OutputCheck %s
(set-logic QF_FP)
(declare-fun f () (_ FloatingPoint 8 24))
(declare-fun g () (_ FloatingPoint 8 24))
; the crash shape: to_ubv of a NaN constant, no arrays anywhere in sight
(push 1)
(assert (distinct (_ bv0 1)
  (ite (bvuge (_ bv1 32)
              ((_ fp.to_ubv 32) roundTowardZero
                                (fp (_ bv0 1) (_ bv255 8) (_ bv1 23))))
       (_ bv1 1) (_ bv0 1))))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
; the soundness shape: two unspecified reads whose indices are made equal
; must agree -- that is the introduced array's read congruence, which only
; the refinement loop enforces
(push 1)
(assert (fp.isNaN f))
(assert (fp.isNaN g))
(assert (= f g))
(assert (distinct ((_ fp.to_ubv 32) roundTowardZero f)
                  ((_ fp.to_ubv 32) roundTowardZero g)))
; CHECK-NEXT: ^unsat
(check-sat)
(pop 1)
; while different rounding modes index the unspecified array differently,
; leaving the two results independent
(push 1)
(assert (fp.isNaN f))
(assert (distinct ((_ fp.to_ubv 32) roundTowardZero f)
                  ((_ fp.to_ubv 32) roundNearestTiesToEven f)))
; CHECK-NEXT: ^sat
(check-sat)
(pop 1)
(exit)
