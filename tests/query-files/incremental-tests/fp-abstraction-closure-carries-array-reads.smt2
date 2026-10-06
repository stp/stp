; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true %s | %OutputCheck %s
; RUN: %solver --incremental=on --fp-abstraction=true --fp-abstraction-incremental=true -d %s | %OutputCheck %s
;
; A per-level piece carries the definitions of every abstraction record it
; reaches, including the cross-operation partner of a fused multiply-add
; that another piece minted. Those definitions mention the other piece's
; operands, so a piece with no array operation of its own can still encode
; a read: below, each FMA's addend is a read, and the later piece holds only
; the product of its factors, which is the FMA's partner. The driver judged
; arrayness on the piece before the abstraction, skipped the array
; transform, and the read reached the bit-blaster ("BBTerm: Illegal kind to
; BBTerm").
;
; The first block is the reported shape: the read is of the unspecified-value
; array that totalising an out-of-range fp.to_ubv introduces. The second
; pops the piece holding a user array's select before the product arrives,
; so the read reaches the encoding only through the closure.
; CHECK: ^sat$
; CHECK-NEXT: ^unsat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^sat$
; CHECK-NEXT: ^unsat$
(set-logic QF_ABVFP)
(declare-const x (_ FloatingPoint 5 11))
(declare-const y (_ FloatingPoint 5 11))
(declare-const u (_ FloatingPoint 5 11))
(declare-const v (_ FloatingPoint 5 11))
(declare-const i (_ BitVec 4))
(declare-const a (Array (_ BitVec 4) (_ FloatingPoint 5 11)))
(push 1)
(assert (fp.isNormal (fp.fma RNE x y ((_ to_fp_unsigned 5 11) RNE ((_ fp.to_ubv 4) RNE (fp #b0 #b11110 #b0000000000))))))
(check-sat-assuming ((fp.isNormal (fp.mul RNE x y))))
(check-sat-assuming ((fp.isNormal (fp.mul RNE x y)) (fp.isInfinite x)))
(pop 1)
(push 1)
(assert (fp.isNormal (fp.fma RNE u v (select a i))))
(check-sat)
(pop 1)
(assert (fp.isNormal (fp.mul RNE u v)))
(check-sat)
(assert (fp.isInfinite u))
(check-sat)
(exit)
