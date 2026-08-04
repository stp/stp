; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; symfpu::roundToIntegral resizes a rounding point of width
; unpackedExponentWidth + 1 down to the unpacked significand width, choosing
; between matchWidth -- which may only widen -- and extract on
;
;   significandWidth >= exponentWidth        (symfpu/core/convert.h:122)
;
; one short of the width it is really resizing. Where the two widths are
; equal the guard sends a value one bit too wide into matchWidth, whose
; unsigned subtraction then wraps to about 2^32: SIGSEGV in a Release build,
; assertion failure otherwise. (_ FloatingPoint 4 5) is the smallest such
; format; the family is unbounded -- (eb, eb+1) for every eb >= 3, so
; (_ FloatingPoint 8 9) too -- and nowhere near the degenerate formats, which
; is why the standard sizes never showed it.
;
; The extract arm is the one that should run there and is already correct
; (the collar above it bounds the value), so upstream's guard wants to read
; '>' and this refusal can go when the pinned submodule carries that fix.
; CHECK: fp.roundToIntegral is not supported at this format
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 4 5))
(assert (not (fp.eq (fp.roundToIntegral RNE x) x)))
(assert (fp.isNormal x))
(check-sat)
