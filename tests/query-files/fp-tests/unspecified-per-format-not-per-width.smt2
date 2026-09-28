; RUN: %solver %s | %OutputCheck %s
;
; fp.min's result for (+0, -0) is unspecified, and it is unspecified once per
; *sort*: fp.min at (_ FloatingPoint 8 24) and fp.min at (_ FloatingPoint 24 8)
; are two different SMT-LIB functions, free to answer differently.
;
; The two sorts pack into the same 32 bits, and +0/-0 have the same bits in
; every IEEE format, so the totalisation array these read -- one array per
; operation and signature, indexed on the operands -- used to be shared
; between them: its name spelled the packed index and value widths, which are
; equal here, rather than the operand formats, which are not. The two
; independent choices were then forced to agree and this answered unsat.
;
; See FloatBlaster::unspecifiedValue. The sibling test pins the congruence
; that sharing is *supposed* to provide, so the fix cannot be "never share".
; CHECK: ^sat
(set-logic QF_FP)
(assert (fp.isNegative (fp.min (_ +zero  8 24) (_ -zero  8 24))))
(assert (fp.isPositive (fp.min (_ +zero 24  8) (_ -zero 24  8))))
(check-sat)
