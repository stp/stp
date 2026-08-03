; RUN: not %solver %s 2>&1 | %OutputCheck %s
;
; SMT-LIB allows any format with eb >= 2 and sb >= 2, but symfpu cannot build
; circuits for the narrowest of them. Every operation unpacks its operands,
; and symfpu::unpack asserts INVARIANT(unpackedExWidth > exWidth) to keep its
; exponent arithmetic from overflowing; unpackedFloat::exponentWidth returns
; the packed width unchanged once sb <= 3, so that reads eb > eb.
;
; With assertions on the solve aborted. With them off -- which is what
; CMAKE_BUILD_TYPE=Release forces, whatever -DENABLE_ASSERTIONS says -- the
; widths underflowed through matchWidth into a bitvector of about 2^32 bits
; and the process segfaulted. Refused at the front door instead, the way
; fp.rem is.
; CHECK: this floating-point format is not supported.*at least 4 significand bits
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 3 3))
(assert (fp.isSubnormal x))
(check-sat)
