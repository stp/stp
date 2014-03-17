; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(
benchmark smt
:logic QF_BV
:status sat

; sym1 = 0xF..F.
:extrafuns ((sym1 BitVec[64]))
:assumption (=  sym1 (sign_extend[63] bv1[1]))
:assumption (=  sym1 (bvnot bv0[64]))

; sym2 = 0x0..01
:extrafuns ((sym2 BitVec[64]))
:assumption (=  sym2 (zero_extend[63] bv1[1]))

; Valid according to the spec.
:assumption (= sym1 (zero_extend[0] sym1))
:assumption (= sym1 (sign_extend[0] sym1))

; Bit shift by a value with a type > 32 bits.
:extrafuns ((sym3 BitVec[64]))
:assumption (= sym3 (bvshl bv1[64] bv63[64]))
:extrafuns ((sym4 BitVec[64]))
:assumption (= sym4 (bvlshr bv1[64] bv63[64]))

:extrafuns ((sym6 BitVec[64]))
:extrafuns ((sym7 BitVec[63]))
:assumption (= sym6 (zero_extend[1] sym7))
:assumption (= sym6 (sign_extend[1] sym7))

; Bit shift by a variable. Note it's shifted by itself.
;:extrafuns ((sym4 BitVec[32]))
;:extrafuns ((sym5 BitVec[32]))
;:assumption (= sym5 (bvshl sym4 sym4))

:formula true
)
