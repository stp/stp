; RUN: %solver %s | %OutputCheck %s
;
; fp.to_sbv/fp.to_ubv of constants whose exponent field is 64 bits or wider
; (#1372). The literal evaluator's decoder keeps the exponent in int64_t, so
; these formats must go to the circuit: before the fix the bias computation
; was undefined behaviour, and at (66, 4) the literal path tripped a symfpu
; precondition on -16.
(set-logic QF_BVFP)
(assert (or
  (distinct ((_ fp.to_sbv 8) RNE (_ +zero 64 4))
            #x00)
  (distinct ((_ fp.to_sbv 8) RNA (fp #b0 (_ bv9223372036854775809 64) #b101))
            #x07)
  (distinct ((_ fp.to_ubv 8) RNE (fp #b0 (_ bv9223372036854775809 64) #b101))
            #x06)
  (distinct ((_ fp.to_sbv 8) RNE (_ +zero 65 4))
            #x00)
  (distinct ((_ fp.to_sbv 8) RNA (fp #b0 (_ bv18446744073709551617 65) #b101))
            #x07)
  (distinct ((_ fp.to_ubv 8) RNE (fp #b0 (_ bv18446744073709551617 65) #b101))
            #x06)
  (distinct ((_ fp.to_sbv 8) RTZ (fp #b1 (_ bv18446744073709551616 65) #b110))
            #xfd)
  (distinct ((_ fp.to_sbv 8) RNE (fp #b1 (_ bv36893488147419103235 66) #b000))
            #xf0)
  (distinct ((_ fp.to_sbv 8) RNA (fp #b0 (_ bv604462909807314587353089 80) #b101))
            #x07)
  (distinct ((_ fp.to_ubv 8) RNE (fp #b0 (_ bv170141183460469231731687303715884105715 128) #b000))
            #x00)
  (distinct ((_ fp.to_sbv 8) RTP (fp #b0 (_ bv170141183460469231731687303715884105715 128) #b000))
            #x01)
  false))
; CHECK: ^unsat
(check-sat)
