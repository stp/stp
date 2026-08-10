; RUN: %solver %s | %OutputCheck %s
;
; One bitvector read two ways in one problem: reinterpreted as a binary16 by
; ((_ to_fp 5 11) bits), and converted as the signed integer it holds by
; ((_ to_fp 5 11) RNE bits). The two readings disagree, so which operation is
; which has to survive lowering.
;
; It did not. A lowered float *is* its packed bits, with the format stamped
; onto the node holding them -- and nodes are hash-consed, so blasting the
; reinterpretation retyped the very node `bits` names. to_fp told its two
; four-argument forms apart by asking that operand's sort, so the integer got
; converted as though it were a float: -32768 came out a zero and STP answered
; unsat. The distinction is recorded in the kind now (FP_TOFP_SIGNED), decided
; here in the parser where the sort is still known.
;
; s = #b1 makes the bits #x8000, which is -32768 signed and exactly
; representable in binary16, so the conversion is not a zero and this is
; satisfiable. The first assertion is a tautology -- the reinterpretation has
; a zero exponent field, so it is +/-0.0 and never NaN -- and exists only to
; make the reinterpretation get lowered first.
(set-logic QF_BVFP)
(declare-fun s () (_ BitVec 1))
(assert (fp.leq ((_ to_fp 5 11) (concat s #b000000000000000))
                ((_ to_fp 5 11) (concat s #b000000000000000))))
(assert (not (fp.isZero ((_ to_fp 5 11) RNE (concat s #b000000000000000)))))
; CHECK: ^sat
(check-sat)
