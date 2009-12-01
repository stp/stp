(benchmark BenchmarkName.smt
:logic QF_AUFBV
:extrafuns ((myarray BitVec[32] BitVec[32]))
:extrafuns ((mychar BitVec[32]))
:extrafuns ((myindex BitVec[32]))

; 
; Verification formulas
; 
:extrafuns ((in_1L0_1L0_0 BitVec[4]))
:extrafuns ((in_1L0 BitVec[4]))
:extrafuns ((in_1L0_1L0_1 BitVec[4]))
:assumption
(= in_1L0_1L0_1 in_1L0)
; bit rSp
:extrafuns ((rSp_3L0_0 BitVec[1]))
; bit rSk
:extrafuns ((rSk_3L1_0 BitVec[1]))
; 
; Inlining :reverseSketch
; 
:extrafuns ((in_1L0_5L0_0 BitVec[4]))
:extrafuns ((in_1L0_5L0_1 BitVec[4]))
:assumption
(= in_1L0_5L0_1 in_1L0_1L0_1)
:extrafuns ((sk__out_1L1_5L1_0 BitVec[1]))
; _out_1L1 = 0
:extrafuns ((sk__out_1L1_5L1_1 BitVec[1]))
:assumption
(= sk__out_1L1_5L1_1 bv0[1])
; bit _has_out__3L0
:extrafuns ((sk__has_out__3L0_7L0_0 BitVec[1]))
; _has_out__3L0 = 0
:extrafuns ((sk__has_out__3L0_7L0_1 BitVec[1]))
:assumption
(= sk__has_out__3L0_7L0_1 bv0[1])
; bit[5] tmp_3L1
:extrafuns ((tmp_3L1_7L1_0 BitVec[5]))
; tmp_3L1 = ??:bit[5]:1
:extrafuns ((tmp_3L1_7L1_1 BitVec[5]))
:assumption
(= tmp_3L1_7L1_1 bv0[5])
; bit[2] tmp2_3L2
:extrafuns ((tmp2_3L2_7L2_0 BitVec[2]))
; tmp2_3L2 = ??:bit[2]:1
:extrafuns ((tmp2_3L2_7L2_1 BitVec[2]))
:assumption
(= tmp2_3L2_7L2_1 bv0[2])
; int lll_3L3
:extrafuns ((lll_3L3_7L3_0 BitVec[5]))
; lll_3L3 = ((int)tmp2_3L2)
:extrafuns ((lll_3L3_7L3_1 BitVec[5]))
:assumption
(= lll_3L3_7L3_1 (concat bv0[3] tmp2_3L2_7L2_1))
; int ttt_3L4
:extrafuns ((ttt_3L4_7L4_0 BitVec[5]))
; bit[5] __sa0
:extrafuns ((sk___sa0_7L5_0 BitVec[5]))
; __sa0 = tmp_3L1
:extrafuns ((sk___sa0_7L5_1 BitVec[5]))
:assumption
(= sk___sa0_7L5_1 tmp_3L1_7L1_1)
; bit[5] __sa1
:extrafuns ((sk___sa1_7L6_0 BitVec[5]))
; __sa1 = (__sa0)>>(lll_3L3)
:extrafuns ((sk___sa1_7L6_1 BitVec[5]))
:assumption
(= sk___sa1_7L6_1 (ite		(= lll_3L3_7L3_1 bv0[5])
	sk___sa0_7L5_1
	(ite		(= lll_3L3_7L3_1 bv1[5])
	(bvlshr sk___sa0_7L5_1 bv1[5])
	(ite		(= lll_3L3_7L3_1 bv2[5])
	(bvlshr sk___sa0_7L5_1 bv2[5])
	(ite		(= lll_3L3_7L3_1 bv3[5])
	(bvlshr sk___sa0_7L5_1 bv3[5])
	(ite		(= lll_3L3_7L3_1 bv4[5])
	(bvlshr sk___sa0_7L5_1 bv4[5])
	(ite		(= lll_3L3_7L3_1 bv5[5])
	(bvlshr sk___sa0_7L5_1 bv5[5])
	(ite		(= lll_3L3_7L3_1 bv6[5])
	(bvlshr sk___sa0_7L5_1 bv6[5])
	(ite		(= lll_3L3_7L3_1 bv7[5])
	(bvlshr sk___sa0_7L5_1 bv7[5])
	(ite		(= lll_3L3_7L3_1 bv8[5])
	(bvlshr sk___sa0_7L5_1 bv8[5])
	(ite		(= lll_3L3_7L3_1 bv9[5])
	(bvlshr sk___sa0_7L5_1 bv9[5])
	(ite		(= lll_3L3_7L3_1 bv10[5])
	(bvlshr sk___sa0_7L5_1 bv10[5])
	(ite		(= lll_3L3_7L3_1 bv11[5])
	(bvlshr sk___sa0_7L5_1 bv11[5])
	(ite		(= lll_3L3_7L3_1 bv12[5])
	(bvlshr sk___sa0_7L5_1 bv12[5])
	(ite		(= lll_3L3_7L3_1 bv13[5])
	(bvlshr sk___sa0_7L5_1 bv13[5])
	(ite		(= lll_3L3_7L3_1 bv14[5])
	(bvlshr sk___sa0_7L5_1 bv14[5])
	(ite		(= lll_3L3_7L3_1 bv15[5])
	(bvlshr sk___sa0_7L5_1 bv15[5])
	(ite		(= lll_3L3_7L3_1 bv16[5])
	(bvlshr sk___sa0_7L5_1 bv16[5])
	(ite		(= lll_3L3_7L3_1 bv17[5])
	(bvlshr sk___sa0_7L5_1 bv17[5])
	(ite		(= lll_3L3_7L3_1 bv18[5])
	(bvlshr sk___sa0_7L5_1 bv18[5])
	(ite		(= lll_3L3_7L3_1 bv19[5])
	(bvlshr sk___sa0_7L5_1 bv19[5])
	(ite		(= lll_3L3_7L3_1 bv20[5])
	(bvlshr sk___sa0_7L5_1 bv20[5])
	(ite		(= lll_3L3_7L3_1 bv21[5])
	(bvlshr sk___sa0_7L5_1 bv21[5])
	(ite		(= lll_3L3_7L3_1 bv22[5])
	(bvlshr sk___sa0_7L5_1 bv22[5])
	(ite		(= lll_3L3_7L3_1 bv23[5])
	(bvlshr sk___sa0_7L5_1 bv23[5])
	(ite		(= lll_3L3_7L3_1 bv24[5])
	(bvlshr sk___sa0_7L5_1 bv24[5])
	(ite		(= lll_3L3_7L3_1 bv25[5])
	(bvlshr sk___sa0_7L5_1 bv25[5])
	(ite		(= lll_3L3_7L3_1 bv26[5])
	(bvlshr sk___sa0_7L5_1 bv26[5])
	(ite		(= lll_3L3_7L3_1 bv27[5])
	(bvlshr sk___sa0_7L5_1 bv27[5])
	(ite		(= lll_3L3_7L3_1 bv28[5])
	(bvlshr sk___sa0_7L5_1 bv28[5])
	(ite		(= lll_3L3_7L3_1 bv29[5])
	(bvlshr sk___sa0_7L5_1 bv29[5])
	(ite		(= lll_3L3_7L3_1 bv30[5])
	(bvlshr sk___sa0_7L5_1 bv30[5])
	(ite		(= lll_3L3_7L3_1 bv31[5])
	(bvlshr sk___sa0_7L5_1 bv31[5])
	(bvlshr sk___sa0_7L5_1 bv32[5])
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
))
; ttt_3L4 = ((int)__sa1)
:extrafuns ((ttt_3L4_7L4_1 BitVec[5]))
:assumption
(= ttt_3L4_7L4_1 sk___sa1_7L6_1)
; int _pac2
:extrafuns ((sk__pac2_9L0_0 BitVec[5]))
; _pac2 = ttt_3L4
:extrafuns ((sk__pac2_9L0_1 BitVec[5]))
:assumption
(= sk__pac2_9L0_1 ttt_3L4_7L4_1)
; _out_1L1 = in_1L0[_pac2]
:extrafuns ((rawArracTmp0_0 BitVec[1]))
:extrafuns ((rawArracTmp0_1 BitVec[1]))
:assumption
(= rawArracTmp0_1 (ite		(= sk__pac2_9L0_1 bv0[5])
	(extract[0:0] in_1L0_5L0_1)
	(ite		(= sk__pac2_9L0_1 bv1[5])
	(extract[1:1] in_1L0_5L0_1)
	(ite		(= sk__pac2_9L0_1 bv2[5])
	(extract[2:2] in_1L0_5L0_1)
	(extract[3:3] in_1L0_5L0_1)
)
)
))
:extrafuns ((sk__out_1L1_5L1_2 BitVec[1]))
:assumption
(= sk__out_1L1_5L1_2 rawArracTmp0_1)
; _has_out__3L0 = 1
:extrafuns ((sk__has_out__3L0_7L0_2 BitVec[1]))
:assumption
(= sk__has_out__3L0_7L0_2 bv1[1])
:extrafuns ((rSk_3L1_1 BitVec[1]))
:assumption
(= rSk_3L1_1 sk__out_1L1_5L1_2)
; 
; Done inlining :reverseSketch
; 
; 
; Inlining :reverse
; 
:extrafuns ((in_5L2_11L0_0 BitVec[4]))
:extrafuns ((in_5L2_11L0_1 BitVec[4]))
:assumption
(= in_5L2_11L0_1 in_1L0_1L0_1)
:extrafuns ((sk__out_5L2_11L1_0 BitVec[1]))
; _out_5L2 = 0
:extrafuns ((sk__out_5L2_11L1_1 BitVec[1]))
:assumption
(= sk__out_5L2_11L1_1 bv0[1])
; bit _has_out__7L0
:extrafuns ((sk__has_out__7L0_13L0_0 BitVec[1]))
; _has_out__7L0 = 0
:extrafuns ((sk__has_out__7L0_13L0_1 BitVec[1]))
:assumption
(= sk__has_out__7L0_13L0_1 bv0[1])
; int _pac3
:extrafuns ((sk__pac3_14L0_0 BitVec[5]))
; _pac3 = 2
:extrafuns ((sk__pac3_14L0_1 BitVec[5]))
:assumption
(= sk__pac3_14L0_1 bv2[5])
; _out_5L2 = in_5L2[_pac3]
:extrafuns ((sk__out_5L2_11L1_2 BitVec[1]))
:assumption
(= sk__out_5L2_11L1_2 (extract[2:2] in_5L2_11L0_1))
; _has_out__7L0 = 1
:extrafuns ((sk__has_out__7L0_13L0_2 BitVec[1]))
:assumption
(= sk__has_out__7L0_13L0_2 bv1[1])
:extrafuns ((rSp_3L0_1 BitVec[1]))
:assumption
(= rSp_3L0_1 sk__out_5L2_11L1_2)
; 
; Done inlining :reverse
; 
; 
; Correctness Conditions
; 
:assumption
(or		(not (bvslt ttt_3L4_7L4_1 bv4[5]))
	(not (and (bvsge sk__pac2_9L0_1 bv0[5]) (bvslt sk__pac2_9L0_1 bv4[5])))
	(not (= rSp_3L0_1 rSk_3L1_1))
)
)
