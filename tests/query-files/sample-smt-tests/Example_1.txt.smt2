; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(set-logic QF_BV)
(set-info :source |
  Christoph Erkinger, "Rotating Workforce Scheduling as Satisfiability Modulo
  Theories", Master's Thesis, Technische Universitaet Wien, 2013
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun shift0 () (_ BitVec 63))
(declare-fun shift1 () (_ BitVec 63))
(declare-fun shift2 () (_ BitVec 63))
(declare-fun shift3 () (_ BitVec 63))
(assert (and (= (bvand shift0 shift1) (_ bv0 63)) (= (bvand shift0 shift2) (_ bv0 63)) (= (bvand shift0 shift3) (_ bv0 63)) (= (bvand shift1 shift2) (_ bv0 63)) (= (bvand shift1 shift3) (_ bv0 63)) (= (bvand shift2 shift3) (_ bv0 63)) ))
(assert (= (bvnot (_ bv0 63)) (bvor shift0  (bvor shift1  (bvor shift2  shift3 ) ) ) ))
; ==== Temporal Requirements ====
;
;
(define-fun bitsumhelper ((x (_ BitVec 9))) (_ BitVec 9) (bvand x (bvsub x (_ bv1 9))))
;
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 0 0) shift1)  (concat ((_ extract 7 7) shift1)  (concat ((_ extract 14 14) shift1)  (concat ((_ extract 21 21) shift1)  (concat ((_ extract 28 28) shift1)  (concat ((_ extract 35 35) shift1)  (concat ((_ extract 42 42) shift1)  (concat ((_ extract 49 49) shift1)  ((_ extract 56 56) shift1)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 0 0) shift1)  (concat ((_ extract 7 7) shift1)  (concat ((_ extract 14 14) shift1)  (concat ((_ extract 21 21) shift1)  (concat ((_ extract 28 28) shift1)  (concat ((_ extract 35 35) shift1)  (concat ((_ extract 42 42) shift1)  (concat ((_ extract 49 49) shift1)  ((_ extract 56 56) shift1)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 0 0) shift2)  (concat ((_ extract 7 7) shift2)  (concat ((_ extract 14 14) shift2)  (concat ((_ extract 21 21) shift2)  (concat ((_ extract 28 28) shift2)  (concat ((_ extract 35 35) shift2)  (concat ((_ extract 42 42) shift2)  (concat ((_ extract 49 49) shift2)  ((_ extract 56 56) shift2)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 0 0) shift2)  (concat ((_ extract 7 7) shift2)  (concat ((_ extract 14 14) shift2)  (concat ((_ extract 21 21) shift2)  (concat ((_ extract 28 28) shift2)  (concat ((_ extract 35 35) shift2)  (concat ((_ extract 42 42) shift2)  (concat ((_ extract 49 49) shift2)  ((_ extract 56 56) shift2)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 0 0) shift3)  (concat ((_ extract 7 7) shift3)  (concat ((_ extract 14 14) shift3)  (concat ((_ extract 21 21) shift3)  (concat ((_ extract 28 28) shift3)  (concat ((_ extract 35 35) shift3)  (concat ((_ extract 42 42) shift3)  (concat ((_ extract 49 49) shift3)  ((_ extract 56 56) shift3)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 0 0) shift3)  (concat ((_ extract 7 7) shift3)  (concat ((_ extract 14 14) shift3)  (concat ((_ extract 21 21) shift3)  (concat ((_ extract 28 28) shift3)  (concat ((_ extract 35 35) shift3)  (concat ((_ extract 42 42) shift3)  (concat ((_ extract 49 49) shift3)  ((_ extract 56 56) shift3)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 1 1) shift1)  (concat ((_ extract 8 8) shift1)  (concat ((_ extract 15 15) shift1)  (concat ((_ extract 22 22) shift1)  (concat ((_ extract 29 29) shift1)  (concat ((_ extract 36 36) shift1)  (concat ((_ extract 43 43) shift1)  (concat ((_ extract 50 50) shift1)  ((_ extract 57 57) shift1)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 1 1) shift1)  (concat ((_ extract 8 8) shift1)  (concat ((_ extract 15 15) shift1)  (concat ((_ extract 22 22) shift1)  (concat ((_ extract 29 29) shift1)  (concat ((_ extract 36 36) shift1)  (concat ((_ extract 43 43) shift1)  (concat ((_ extract 50 50) shift1)  ((_ extract 57 57) shift1)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 1 1) shift2)  (concat ((_ extract 8 8) shift2)  (concat ((_ extract 15 15) shift2)  (concat ((_ extract 22 22) shift2)  (concat ((_ extract 29 29) shift2)  (concat ((_ extract 36 36) shift2)  (concat ((_ extract 43 43) shift2)  (concat ((_ extract 50 50) shift2)  ((_ extract 57 57) shift2)  ) ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (bitsumhelper  (concat ((_ extract 1 1) shift2)  (concat ((_ extract 8 8) shift2)  (concat ((_ extract 15 15) shift2)  (concat ((_ extract 22 22) shift2)  (concat ((_ extract 29 29) shift2)  (concat ((_ extract 36 36) shift2)  (concat ((_ extract 43 43) shift2)  (concat ((_ extract 50 50) shift2)  ((_ extract 57 57) shift2)  ) ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 1 1) shift3)  (concat ((_ extract 8 8) shift3)  (concat ((_ extract 15 15) shift3)  (concat ((_ extract 22 22) shift3)  (concat ((_ extract 29 29) shift3)  (concat ((_ extract 36 36) shift3)  (concat ((_ extract 43 43) shift3)  (concat ((_ extract 50 50) shift3)  ((_ extract 57 57) shift3)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 1 1) shift3)  (concat ((_ extract 8 8) shift3)  (concat ((_ extract 15 15) shift3)  (concat ((_ extract 22 22) shift3)  (concat ((_ extract 29 29) shift3)  (concat ((_ extract 36 36) shift3)  (concat ((_ extract 43 43) shift3)  (concat ((_ extract 50 50) shift3)  ((_ extract 57 57) shift3)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 2 2) shift1)  (concat ((_ extract 9 9) shift1)  (concat ((_ extract 16 16) shift1)  (concat ((_ extract 23 23) shift1)  (concat ((_ extract 30 30) shift1)  (concat ((_ extract 37 37) shift1)  (concat ((_ extract 44 44) shift1)  (concat ((_ extract 51 51) shift1)  ((_ extract 58 58) shift1)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 2 2) shift1)  (concat ((_ extract 9 9) shift1)  (concat ((_ extract 16 16) shift1)  (concat ((_ extract 23 23) shift1)  (concat ((_ extract 30 30) shift1)  (concat ((_ extract 37 37) shift1)  (concat ((_ extract 44 44) shift1)  (concat ((_ extract 51 51) shift1)  ((_ extract 58 58) shift1)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 2 2) shift2)  (concat ((_ extract 9 9) shift2)  (concat ((_ extract 16 16) shift2)  (concat ((_ extract 23 23) shift2)  (concat ((_ extract 30 30) shift2)  (concat ((_ extract 37 37) shift2)  (concat ((_ extract 44 44) shift2)  (concat ((_ extract 51 51) shift2)  ((_ extract 58 58) shift2)  ) ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (bitsumhelper  (concat ((_ extract 2 2) shift2)  (concat ((_ extract 9 9) shift2)  (concat ((_ extract 16 16) shift2)  (concat ((_ extract 23 23) shift2)  (concat ((_ extract 30 30) shift2)  (concat ((_ extract 37 37) shift2)  (concat ((_ extract 44 44) shift2)  (concat ((_ extract 51 51) shift2)  ((_ extract 58 58) shift2)  ) ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 2 2) shift3)  (concat ((_ extract 9 9) shift3)  (concat ((_ extract 16 16) shift3)  (concat ((_ extract 23 23) shift3)  (concat ((_ extract 30 30) shift3)  (concat ((_ extract 37 37) shift3)  (concat ((_ extract 44 44) shift3)  (concat ((_ extract 51 51) shift3)  ((_ extract 58 58) shift3)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 2 2) shift3)  (concat ((_ extract 9 9) shift3)  (concat ((_ extract 16 16) shift3)  (concat ((_ extract 23 23) shift3)  (concat ((_ extract 30 30) shift3)  (concat ((_ extract 37 37) shift3)  (concat ((_ extract 44 44) shift3)  (concat ((_ extract 51 51) shift3)  ((_ extract 58 58) shift3)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 3 3) shift1)  (concat ((_ extract 10 10) shift1)  (concat ((_ extract 17 17) shift1)  (concat ((_ extract 24 24) shift1)  (concat ((_ extract 31 31) shift1)  (concat ((_ extract 38 38) shift1)  (concat ((_ extract 45 45) shift1)  (concat ((_ extract 52 52) shift1)  ((_ extract 59 59) shift1)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 3 3) shift1)  (concat ((_ extract 10 10) shift1)  (concat ((_ extract 17 17) shift1)  (concat ((_ extract 24 24) shift1)  (concat ((_ extract 31 31) shift1)  (concat ((_ extract 38 38) shift1)  (concat ((_ extract 45 45) shift1)  (concat ((_ extract 52 52) shift1)  ((_ extract 59 59) shift1)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 3 3) shift2)  (concat ((_ extract 10 10) shift2)  (concat ((_ extract 17 17) shift2)  (concat ((_ extract 24 24) shift2)  (concat ((_ extract 31 31) shift2)  (concat ((_ extract 38 38) shift2)  (concat ((_ extract 45 45) shift2)  (concat ((_ extract 52 52) shift2)  ((_ extract 59 59) shift2)  ) ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (bitsumhelper  (concat ((_ extract 3 3) shift2)  (concat ((_ extract 10 10) shift2)  (concat ((_ extract 17 17) shift2)  (concat ((_ extract 24 24) shift2)  (concat ((_ extract 31 31) shift2)  (concat ((_ extract 38 38) shift2)  (concat ((_ extract 45 45) shift2)  (concat ((_ extract 52 52) shift2)  ((_ extract 59 59) shift2)  ) ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 3 3) shift3)  (concat ((_ extract 10 10) shift3)  (concat ((_ extract 17 17) shift3)  (concat ((_ extract 24 24) shift3)  (concat ((_ extract 31 31) shift3)  (concat ((_ extract 38 38) shift3)  (concat ((_ extract 45 45) shift3)  (concat ((_ extract 52 52) shift3)  ((_ extract 59 59) shift3)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 3 3) shift3)  (concat ((_ extract 10 10) shift3)  (concat ((_ extract 17 17) shift3)  (concat ((_ extract 24 24) shift3)  (concat ((_ extract 31 31) shift3)  (concat ((_ extract 38 38) shift3)  (concat ((_ extract 45 45) shift3)  (concat ((_ extract 52 52) shift3)  ((_ extract 59 59) shift3)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 4 4) shift1)  (concat ((_ extract 11 11) shift1)  (concat ((_ extract 18 18) shift1)  (concat ((_ extract 25 25) shift1)  (concat ((_ extract 32 32) shift1)  (concat ((_ extract 39 39) shift1)  (concat ((_ extract 46 46) shift1)  (concat ((_ extract 53 53) shift1)  ((_ extract 60 60) shift1)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 4 4) shift1)  (concat ((_ extract 11 11) shift1)  (concat ((_ extract 18 18) shift1)  (concat ((_ extract 25 25) shift1)  (concat ((_ extract 32 32) shift1)  (concat ((_ extract 39 39) shift1)  (concat ((_ extract 46 46) shift1)  (concat ((_ extract 53 53) shift1)  ((_ extract 60 60) shift1)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 4 4) shift2)  (concat ((_ extract 11 11) shift2)  (concat ((_ extract 18 18) shift2)  (concat ((_ extract 25 25) shift2)  (concat ((_ extract 32 32) shift2)  (concat ((_ extract 39 39) shift2)  (concat ((_ extract 46 46) shift2)  (concat ((_ extract 53 53) shift2)  ((_ extract 60 60) shift2)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 4 4) shift2)  (concat ((_ extract 11 11) shift2)  (concat ((_ extract 18 18) shift2)  (concat ((_ extract 25 25) shift2)  (concat ((_ extract 32 32) shift2)  (concat ((_ extract 39 39) shift2)  (concat ((_ extract 46 46) shift2)  (concat ((_ extract 53 53) shift2)  ((_ extract 60 60) shift2)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 4 4) shift3)  (concat ((_ extract 11 11) shift3)  (concat ((_ extract 18 18) shift3)  (concat ((_ extract 25 25) shift3)  (concat ((_ extract 32 32) shift3)  (concat ((_ extract 39 39) shift3)  (concat ((_ extract 46 46) shift3)  (concat ((_ extract 53 53) shift3)  ((_ extract 60 60) shift3)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 4 4) shift3)  (concat ((_ extract 11 11) shift3)  (concat ((_ extract 18 18) shift3)  (concat ((_ extract 25 25) shift3)  (concat ((_ extract 32 32) shift3)  (concat ((_ extract 39 39) shift3)  (concat ((_ extract 46 46) shift3)  (concat ((_ extract 53 53) shift3)  ((_ extract 60 60) shift3)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 5 5) shift1)  (concat ((_ extract 12 12) shift1)  (concat ((_ extract 19 19) shift1)  (concat ((_ extract 26 26) shift1)  (concat ((_ extract 33 33) shift1)  (concat ((_ extract 40 40) shift1)  (concat ((_ extract 47 47) shift1)  (concat ((_ extract 54 54) shift1)  ((_ extract 61 61) shift1)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 5 5) shift1)  (concat ((_ extract 12 12) shift1)  (concat ((_ extract 19 19) shift1)  (concat ((_ extract 26 26) shift1)  (concat ((_ extract 33 33) shift1)  (concat ((_ extract 40 40) shift1)  (concat ((_ extract 47 47) shift1)  (concat ((_ extract 54 54) shift1)  ((_ extract 61 61) shift1)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 5 5) shift2)  (concat ((_ extract 12 12) shift2)  (concat ((_ extract 19 19) shift2)  (concat ((_ extract 26 26) shift2)  (concat ((_ extract 33 33) shift2)  (concat ((_ extract 40 40) shift2)  (concat ((_ extract 47 47) shift2)  (concat ((_ extract 54 54) shift2)  ((_ extract 61 61) shift2)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 5 5) shift2)  (concat ((_ extract 12 12) shift2)  (concat ((_ extract 19 19) shift2)  (concat ((_ extract 26 26) shift2)  (concat ((_ extract 33 33) shift2)  (concat ((_ extract 40 40) shift2)  (concat ((_ extract 47 47) shift2)  (concat ((_ extract 54 54) shift2)  ((_ extract 61 61) shift2)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 5 5) shift3)  (concat ((_ extract 12 12) shift3)  (concat ((_ extract 19 19) shift3)  (concat ((_ extract 26 26) shift3)  (concat ((_ extract 33 33) shift3)  (concat ((_ extract 40 40) shift3)  (concat ((_ extract 47 47) shift3)  (concat ((_ extract 54 54) shift3)  ((_ extract 61 61) shift3)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 5 5) shift3)  (concat ((_ extract 12 12) shift3)  (concat ((_ extract 19 19) shift3)  (concat ((_ extract 26 26) shift3)  (concat ((_ extract 33 33) shift3)  (concat ((_ extract 40 40) shift3)  (concat ((_ extract 47 47) shift3)  (concat ((_ extract 54 54) shift3)  ((_ extract 61 61) shift3)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 6 6) shift1)  (concat ((_ extract 13 13) shift1)  (concat ((_ extract 20 20) shift1)  (concat ((_ extract 27 27) shift1)  (concat ((_ extract 34 34) shift1)  (concat ((_ extract 41 41) shift1)  (concat ((_ extract 48 48) shift1)  (concat ((_ extract 55 55) shift1)  ((_ extract 62 62) shift1)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 6 6) shift1)  (concat ((_ extract 13 13) shift1)  (concat ((_ extract 20 20) shift1)  (concat ((_ extract 27 27) shift1)  (concat ((_ extract 34 34) shift1)  (concat ((_ extract 41 41) shift1)  (concat ((_ extract 48 48) shift1)  (concat ((_ extract 55 55) shift1)  ((_ extract 62 62) shift1)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 6 6) shift2)  (concat ((_ extract 13 13) shift2)  (concat ((_ extract 20 20) shift2)  (concat ((_ extract 27 27) shift2)  (concat ((_ extract 34 34) shift2)  (concat ((_ extract 41 41) shift2)  (concat ((_ extract 48 48) shift2)  (concat ((_ extract 55 55) shift2)  ((_ extract 62 62) shift2)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 6 6) shift2)  (concat ((_ extract 13 13) shift2)  (concat ((_ extract 20 20) shift2)  (concat ((_ extract 27 27) shift2)  (concat ((_ extract 34 34) shift2)  (concat ((_ extract 41 41) shift2)  (concat ((_ extract 48 48) shift2)  (concat ((_ extract 55 55) shift2)  ((_ extract 62 62) shift2)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
(assert (not (= (_ bv0 9)  (bitsumhelper  (concat ((_ extract 6 6) shift3)  (concat ((_ extract 13 13) shift3)  (concat ((_ extract 20 20) shift3)  (concat ((_ extract 27 27) shift3)  (concat ((_ extract 34 34) shift3)  (concat ((_ extract 41 41) shift3)  (concat ((_ extract 48 48) shift3)  (concat ((_ extract 55 55) shift3)  ((_ extract 62 62) shift3)  ) ) ) ) ) ) ) ) ) )))
(assert (= (_ bv0 9)  (bitsumhelper  (bitsumhelper  (concat ((_ extract 6 6) shift3)  (concat ((_ extract 13 13) shift3)  (concat ((_ extract 20 20) shift3)  (concat ((_ extract 27 27) shift3)  (concat ((_ extract 34 34) shift3)  (concat ((_ extract 41 41) shift3)  (concat ((_ extract 48 48) shift3)  (concat ((_ extract 55 55) shift3)  ((_ extract 62 62) shift3)  ) ) ) ) ) ) ) ) ) ) ))
; =========================
; ==== Length of workblocks ====
;
(declare-fun noncyclic_workblocks () (_ BitVec 126))
(declare-fun workblocks_justTrailingOnes () (_ BitVec 63))
(declare-fun workblocks_withoutTrailingOnes () (_ BitVec 63))
(declare-fun workblock_helper () (_ BitVec 126))
(assert (= workblocks_justTrailingOnes (bvnot (bvneg (bvxor shift0 (bvand shift0 (bvsub shift0 (_ bv1 63)))))) ))
(assert (= workblocks_withoutTrailingOnes (bvxor (bvnot shift0) (bvnot (bvneg (bvxor shift0 (bvand shift0 (bvsub shift0 (_ bv1 63))))))) ))
(assert (= noncyclic_workblocks (concat workblocks_justTrailingOnes workblocks_withoutTrailingOnes )))
(assert (= workblock_helper (bvand noncyclic_workblocks  (bvand (bvlshr noncyclic_workblocks (_ bv1 126)) (bvand (bvlshr noncyclic_workblocks (_ bv2 126)) (bvlshr noncyclic_workblocks (_ bv3 126)) ) ) )))
(assert (= noncyclic_workblocks (bvor workblock_helper  (bvor (bvshl workblock_helper (_ bv1 126)) (bvor (bvshl workblock_helper (_ bv2 126)) (bvshl workblock_helper (_ bv3 126)) ) ) )))
(assert (= (bvand noncyclic_workblocks  (bvand (bvlshr noncyclic_workblocks (_ bv1 126)) (bvand (bvlshr noncyclic_workblocks (_ bv2 126)) (bvand (bvlshr noncyclic_workblocks (_ bv3 126)) (bvand (bvlshr noncyclic_workblocks (_ bv4 126)) (bvand (bvlshr noncyclic_workblocks (_ bv5 126)) (bvand (bvlshr noncyclic_workblocks (_ bv6 126)) (bvlshr noncyclic_workblocks (_ bv7 126)) ) ) ) ) ) ) )(_ bv0 126)))
; ==== length of blocks of consecutive shifts ====
;
(declare-fun noncyclic_shift0 () (_ BitVec 126))
(declare-fun shift0_justTrailingOnes () (_ BitVec 63))
(declare-fun shift0_withoutTrailingOnes () (_ BitVec 63))
(assert (= shift0_justTrailingOnes (bvnot (bvneg (bvxor (bvnot shift0) (bvand (bvnot shift0) (bvsub (bvnot shift0) (_ bv1 63)))))) ))
(assert (= shift0_withoutTrailingOnes (bvxor shift0 (bvnot (bvneg (bvxor (bvnot shift0) (bvand (bvnot shift0) (bvsub (bvnot shift0) (_ bv1 63))))))) ))
(assert (= noncyclic_shift0 (concat shift0_justTrailingOnes shift0_withoutTrailingOnes )))
(declare-fun shift0_helper () (_ BitVec 126))
(assert (= shift0_helper (bvand noncyclic_shift0  (bvlshr noncyclic_shift0 (_ bv1 126)) )))
(assert (= noncyclic_shift0 (bvor shift0_helper  (bvshl shift0_helper (_ bv1 126)) )))
(assert (= (bvand (concat shift0 shift0)  (bvand (bvlshr (concat shift0 shift0) (_ bv1 126)) (bvand (bvlshr (concat shift0 shift0) (_ bv2 126)) (bvand (bvlshr (concat shift0 shift0) (_ bv3 126)) (bvlshr (concat shift0 shift0) (_ bv4 126)) ) ) ) )(_ bv0 126)))
(declare-fun noncyclic_shift1 () (_ BitVec 126))
(declare-fun shift1_justTrailingOnes () (_ BitVec 63))
(declare-fun shift1_withoutTrailingOnes () (_ BitVec 63))
(assert (= shift1_justTrailingOnes (bvnot (bvneg (bvxor (bvnot shift1) (bvand (bvnot shift1) (bvsub (bvnot shift1) (_ bv1 63)))))) ))
(assert (= shift1_withoutTrailingOnes (bvxor shift1 (bvnot (bvneg (bvxor (bvnot shift1) (bvand (bvnot shift1) (bvsub (bvnot shift1) (_ bv1 63))))))) ))
(assert (= noncyclic_shift1 (concat shift1_justTrailingOnes shift1_withoutTrailingOnes )))
(declare-fun shift1_helper () (_ BitVec 126))
(assert (= shift1_helper (bvand noncyclic_shift1  (bvlshr noncyclic_shift1 (_ bv1 126)) )))
(assert (= noncyclic_shift1 (bvor shift1_helper  (bvshl shift1_helper (_ bv1 126)) )))
(assert (= (bvand (concat shift1 shift1)  (bvand (bvlshr (concat shift1 shift1) (_ bv1 126)) (bvand (bvlshr (concat shift1 shift1) (_ bv2 126)) (bvand (bvlshr (concat shift1 shift1) (_ bv3 126)) (bvand (bvlshr (concat shift1 shift1) (_ bv4 126)) (bvand (bvlshr (concat shift1 shift1) (_ bv5 126)) (bvand (bvlshr (concat shift1 shift1) (_ bv6 126)) (bvlshr (concat shift1 shift1) (_ bv7 126)) ) ) ) ) ) ) )(_ bv0 126)))
(declare-fun noncyclic_shift2 () (_ BitVec 126))
(declare-fun shift2_justTrailingOnes () (_ BitVec 63))
(declare-fun shift2_withoutTrailingOnes () (_ BitVec 63))
(assert (= shift2_justTrailingOnes (bvnot (bvneg (bvxor (bvnot shift2) (bvand (bvnot shift2) (bvsub (bvnot shift2) (_ bv1 63)))))) ))
(assert (= shift2_withoutTrailingOnes (bvxor shift2 (bvnot (bvneg (bvxor (bvnot shift2) (bvand (bvnot shift2) (bvsub (bvnot shift2) (_ bv1 63))))))) ))
(assert (= noncyclic_shift2 (concat shift2_justTrailingOnes shift2_withoutTrailingOnes )))
(declare-fun shift2_helper () (_ BitVec 126))
(assert (= shift2_helper (bvand noncyclic_shift2  (bvlshr noncyclic_shift2 (_ bv1 126)) )))
(assert (= noncyclic_shift2 (bvor shift2_helper  (bvshl shift2_helper (_ bv1 126)) )))
(assert (= (bvand (concat shift2 shift2)  (bvand (bvlshr (concat shift2 shift2) (_ bv1 126)) (bvand (bvlshr (concat shift2 shift2) (_ bv2 126)) (bvand (bvlshr (concat shift2 shift2) (_ bv3 126)) (bvand (bvlshr (concat shift2 shift2) (_ bv4 126)) (bvand (bvlshr (concat shift2 shift2) (_ bv5 126)) (bvlshr (concat shift2 shift2) (_ bv6 126)) ) ) ) ) ) )(_ bv0 126)))
(declare-fun noncyclic_shift3 () (_ BitVec 126))
(declare-fun shift3_justTrailingOnes () (_ BitVec 63))
(declare-fun shift3_withoutTrailingOnes () (_ BitVec 63))
(assert (= shift3_justTrailingOnes (bvnot (bvneg (bvxor (bvnot shift3) (bvand (bvnot shift3) (bvsub (bvnot shift3) (_ bv1 63)))))) ))
(assert (= shift3_withoutTrailingOnes (bvxor shift3 (bvnot (bvneg (bvxor (bvnot shift3) (bvand (bvnot shift3) (bvsub (bvnot shift3) (_ bv1 63))))))) ))
(assert (= noncyclic_shift3 (concat shift3_justTrailingOnes shift3_withoutTrailingOnes )))
(declare-fun shift3_helper () (_ BitVec 126))
(assert (= shift3_helper (bvand noncyclic_shift3  (bvlshr noncyclic_shift3 (_ bv1 126)) )))
(assert (= noncyclic_shift3 (bvor shift3_helper  (bvshl shift3_helper (_ bv1 126)) )))
(assert (= (bvand (concat shift3 shift3)  (bvand (bvlshr (concat shift3 shift3) (_ bv1 126)) (bvand (bvlshr (concat shift3 shift3) (_ bv2 126)) (bvand (bvlshr (concat shift3 shift3) (_ bv3 126)) (bvlshr (concat shift3 shift3) (_ bv4 126)) ) ) ) )(_ bv0 126)))
; ==== not allowed shift sequences ====
;
(assert (= (_ bv0 63) (bvand ((_ rotate_right 1) shift3) shift1)))
(assert (= (_ bv0 63) (bvand ((_ rotate_right 1) shift3) shift2)))
(assert (= (_ bv0 63) (bvand ((_ rotate_right 1) shift2) shift1)))
(check-sat)
