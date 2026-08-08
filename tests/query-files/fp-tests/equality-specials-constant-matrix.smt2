; RUN: %solver %s | %OutputCheck %s
; RUN: %solver --disable-simplifications %s | %OutputCheck %s
; RUN: %solver --bb.fp-native-cmp=false %s | %OutputCheck %s
;
; The specials matrix again, but written as LITERALS, so it lands on the
; constant path -- the node-creation folders and the constant evaluator --
; rather than on a blasted circuit. Both operators, all pairs.
;
; The NaN rows are the reason this file exists as a separate test: three
; different NaN bit patterns are used (canonical quiet, a payload-1 pattern
; with the quiet bit clear, and one with the sign bit set and yet another
; payload). All three denote the single SMT-LIB NaN, so `=` must hold
; between any two of them and fp.eq between none. A constant path that
; compared packed bits, or that let a payload survive interning, gets these
; backwards -- and it cannot be caught by comparing two symbolic NaNs,
; because the two spellings only ever meet as constants here.
;
; CHECK: ^unsat
(set-logic QF_FP)
(assert (not (and
  ; --- fp.eq: zeros equal, NaN never, infinities by sign ---
  (fp.eq ((_ to_fp 8 24) #x00000000) ((_ to_fp 8 24) #x80000000))
  (fp.eq ((_ to_fp 8 24) #x80000000) ((_ to_fp 8 24) #x00000000))
  (fp.eq ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #x7F800000))
  (fp.eq ((_ to_fp 8 24) #xFF800000) ((_ to_fp 8 24) #xFF800000))
  (not (fp.eq ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #xFF800000)))
  (not (fp.eq ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x7FC00000)))
  (not (fp.eq ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x7F800001)))
  (not (fp.eq ((_ to_fp 8 24) #x7F800001) ((_ to_fp 8 24) #xFFC12345)))
  (not (fp.eq ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x00000000)))
  (not (fp.eq ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #x3F800000)))

  ; --- = : zeros distinct, all NaNs identified, infinities by sign ---
  (not (= ((_ to_fp 8 24) #x00000000) ((_ to_fp 8 24) #x80000000)))
  (not (= ((_ to_fp 8 24) #x80000000) ((_ to_fp 8 24) #x00000000)))
  (= ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #x7F800000))
  (= ((_ to_fp 8 24) #xFF800000) ((_ to_fp 8 24) #xFF800000))
  (not (= ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #xFF800000)))
  (= ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x7FC00000))
  (= ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x7F800001))
  (= ((_ to_fp 8 24) #x7F800001) ((_ to_fp 8 24) #xFFC12345))
  (= ((_ to_fp 8 24) #xFFC12345) ((_ to_fp 8 24) #x7FC00000))
  (not (= ((_ to_fp 8 24) #x7FC00000) ((_ to_fp 8 24) #x00000000)))
  (not (= ((_ to_fp 8 24) #x7F800000) ((_ to_fp 8 24) #x3F800000)))
)))
(check-sat)
(exit)
