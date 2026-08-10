; RUN: %solver %s | %OutputCheck %s
;
; Array models print their true index and element sorts, so a get-model
; line replays against the original declaration: float cells and float
; indexes as (fp ...) literals with a (_ FloatingPoint eb sb) sort,
; RoundingMode cells and indexes by mode name -- not the raw bit carriers
; ((_ BitVec 32) cells and #b01000 modes used to leak out). Also covers
; declare-const of an array sort, which used to exist only for declare-fun.
; (CHECK-L: these patterns hold regex metacharacters -- | -- so the plain
; CHECK form would match vacuously.)
(set-logic QF_ABVFP)
(set-option :produce-models true)
(declare-fun fe () (Array (_ BitVec 2) (_ FloatingPoint 8 24)))
(declare-const re (Array (_ BitVec 2) RoundingMode))
(declare-fun fi () (Array (_ FloatingPoint 8 24) (_ BitVec 8)))
(declare-fun ri () (Array RoundingMode (_ BitVec 8)))
(assert (= (select fe #b01) (fp #b0 #b01111111 #b00000000000000000000000)))
(assert (= (select re #b10) RTZ))
(assert (= (select fi (fp #b0 #b01111111 #b00000000000000000000000)) #x2a))
(assert (= (select ri RNE) #x11))
; CHECK: ^sat
(check-sat)
; The observed reads print sorted by array name, then index.
; CHECK-L: (define-fun |fe| (_ BitVec 2) (_ FloatingPoint 8 24) #b01 (fp #b0 #b01111111 #b00000000000000000000000))
; CHECK-L: (define-fun |fi| (_ FloatingPoint 8 24) (_ BitVec 8) (fp #b0 #b01111111 #b00000000000000000000000) #x2A)
; CHECK-L: (define-fun |re| (_ BitVec 2) RoundingMode #b10 RTZ)
; CHECK-L: (define-fun |ri| RoundingMode (_ BitVec 8) RNE #x11)
(get-model)
