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
; Array definitions print sorted by name, with the observed cells stored.
; CHECK-L: (define-fun |fe| () (Array (_ BitVec 2) (_ FloatingPoint 8 24)) (store ((as const (Array (_ BitVec 2) (_ FloatingPoint 8 24))) (fp #b0 #b00000000 #b00000000000000000000000)) #b01 (fp #b0 #b01111111 #b00000000000000000000000)))
; CHECK-L: (define-fun |fi| () (Array (_ FloatingPoint 8 24) (_ BitVec 8)) (store ((as const (Array (_ FloatingPoint 8 24) (_ BitVec 8))) #x00) (fp #b0 #b01111111 #b00000000000000000000000) #x2A))
; CHECK-L: (define-fun |re| () (Array (_ BitVec 2) RoundingMode) (store ((as const (Array (_ BitVec 2) RoundingMode)) RNE) #b10 RTZ))
; CHECK-L: (define-fun |ri| () (Array RoundingMode (_ BitVec 8)) (store ((as const (Array RoundingMode (_ BitVec 8))) #x00) RNE #x11))
(get-model)
