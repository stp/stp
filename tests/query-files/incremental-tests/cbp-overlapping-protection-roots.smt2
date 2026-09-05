; A shallow CBP feed fixes every node in a long, shared arithmetic spine.
; Before preparing the deeper level, the incremental driver must protect the
; union of symbols in all eligible fixed domains: these domains heavily
; overlap, so the union is deliberately collected in one DAG traversal.
; This is a small semantic canary for the first-engagement path which appears
; at much larger scale in CPAchecker QF_BV queries.
; RUN: %solver --incremental --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental-auto-engage-at 1 --check-sanity %s | %OutputCheck %s
; RUN: %solver --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck --check-prefix=PROFILE %s
; RUN: %solver --incremental --incremental-profile --incremental-cbp-bootstrap-limit 1 --check-sanity %s 2>&1 | %OutputCheck --check-prefix=DEFER %s
(set-logic QF_BV)
(declare-fun x00 () (_ BitVec 16))
(declare-fun x01 () (_ BitVec 16))
(declare-fun x02 () (_ BitVec 16))
(declare-fun x03 () (_ BitVec 16))
(declare-fun x04 () (_ BitVec 16))
(declare-fun x05 () (_ BitVec 16))
(declare-fun x06 () (_ BitVec 16))
(declare-fun x07 () (_ BitVec 16))
(declare-fun x08 () (_ BitVec 16))
(declare-fun x09 () (_ BitVec 16))
(declare-fun x10 () (_ BitVec 16))
(declare-fun x11 () (_ BitVec 16))
(declare-fun x12 () (_ BitVec 16))
(declare-fun x13 () (_ BitVec 16))
(declare-fun x14 () (_ BitVec 16))
(declare-fun x15 () (_ BitVec 16))
(define-fun s01 () (_ BitVec 16) (bvxor x00 x01))
(define-fun s02 () (_ BitVec 16) (bvxor s01 x02))
(define-fun s03 () (_ BitVec 16) (bvxor s02 x03))
(define-fun s04 () (_ BitVec 16) (bvxor s03 x04))
(define-fun s05 () (_ BitVec 16) (bvxor s04 x05))
(define-fun s06 () (_ BitVec 16) (bvxor s05 x06))
(define-fun s07 () (_ BitVec 16) (bvxor s06 x07))
(define-fun s08 () (_ BitVec 16) (bvxor s07 x08))
(define-fun s09 () (_ BitVec 16) (bvxor s08 x09))
(define-fun s10 () (_ BitVec 16) (bvxor s09 x10))
(define-fun s11 () (_ BitVec 16) (bvxor s10 x11))
(define-fun s12 () (_ BitVec 16) (bvxor s11 x12))
(define-fun s13 () (_ BitVec 16) (bvxor s12 x13))
(define-fun s14 () (_ BitVec 16) (bvxor s13 x14))
(define-fun s15 () (_ BitVec 16) (bvxor s14 x15))

(push 1)
; Two partial constraints fix each symbol without presenting equality
; propagation with a whole-symbol definition.  The deeper XOR is therefore
; folded by CBP itself, rather than by the definition context.
(assert (and (= ((_ extract 15 8) x00) #x00) (= ((_ extract 7 0) x00) #x00)
             (= ((_ extract 15 8) x01) #x00) (= ((_ extract 7 0) x01) #x01)
             (= ((_ extract 15 8) x02) #x00) (= ((_ extract 7 0) x02) #x02)
             (= ((_ extract 15 8) x03) #x00) (= ((_ extract 7 0) x03) #x03)
             (= ((_ extract 15 8) x04) #x00) (= ((_ extract 7 0) x04) #x04)
             (= ((_ extract 15 8) x05) #x00) (= ((_ extract 7 0) x05) #x05)
             (= ((_ extract 15 8) x06) #x00) (= ((_ extract 7 0) x06) #x06)
             (= ((_ extract 15 8) x07) #x00) (= ((_ extract 7 0) x07) #x07)
             (= ((_ extract 15 8) x08) #x00) (= ((_ extract 7 0) x08) #x08)
             (= ((_ extract 15 8) x09) #x00) (= ((_ extract 7 0) x09) #x09)
             (= ((_ extract 15 8) x10) #x00) (= ((_ extract 7 0) x10) #x0a)
             (= ((_ extract 15 8) x11) #x00) (= ((_ extract 7 0) x11) #x0b)
             (= ((_ extract 15 8) x12) #x00) (= ((_ extract 7 0) x12) #x0c)
             (= ((_ extract 15 8) x13) #x00) (= ((_ extract 7 0) x13) #x0d)
             (= ((_ extract 15 8) x14) #x00) (= ((_ extract 7 0) x14) #x0e)
             (= ((_ extract 15 8) x15) #x00) (= ((_ extract 7 0) x15) #x0f)))
(push 1)
(assert (= s15 #x0000))
; CHECK-NEXT: ^sat
; PROFILE: Incremental profile cbp/backend: check=1 .*cbp-adoptions=1 .*cbp-deferred-restored=[1-9][0-9]+
; PROFILE: ^sat
; DEFER: Incremental profile cbp/backend: check=1 .*cbp-fed-levels=0 .*cbp-bootstrap-deferred=1
; DEFER: ^sat
(check-sat)
(assert (distinct s15 #x0000))
; CHECK-NEXT: ^unsat
; PROFILE: ^unsat
; DEFER: Incremental profile cbp/backend: check=2 .*cbp-fed-levels=[1-9][0-9]* .*cbp-bootstrap-deferred=0
; DEFER: ^unsat
(check-sat)
(pop 1)
(pop 1)
(exit)
