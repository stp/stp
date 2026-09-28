; The eager policy walks exactly the pairs it charged for.
;
; A pair of two applications whose actuals are all constants is charged nothing,
; because the two are either the same hash-consed handle or they differ at a
; position where both hold constants and the pair is dropped. Being charged
; nothing is only half of what that has to mean: such a pair must not be walked
; either. Charging per congruent part made the charge small enough that
; declarations like this one get selected, and a part of many all-constant
; applications was then enumerated quadratically on a budget of one pair --
; 60 000 applications reached 1 799 970 001 enumerated pairs and 20.5 s against
; 1.5 s with the policy off.
;
; Twelve applications share one literal tag and hold a distinct literal in the
; other position, so all twelve are all-constant and none of the C(12, 2) pairs
; between them can produce anything. Two more share a second tag and hold
; symbolic actuals, which is the one chargeable pair. Estimated and enumerated
; must both read 1: the estimate alone would have read 1 while the walk did 67.
;
; RUN: %solver --uninterpreted-functions --incremental=off -s %s 2>&1 | %OutputCheck %s
; RUN: %solver --uninterpreted-functions --incremental=on -s %s 2>&1 | %OutputCheck %s
; CHECK: UF: eager selected f \(14 applications, 1 pairs estimated, 1 enumerated, 0 impossible, 1 constraints\)
; CHECK: ^sat
;
(set-logic QF_UFBV)
(declare-fun f ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-const p (_ BitVec 8))
(declare-const q (_ BitVec 8))
(assert (or (bvult (f #x01 #x00) #x40) (bvult (f #x01 #x01) #x40)
            (bvult (f #x01 #x02) #x40) (bvult (f #x01 #x03) #x40)
            (bvult (f #x01 #x04) #x40) (bvult (f #x01 #x05) #x40)
            (bvult (f #x01 #x06) #x40) (bvult (f #x01 #x07) #x40)
            (bvult (f #x01 #x08) #x40) (bvult (f #x01 #x09) #x40)
            (bvult (f #x01 #x0a) #x40) (bvult (f #x01 #x0b) #x40)))
(assert (bvult (f #x02 p) #x40))
(assert (bvult (f #x02 q) #x40))
(check-sat)
