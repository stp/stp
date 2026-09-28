; Explicit first engagement may preprocess a complete plain-BV stack as one
; assumption-scoped block when the trial at least halves the DAG.  The first
; scope collapses to model definitions: its deeper literals satisfy the base
; disjunction without encoding the huge-root shape this policy targets.
;
; The next check exercises the transition to the ordinary driver.  Nothing
; from the first scoped block was made permanent: the raw base and its new
; conjunct are encoded normally, and a later pushed contradiction is seen.
; RUN: %solver --incremental --incremental-profile --check-sanity %s 2>&1 | %OutputCheck %s
; RUN: %solver -s --incremental --incremental-profile %s 2>&1 | %OutputCheck --check-prefix=LAZY %s
(set-option :produce-models true)
(set-logic QF_BV)
(declare-fun p00 () Bool)
(declare-fun p01 () Bool)
(declare-fun p02 () Bool)
(declare-fun p03 () Bool)
(declare-fun p04 () Bool)
(declare-fun p05 () Bool)
(declare-fun p06 () Bool)
(declare-fun p07 () Bool)
(declare-fun p08 () Bool)
(declare-fun p09 () Bool)
(declare-fun p10 () Bool)
(declare-fun p11 () Bool)
(declare-fun p12 () Bool)
(declare-fun p13 () Bool)
(declare-fun p14 () Bool)
(declare-fun p15 () Bool)
(declare-fun p16 () Bool)
(declare-fun p17 () Bool)
(declare-fun p18 () Bool)
(declare-fun p19 () Bool)
(declare-fun p20 () Bool)
(declare-fun p21 () Bool)
(declare-fun p22 () Bool)
(declare-fun p23 () Bool)
(declare-fun p24 () Bool)
(declare-fun p25 () Bool)
(declare-fun p26 () Bool)
(declare-fun p27 () Bool)
(declare-fun p28 () Bool)
(declare-fun p29 () Bool)
(declare-fun p30 () Bool)
(declare-fun p31 () Bool)
(declare-fun p32 () Bool)
(declare-fun p33 () Bool)
(declare-fun p34 () Bool)
(declare-fun p35 () Bool)
(declare-fun p36 () Bool)
(declare-fun p37 () Bool)
(declare-fun p38 () Bool)
(declare-fun p39 () Bool)
(declare-fun p40 () Bool)
(declare-fun p41 () Bool)
(declare-fun p42 () Bool)
(declare-fun p43 () Bool)
(declare-fun p44 () Bool)
(declare-fun p45 () Bool)
(declare-fun p46 () Bool)
(declare-fun p47 () Bool)
(declare-fun p48 () Bool)
(declare-fun p49 () Bool)
(declare-fun p50 () Bool)
(declare-fun p51 () Bool)
(declare-fun p52 () Bool)
(declare-fun p53 () Bool)
(declare-fun p54 () Bool)
(declare-fun p55 () Bool)
(declare-fun p56 () Bool)
(declare-fun p57 () Bool)
(declare-fun p58 () Bool)
(declare-fun p59 () Bool)
(declare-fun p60 () Bool)
(declare-fun p61 () Bool)
(declare-fun p62 () Bool)
(declare-fun p63 () Bool)
(declare-fun p64 () Bool)
(declare-fun p65 () Bool)
(declare-fun p66 () Bool)
(declare-fun p67 () Bool)
(declare-fun p68 () Bool)
(declare-fun p69 () Bool)
(assert (or p00 p01 p02 p03 p04 p05 p06 p07 p08 p09 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50 p51 p52 p53 p54 p55 p56 p57 p58 p59 p60 p61 p62 p63 p64 p65 p66 p67 p68 p69))
(push 1)
(assert (and (not p00) (not p01) (not p02) (not p03) (not p04) (not p05) (not p06) (not p07) (not p08) (not p09) (not p10) (not p11) (not p12) (not p13) (not p14) (not p15) (not p16) (not p17) (not p18) (not p19) (not p20) (not p21) (not p22) (not p23) (not p24) (not p25) (not p26) (not p27) (not p28) (not p29) (not p30) (not p31) (not p32) (not p33) (not p34) (not p35) (not p36) (not p37) (not p38) (not p39) (not p40) (not p41) (not p42) (not p43) (not p44) (not p45) (not p46) (not p47) (not p48) (not p49) (not p50) (not p51) (not p52) (not p53) (not p54) (not p55) (not p56) (not p57) (not p58) (not p59) (not p60) (not p61) (not p62) (not p63) (not p64) (not p65) (not p66) (not p67) (not p68)))
; CHECK: Incremental profile cbp/backend: check=1 .*extensionality=0 first-stack-preprocesses=1 first-stack-eliminations=[1-9][0-9]* first-stack-rejected=0
; CHECK: ^sat
; LAZY: Incremental: first scoped BV round, block of 2 levels encoded
; LAZY: Incremental profile cbp/backend: check=1 .*sat-calls=1 refinement-sat-calls=0 refinement-rounds=0 .*extensionality=0 first-stack-preprocesses=1 first-stack-eliminations=[1-9][0-9]* first-stack-rejected=0
; LAZY: ^sat
(check-sat)
; CHECK: \|p00\| +false
; CHECK: \|p69\| +true
; LAZY: Incremental: model materialized on demand
; LAZY: \|p00\| +false
; LAZY: \|p69\| +true
(get-value (p00 p69))
(pop 1)

; The exact-stack round deliberately did not populate level0Asserted.  This
; growing base must therefore enter as ordinary permanent roots now.
(assert (not p00))
; CHECK: Incremental profile cbp/backend: check=2 .*extensionality=0 first-stack-preprocesses=0 first-stack-eliminations=0 first-stack-rejected=0
; CHECK: ^sat
; LAZY: Incremental profile cbp/backend: check=2 .*sat-calls=1 refinement-sat-calls=0 refinement-rounds=0 .*extensionality=0 first-stack-preprocesses=0 first-stack-eliminations=0 first-stack-rejected=0
; LAZY: ^sat
(check-sat)
; CHECK: \|p00\| +false
; LAZY: Incremental: model materialized on demand
; LAZY: \|p00\| +false
(get-value (p00))

(push 1)
(assert (and (not p01) (not p02) (not p03) (not p04) (not p05) (not p06) (not p07) (not p08) (not p09) (not p10) (not p11) (not p12) (not p13) (not p14) (not p15) (not p16) (not p17) (not p18) (not p19) (not p20) (not p21) (not p22) (not p23) (not p24) (not p25) (not p26) (not p27) (not p28) (not p29) (not p30) (not p31) (not p32) (not p33) (not p34) (not p35) (not p36) (not p37) (not p38) (not p39) (not p40) (not p41) (not p42) (not p43) (not p44) (not p45) (not p46) (not p47) (not p48) (not p49) (not p50) (not p51) (not p52) (not p53) (not p54) (not p55) (not p56) (not p57) (not p58) (not p59) (not p60) (not p61) (not p62) (not p63) (not p64) (not p65) (not p66) (not p67) (not p68) (not p69)))
; CHECK: Incremental profile cbp/backend: check=3 .*extensionality=0 first-stack-preprocesses=0 first-stack-eliminations=0 first-stack-rejected=0
; CHECK: ^unsat
; LAZY: Incremental profile cbp/backend: check=3 .*sat-calls=1 refinement-sat-calls=0 refinement-rounds=0 .*extensionality=0 first-stack-preprocesses=0 first-stack-eliminations=0 first-stack-rejected=0
; LAZY: ^unsat
(check-sat)
(pop 1)
(exit)
