; RUN: %solver --array-equality %s | %OutputCheck %s
; RUN: %solver --array-equality -r %s | %OutputCheck %s
; RUN: %solver --incremental=on --array-equality %s | %OutputCheck %s
; RUN: %solver --incremental=on --array-equality -r %s | %OutputCheck %s
;
; A cell of an array of rounding modes holds one of the five modes -- the
; cells an array equality introduces after the pinning pass has run included.
;
; RoundingMode is carried in five bits, one-hot, so twenty-seven of the
; thirty-two carriers name no mode at all. Every mode a query names is pinned
; to the five: by its declaration, and by FpTotalise at solve time, which
; covers the reads the formula names as well as its symbols. An equality
; between a chain of writes and its own base is not abstracted at all,
; though -- it is rewritten, each write contributing "the base's cell at this
; index is the value written, unless a later write shadowed it"
; (ExtensionalityContext::solveWriteChain). The cells that rewrite reads are
; new reads, minted after FpTotalise has run, and nothing pinned them.
;
; One free carrier could therefore witness all five of these disequalities at
; once: a[i] naming no mode differs from every mode there is. There are only
; five, and the five assertions exclude each of them, so this is
; unsatisfiable. STP answered "sat" on all four routes below.
;
; The array transform now pins the cells it mints, as the array-equality
; checker already pinned its own virtual reads. The sibling
; array-rm-abstracted-cell-is-a-mode.smt2 covers the transform's other
; minting site.
;
; CHECK: ^unsat
(set-logic QF_ABVFP)
(declare-fun a () (Array RoundingMode RoundingMode))
(declare-fun i () RoundingMode)
(assert (not (= (store a i RNE) a)))
(assert (not (= (store a i RNA) a)))
(assert (not (= (store a i RTP) a)))
(assert (not (= (store a i RTN) a)))
(assert (not (= (store a i RTZ) a)))
(check-sat)
(exit)
