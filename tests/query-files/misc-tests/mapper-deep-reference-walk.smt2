; REQUIRES: prlimit
; RUN: prlimit --stack=786432 -- %solver --cnf-generation-effort=gia-low %s | %OutputCheck %s
; CHECK: ^sat$
;
; ABC's mapper, which turns the blasted circuit into CNF under every effort
; but very-low, medium and the new- rungs, has an exact-area round that walks
; the mapping's reference counts down the chain of best cuts. That chain is as
; long as the mapped logic is deep, and the walk used to recurse once per cut.
; A wide divider is deep: at 512 bits the recursion overflowed the 8MiB stack
; a process gets, and STP died of SIGSEGV generating the CNF. The walk now
; keeps its own stack.
;
; Reduced with ddSMT from QF_BV/20220315-ecrw/rw_rule_candidate_vmcai_2022_bw512_4.smt2
; in SMT-LIB, then narrowed to 256 bits and run in 768KiB of stack instead of
; 8MiB, which makes it take a third of a second rather than several. The
; recursion needed about 2MiB here; everything else the run does needs about
; 270KiB, most of it the bit-blaster's divider, which recurses once per bit.
; 768KiB is a factor of about 2.8 from each, which is how far another
; compiler's frame sizes can move either way before the test stops telling a
; build with the recursion from one without it.
;
; The divisor is t's low bit, so the remainder is t itself when t is even and
; 0 when it is odd: any even t but 0 satisfies it. Nothing before the blast
; notices, so the whole divider is mapped.
(set-logic QF_BV)
(declare-const t (_ BitVec 255))
(assert (distinct (_ bv0 256) (bvurem ((_ zero_extend 1) t) (bvand (_ bv1 256) ((_ zero_extend 1) t)))))
(check-sat)
