; RUN: %solver %s | %OutputCheck %s
; CHECK: ^unsat
; The instance from stp#444, reduced with ddSMT from Sage2/bench_15307.smt2.
; The second sum is the first plus two copies of a one-bit addend, written
; with different nesting, so the query is unsat only because addition is
; associative and commutative. STP timed out on it until flattening became a
; default; this pins that, and the adder sharing that follows from it.
(set-logic QF_BV)
(declare-const __T1 (_ BitVec 5))
(declare-const __ (_ BitVec 6))
(declare-const _T1 (_ BitVec 3))
(declare-const __T (_ BitVec 6))
(declare-const T1 (_ BitVec 3))
(declare-const T (_ BitVec 7))
(declare-const _T (_ BitVec 1))
(assert
  (let
    ((?x25 ((_ zero_extend 24) ((_ zero_extend 1) ((_ zero_extend 1) __T)))))
    (bvslt
      (_ bv111 32)
      (bvadd
        ((_ zero_extend 24) ((_ zero_extend 4) ((_ zero_extend 1) T1)))
        (bvadd
          ((_ zero_extend 24) ((_ zero_extend 1) T))
          ?x25
          (
            (_ zero_extend 24)
            ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 1) __T1))))
          ((_ zero_extend 24) ((_ zero_extend 4) ((_ zero_extend 1) _T1)))
          ((_ zero_extend 24) ((_ zero_extend 1) ((_ zero_extend 1) __))))))))
(assert
  (let
    (
      (?x1088
        (bvadd
          ((_ zero_extend 24) ((_ zero_extend 7) _T))
          ((_ zero_extend 24) ((_ zero_extend 1) ((_ zero_extend 1) __))))))
    (bvsge
      (_ bv111 32)
      (bvadd
        (bvadd
          ((_ zero_extend 24) ((_ zero_extend 4) ((_ zero_extend 1) T1)))
          (
            (_ zero_extend 24)
            ((_ zero_extend 1) ((_ zero_extend 1) ((_ zero_extend 1) __T1)))))
        ?x1088
        ((_ zero_extend 24) ((_ zero_extend 4) ((_ zero_extend 1) _T1)))
        ((_ zero_extend 24) ((_ zero_extend 1) ((_ zero_extend 1) __T)))
        (bvadd
          ((_ zero_extend 24) ((_ zero_extend 7) _T))
          ((_ zero_extend 24) ((_ zero_extend 1) T)))))))
(check-sat)
