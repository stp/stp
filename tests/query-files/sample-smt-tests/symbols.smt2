; RUN: %solver %s | %OutputCheck %s
; CHECK-NEXT: ^sat
(set-logic QF_BV)
(set-info :source |
	Constructed by Trevor Hansen to test edge case parsing
|)
(set-info :smt-lib-version 2.0)
(set-info :category "check")
(set-info :status sat)

;The SMT-LIB Standard Version 2.0, Release: March 30, 2010

; :notes is a reserved keyword; but not notes without the colon.
(declare-fun notes () (_ BitVec 4))

;Symbols. A symbol is either a non-empty sequence of letters, digits and the characters
;~ ! @ $ % ^ & * _ - + = < > . ? / that does not start with a digit, or a sequence of
;printable ASCII characters, including white spaces, that starts and ends with | and does
;not otherwise contain | .

; Other more difficult things that are allowed, but seem ridiculous are:
; Having /n in symbol names.
; Having symbol names that are functions in other theories: +, /

(declare-fun | | () (_ BitVec 4))
(declare-fun || () (_ BitVec 4))
(declare-fun ?v0 () (_ BitVec 4))
(declare-fun v0 () (_ BitVec 4))
(declare-fun |v1| () (_ BitVec 4))
(declare-fun V0 () (_ BitVec 4))
(declare-fun ~!@$%^&*_-+=><.?/() (_ BitVec 4))
; We put () inside the ||'s 'cause you can.
(declare-fun |~!@$%^&*_-+=<>.?/()|() (_ BitVec 4))
(declare-fun |~!@$%^&*_-+=<>.?/|() (_ BitVec 4))
(assert (distinct notes || |~!@$%^&*_-+=<>.?/()| ?v0 |v0| v1 V0 ~!@$%^&*_-+=><.?/))
(assert (not (= v0 V0)))
(assert (not (= |~!@$%^&*_-+=<>.?/| ~!@$%^&*_-+=><.?/)))
(assert (not (= || | |)))
(assert (distinct (distinct || | | )(distinct |~!@$%^&*_-+=<>.?/|  v0)))
(check-sat)
(exit)
