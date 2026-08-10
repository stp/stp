;id:1	verified_to:0	time:0	from_difficulty:0	to_difficulty:0
(push 1)
; Valid rewrite rules, used to smoke test rewrite_rule_gen:
;   rewrite_rule_gen verify tools/rewrite_rule_gen/test-rules.smt2
;
; Format note: load_new_rules() reads the tab-separated ";id:..." line of each
; block with sscanf and stops parsing the moment a line does not match, so
; comments cannot appear before a header or between blocks -- only inside one,
; like this, where the SMT2 parser handles them.
;
; These are deliberately rules the SimplifyingNodeFactory does not already
; know. Anything it can fold collapses to from == to when the loader rebuilds
; the rule with that factory, and is then dropped as unorderable, so the
; obvious candidates (De Morgan, bvsub as add-negate, double negation) are
; unusable here. The absorption and consensus laws below survive.
(set-logic QF_BV)
(declare-fun v () (_ BitVec 6))
(declare-fun w () (_ BitVec 6))
(assert (= (bvand v (bvor v w)) v))
(exit)
;id:2	verified_to:0	time:0	from_difficulty:0	to_difficulty:0
(push 1)
(set-logic QF_BV)
(declare-fun v () (_ BitVec 6))
(declare-fun w () (_ BitVec 6))
(assert (= (bvor v (bvand v w)) v))
(exit)
;id:3	verified_to:0	time:0	from_difficulty:0	to_difficulty:0
(push 1)
(set-logic QF_BV)
(declare-fun v () (_ BitVec 6))
(declare-fun w () (_ BitVec 6))
(assert (= (bvor (bvand v w) (bvand v (bvnot w))) v))
(exit)
;id:4	verified_to:0	time:0	from_difficulty:0	to_difficulty:0
(push 1)
(set-logic QF_BV)
(declare-fun v () (_ BitVec 6))
(declare-fun w () (_ BitVec 6))
(assert (= (bvand (bvor v w) (bvor v (bvnot w))) v))
(exit)
