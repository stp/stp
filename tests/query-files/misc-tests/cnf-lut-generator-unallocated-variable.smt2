; A CNF generator that names a variable it never allocated.
;
; ABC's LUT-cut generator gives a CNF variable only to an object whose
; mapping reference count is non-zero, and the exact-area round maintains
; those counts in a 16-bit bitfield with unchecked increments and decrements.
; On an AIG this size the bookkeeping decrements a counter that is already
; zero, which wraps it, and an AND node that is still a leaf of two live best
; cuts ends up reading zero references. It is then written into its users'
; clauses as ABC's "no variable" marker of -1 -- a negative literal, which the
; shift that recovers a variable turns into ~0u.
;
; The clause cannot be stated. Loading it asserted in a debug build; in a
; release build the index reached the backend, which wrote outside arrays
; sized by nVars() and segfaulted inside addClause. Nor is there a sound way
; to keep the formula: the node whose variable is missing has no defining
; clauses either, so minting a fresh one leaves the gates above it
; unconstrained and the encoding an over-approximation of the query.
;
; So the conversion checks what it adopted and, finding this, derives the CNF
; again with the generator that does not map. What this file pins is that the
; query is answered: the other seven effort levels all say sat. The warning is
; deliberately not checked -- fix the reference counting in ABC and the
; fallback stops firing, which should not fail this test.
;
; From push/pop fuzzing, reduced. --cnf-generation-effort=high is the whole
; trigger; the session it came from needed nothing else either.
; RUN: %solver --cnf-generation-effort=high %s 2>&1 | %OutputCheck %s
; CHECK: ^sat
(set-logic QF_ABVFP)
(declare-fun v1173692 () (_ FloatingPoint 11 53))
(declare-fun v1173693 () Float64)
(declare-fun v1173694 () Float32)
(declare-fun v1173695 () Float64)
(declare-fun v1173696 () Float128)
(declare-fun v1173697 () (_ FloatingPoint 15 113))
(declare-fun rm1173698 () RoundingMode)
(declare-fun v1173699 () (_ BitVec 5))
(declare-fun a1173700 () (Array (_ FloatingPoint 8 24) (_ FloatingPoint 15 113)))
(declare-fun a1173701 () (Array (_ FloatingPoint 11 53) (_ BitVec 1)))
(assert (let ((e1173893 (fp #b0 (_ bv0 8) (_ bv0 23)))) (let ((e1173894 ((_ to_fp_unsigned 8
24) roundTowardNegative (_ bv0 3)))) (let ((e1173895 (fp (_ bv0 1) (_ bv0 5) (_ bv0 10)))) (let
((e1173896 (_ bv0 6))) (let ((e1173897 (bvnand (_ bv0 6) (_ bv0 6)))) (let ((e1173898 (bvsub
((_ sign_extend 1) (_ bv0 5)) (_ bv0 6)))) (let ((e1173899 (store a1173700 v1173694 v1173697)))
(let ((e1173900 (store a1173701 v1173695 ((_ extract 5 5) e1173897)))) (let ((e1173901 (store
a1173700 (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) v1173696))) (let ((e1173902 (store a1173700 (fp (_
bv0 1) (_ bv0 8) (_ bv0 23)) (fp (_ bv0 1) (_ bv0 15) (_ bv0 112))))) (let ((e1173903 (fp (_
bv0 1) (_ bv0 8) (_ bv0 23)))) (let ((e1173904 (select a1173700 (fp (_ bv0 1) (_ bv0 8) (_ bv0
23))))) (let ((e1173905 (select e1173899 e1173894))) (let ((e1173906 (select a1173700
e1173894))) (let ((e1173907 (select e1173902 e1173894))) (let ((e1173908 (select e1173900
v1173695))) (let ((e1173909 (select a1173701 v1173695))) (let ((e1173910 (select e1173901
v1173694))) (let ((e1173911 (select a1173701 (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))))) (let
((e1173912 (store a1173701 (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)) (_ bv0 1)))) (let ((e1173913
(store e1173901 (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) (fp (_ bv0 1) (_ bv0 15) (_ bv0 112)))))
(let ((e1173914 (select e1173902 (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))) (let ((e1173915 (select
e1173912 v1173695))) (let ((e1173916 (select e1173900 (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))))
(let ((e1173917 (select e1173912 v1173695))) (let ((e1173918 (store a1173700 e1173893
v1173696))) (let ((e1173919 (select e1173901 (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))) (let
((e1173920 (select e1173902 v1173694))) (let ((e1173921 (store e1173900 v1173693 (_ bv0 1))))
(let ((e1173922 (select e1173912 v1173695))) (let ((e1173923 (select e1173913 e1173893))) (let
((e1173924 ((_ to_fp_unsigned 8 24) rm1173698 e1173922))) (let ((e1173925 ((_ to_fp_unsigned 11
53) roundTowardNegative e1173922))) (let ((e1173926 ((_ to_fp 11 53) ((_ sign_extend 63)
e1173917)))) (let ((e1173927 (fp.abs e1173893))) (let ((e1173928 (ite (fp.geq (fp (_ bv0 1) (_
bv0 8) (_ bv0 23)) (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))) e1173919 e1173910))) (let ((e1173929
(fp.mul RTN (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))) (let
((e1173930 (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))) (let ((e1173931 (fp (_ bv0 1) (_ bv0 11) (_
bv0 52)))) (let ((e1173932 (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)))) (let ((e1173933 (fp (_ bv0 1)
(_ bv0 11) (_ bv0 52)))) (let ((e1173934 (fp.neg e1173920))) (let ((e1173935 (fp.neg
v1173696))) (let ((e1173936 (fp.div roundNearestTiesToEven (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))
(fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))) (let ((e1173937 (fp.abs e1173905))) (let ((e1173938
(fp.abs e1173903))) (let ((e1173939 (fp.div RTP e1173924 ((_ to_fp 8 24) RTZ e1173934)))) (let
((e1173940 (ite (fp.eq e1173937 ((_ to_fp 15 113) RNE e1173925)) e1173937 ((_ to_fp 15 113) RTN
e1173925)))) (let ((e1173941 (fp.rem v1173692 ((_ to_fp 11 53) RTZ e1173940)))) (let ((e1173942
(fp.div roundTowardNegative v1173695 (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))))) (let ((e1173943
(fp (_ bv0 1) (_ bv0 8) (_ bv0 23)))) (let ((e1173944 (fp.sub rm1173698 (fp (_ bv0 1) (_ bv0 8)
(_ bv0 23)) ((_ to_fp 8 24) RNE e1173941)))) (let ((e1173945 (fp.abs e1173920))) (let
((e1173946 (ite false (fp (_ bv0 1) (_ bv0 5) (_ bv0 10)) (fp (_ bv0 1) (_ bv0 5) (_ bv0
10))))) (let ((e1173947 (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)))) (let ((e1173948 (fp (_ bv0 1) (_
bv0 8) (_ bv0 23)))) (let ((e1173949 (fp.sqrt RNE e1173944))) (let ((e1173950 (fp.sub
roundTowardPositive e1173906 (fp (_ bv0 1) (_ bv0 15) (_ bv0 112))))) (let ((e1173951 ((_
fp.to_ubv 16) RTN v1173693))) (let ((e1173952 ((_ fp.to_ubv 6) roundTowardPositive e1173904)))
(let ((e1173953 ((_ fp.to_sbv 15) RTN e1173949))) (let ((e1173954 (store e1173901 e1173944
e1173907))) (let ((e1173955 (store e1173913 e1173927 e1173940))) (let ((e1173956 (store
a1173700 e1173932 e1173950))) (let ((e1173957 (store e1173900 e1173933 e1173908))) (let
((e1173958 (select e1173918 e1173893))) (let ((e1173959 (select e1173899 e1173944))) (let
((e1173960 (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)))) (let ((e1173961 (fp (_ bv0 1) (_ bv0 8) (_ bv0
23)))) (let ((e1173962 (select e1173956 (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))))) (let ((e1173963
(fp (_ bv0 1) (_ bv0 8) (_ bv0 23)))) (let ((e1173964 (select e1173900 e1173925))) (let
((e1173965 (select e1173956 e1173944))) (let ((e1173966 (select e1173900 v1173692))) (let
((e1173967 (fp.isPositive e1173905))) (let ((e1173968 (fp.isInfinite e1173945))) (let
((e1173969 (fp.leq e1173925 (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))))) (let ((e1173970 false))
(let ((e1173971 false)) (let ((e1173972 false)) (let ((e1173973 false)) (let ((e1173974 false))
(let ((e1173975 false)) (let ((e1173976 false)) (let ((e1173977 false)) (let ((e1173978 false))
(let ((e1173979 false)) (let ((e1173980 false)) (let ((e1173981 false)) (let ((e1173982 false))
(let ((e1173983 false)) (let ((e1173984 false)) (let ((e1173985 false)) (let ((e1173986 false))
(let ((e1173987 false)) (let ((e1173988 false)) (let ((e1173989 false)) (let ((e1173990 false))
(let ((e1173991 false)) (let ((e1173992 false)) (let ((e1173993 false)) (let ((e1173994 false))
(let ((e1173995 false)) (let ((e1173996 (fp.geq (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) (fp (_ bv0
1) (_ bv0 8) (_ bv0 23))))) (let ((e1173997 false)) (let ((e1173998 false)) (let ((e1173999
false)) (let ((e1174000 (fp.isZero e1173903))) (let ((e1174001 false)) (let ((e1174002 false))
(let ((e1174003 false)) (let ((e1174004 false)) (let ((e1174005 false)) (let ((e1174006 (fp.eq
v1173696 e1173935))) (let ((e1174007 (fp.isNormal e1173906))) (let ((e1174008 (fp.lt e1173910
((_ to_fp 15 113) roundNearestTiesToEven e1173895) e1173940))) (let ((e1174009 (fp.isInfinite
e1173924))) (let ((e1174010 false)) (let ((e1174011 false)) (let ((e1174012 false)) (let
((e1174013 false)) (let ((e1174014 false)) (let ((e1174015 false)) (let ((e1174016 (bvsmulo (_
bv0 6) e1173898))) (let ((e1174017 (bvumulo e1173911 e1173964))) (let ((e1174018 (bvugt
v1173699 v1173699))) (let ((e1174019 (bvsdivo e1173908 e1173911))) (let ((e1174020 (bvsle
e1173917 e1173911))) (let ((e1174021 (bvult e1173908 e1173916))) (let ((e1174022 (bvsle ((_
sign_extend 5) e1173908) e1173952))) (let ((e1174023 (bvslt e1173898 ((_ zero_extend 5)
e1173911)))) (let ((e1174024 (bvslt e1173916 e1173964))) (let ((e1174025 (bvuaddo ((_
zero_extend 4) e1173917) v1173699))) (let ((e1174026 (bvule e1173911 e1173917))) (let
((e1174027 (= e1173953 ((_ zero_extend 14) e1173964)))) (let ((e1174028 (= e1173896 ((_
sign_extend 5) e1173909)))) (let ((e1174029 false)) (let ((e1174030 false)) (let ((e1174031
false)) (let ((e1174032 (distinct ((_ zero_extend 5) e1173917) e1173952))) (let ((e1174033
(bvult e1173953 ((_ sign_extend 9) e1173952)))) (let ((e1174034 (bvsmulo e1173908 e1173908)))
(let ((e1174035 (bvsle v1173699 ((_ sign_extend 4) e1173909)))) (let ((e1174036 (bvult e1173922
e1173915))) (let ((e1174039 (and e1173980 false false))) (let ((e1174040 false)) (let
((e1174041 (=> e1174019 e1174004))) (let ((e1174042 (= e1174034 e1173973))) (let ((e1174043
(xor e1173986 e1173986 e1174028))) (let ((e1174044 (distinct e1174007 e1174035))) (let
((e1174045 (distinct e1173983 e1174001))) (let ((e1174046 (or e1174043 e1174017))) (let
((e1174047 (not e1174042))) (let ((e1174048 (=> e1174026 false))) (let ((e1174049 false)) (let
((e1174050 false)) (let ((e1174051 false)) (let ((e1174052 false)) (let ((e1174053 false)) (let
((e1174054 false)) (let ((e1174055 false)) (let ((e1174056 false)) (let ((e1174057 false)) (let
((e1174058 (or e1174046 false))) (let ((e1174059 false)) (let ((e1174060 false)) (let
((e1174061 (or e1174057 e1174049))) (let ((e1174062 (=> e1174033 e1174008 e1174058))) (let
((e1174063 (ite e1173972 e1174009 e1173978))) (let ((e1174064 (xor e1173995 e1173970))) (let
((e1174065 (= e1173968 e1174000))) (let ((e1174066 (and e1174014 e1174036 e1173999))) (let
((e1174067 (or e1174055 false))) (let ((e1174068 false)) (let ((e1174069 false)) (let
((e1174070 false)) (let ((e1174071 false)) (let ((e1174072 (or true e1173982))) (let ((e1174073
(=> e1174068 e1174032))) (let ((e1174074 (xor e1173987 e1173998 e1174041))) (let ((e1174075
(not e1173969))) (let ((e1174076 (ite e1174029 e1174023 e1174070))) (let ((e1174077 (and
e1174025 false false))) (let ((e1174078 false)) (let ((e1174079 (= e1174076 e1173988
e1174076))) (let ((e1174080 false)) (let ((e1174081 false)) (let ((e1174082 (or e1174064
e1174016 e1174054))) (let ((e1174083 (ite e1174074 e1174062 e1174065))) (let ((e1174084 (=
e1174071 e1174077 e1174075))) (let ((e1174085 (xor e1174053 e1174082))) (let ((e1174086
(distinct e1174073 false))) (let ((e1174087 false)) (let ((e1174088 false)) (let ((e1174089
false)) (let ((e1174090 false)) (let ((e1174091 false)) (let ((e1174092 false)) (let ((e1174093
(= e1174083 e1173993 e1174083))) (let ((e1174094 (or false false false))) (let ((e1174095
false)) (let ((e1174096 (ite e1174094 e1174093 e1174093))) (let ((e1174097 (ite e1174090
e1174095 e1174090))) (let ((e1174098 (= e1174096 e1174096 e1174097)))
e1174098))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)))))))))))))))))))))
(check-sat)
