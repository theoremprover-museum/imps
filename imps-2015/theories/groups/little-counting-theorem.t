;% Copyright (c) 1990-1994 The MITRE Corporation
;% 
;% Authors: W. M. Farmer, J. D. Guttman, F. J. Thayer
;%   
;% The MITRE Corporation (MITRE) provides this software to you without
;% charge to use, copy, modify or enhance for any legitimate purpose
;% provided you reproduce MITRE's copyright notice in any copy or
;% derivative work of this software.
;% 
;% This software is the copyright work of MITRE.  No ownership or other
;% proprietary interest in this software is granted you other than what
;% is granted in this license.
;% 
;% Any modification or enhancement of this software must identify the
;% part of this software that was modified, by whom and when, and must
;% inherit this license including its warranty disclaimers.
;% 
;% MITRE IS PROVIDING THE PRODUCT "AS IS" AND MAKES NO WARRANTY, EXPRESS
;% OR IMPLIED, AS TO THE ACCURACY, CAPABILITY, EFFICIENCY OR FUNCTIONING
;% OF THIS SOFTWARE AND DOCUMENTATION.  IN NO EVENT WILL MITRE BE LIABLE
;% FOR ANY GENERAL, CONSEQUENTIAL, INDIRECT, INCIDENTAL, EXEMPLARY OR
;% SPECIAL DAMAGES, EVEN IF MITRE HAS BEEN ADVISED OF THE POSSIBILITY OF
;% SUCH DAMAGES.
;% 
;% You, at your expense, hereby indemnify and hold harmless MITRE, its
;% Board of Trustees, officers, agents and employees, from any and all
;% liability or damages to third parties, including attorneys' fees,
;% court costs, and other related costs and expenses, arising out of your
;% use of this software irrespective of the cause of said liability.
;% 
;% The export from the United States or the subsequent reexport of this
;% software is subject to compliance with United States export control
;% and munitions control restrictions.  You agree that in the event you
;% seek to export this software or any derivative work thereof, you
;% assume full responsibility for obtaining all necessary export licenses
;% and approvals and for assuring compliance with applicable reexport
;% restrictions.
;% 
;% 
;% COPYRIGHT NOTICE INSERTED: Mon Apr 11 11:42:27 EDT 1994


(herald LITTLE-COUNTING-THEOREM)


(load-section fundamental-counting-theorem)



;;; Little counting theorem theory

(def-language LCT-LANGUAGE
  (embedded-language groups)
  (constants
    (a "sets[gg]")
    (b "sets[gg]")))

(def-theory LCT-THEORY
  (language lct-language)
  (component-theories groups)
  (axioms 
   (a-is-a-subgroup "subgroup(a)")
   (b-is-a-subgroup "subgroup(b)")))


;;; Macete and rewrites

(def-compound-macete LCT-MACETE
  (repeat
   subgroup-membership
   a-is-a-subgroup
   b-is-a-subgroup))

(def-theorem A-CONTAINS-E
  "e in a"
  (theory lct-theory)
  (usages rewrite)
  (proof
   (
    (apply-macete-with-minor-premises lct-macete)
    )))

(def-theorem B-CONTAINS-E
  "e in b"
  (theory lct-theory)
  (usages rewrite)
  (proof
   (
    (apply-macete-with-minor-premises lct-macete)
    )))


;;; Definitions

(def-atomic-sort B%SORT
  "lambda(x:gg, x in b)"
  (theory lct-theory)
  (witness "e"))

(def-constant A%COSETS
  "indic{c:sets[gg], forsome(g:gg, g in b and c = right%trans(a,g))}"
  (theory lct-theory))

(def-theorem A%COSETS-CONTAINS-A
  "a in a%cosets"
  (theory lct-theory)
  (proof
   (
    (unfold-single-defined-constant-globally a%cosets)
    simplify
    (instantiate-existential ("e"))
    simplify
    (apply-macete-with-minor-premises trivial-right-translation)
    )))

(def-atomic-sort A%COSETS%SORT
  "lambda(x:sets[gg], x in a%cosets)"
  (theory lct-theory)
  (witness "a"))


;;; Preliminary lemmas

(def-theorem A-IS-DEFINED-IN-A%COSETS%SORT
  "#(a,a%cosets%sort)"
  lemma
  (theory lct-theory)
  (usages rewrite)
  (proof
   (
    (apply-macete-with-minor-premises a%cosets%sort-defining-axiom_lct-theory)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises a%cosets-contains-a)
    )))

;; The following theorem is installed instead of 
;;
;;    "forall(x:b%sort, x in b)"
;;
;; because this latter expression is recognized by IMPS as 
;; 
;;    "total_q{b,sets[b%sort]}", 
;;
;; which is not very useful as a macete.

(def-theorem B%SORT-MEMBERS-ARE-IN-B
  "forall(x:b%sort, x=x implies x in b)"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem b%sort-defining-axiom_lct-theory ("x"))
    (contrapose "with(x:b%sort,not(#(x,b%sort)))")
    )))

(def-theorem B-IS-TOTAL
  "total_q{b,sets[b%sort]} iff truth"
  (theory lct-theory)
  (usages rewrite)
  (proof
   (
    simplify
    insistent-direct-inference
    (apply-macete-with-minor-premises 
     b%sort-members-are-in-b)
    )))
   
(def-theorem A%COSETS%SORT-MEMBERS-ARE-IN-A%COSETS
  "forall(x:a%cosets%sort, x=x implies x in a%cosets)"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem a%cosets%sort-defining-axiom_lct-theory ("x"))
    (contrapose "with(x:a%cosets%sort,not(#(x,a%cosets%sort)))")
    )))

(def-theorem A%COSETS-IS-TOTAL
  "total_q{a%cosets,sets[a%cosets%sort]} iff truth"
  (theory lct-theory)
  (usages rewrite)
  (proof
   (
    simplify
    insistent-direct-inference
    (apply-macete-with-minor-premises 
     a%cosets%sort-members-are-in-a%cosets)
    )))


;;; Obligations

(include-files
  (files (imps theories/groups/lct-obligations)))


;;; Translation

(def-translation LCT-INTERPRETATION
  (source group-actions)
  (target lct-theory)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (gg "b%sort")
   (uu "a%cosets%sort"))
  (constant-pairs
   (mul "restrict2{mul,b,b}")
   (inv "restrict{inv,b}")
   (act "restrict2{right%trans,a%cosets,b}"))
  force-under-quick-load
  (theory-interpretation-check using-simplification))

(def-renamer LCT-RENAMER
  (pairs
   (gg%subgroup lct%gg%subgroup)
   (orbit lct%orbit)
   (stabilizer lct%stabilizer)))

(def-transported-symbols 
  (gg%subgroup orbit stabilizer)
  (translation lct-interpretation)
  (renamer lct-renamer))


;;; Lemmas

(def-theorem FINITENESS-OF-A
  "f_indic_q{gg%subgroup} implies f_indic_q{a}"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-inference
    (apply-macete-with-minor-premises finiteness-of-subgroups)
    (apply-macete-with-minor-premises a-is-a-subgroup)
    )))

(def-theorem FINITENESS-OF-B
  "f_indic_q{gg%subgroup} implies f_indic_q{b}"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-inference
    (apply-macete-with-minor-premises finiteness-of-subgroups)
    (apply-macete-with-minor-premises b-is-a-subgroup)
    )))

(def-theorem FINITENESS-OF-A-INTERS-B
  "f_indic_q{gg%subgroup} implies f_indic_q{a inters b}"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-inference
    (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
    (instantiate-existential ("gg%subgroup"))
    insistent-direct-inference
    (unfold-single-defined-constant-globally gg%subgroup)
    simplify
    )))

(def-theorem FINITENESS-OF-AB
  "f_indic_q{gg%subgroup} implies f_indic_q{a set%mul b}"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-inference
    (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
    (instantiate-existential ("gg%subgroup"))
    insistent-direct-inference
    unfold-defined-constants
    simplify
    )))

(def-theorem B-IS-LCT%GG%SUBGROUP
  "b=lct%gg%subgroup"
  lemma
  reverse
  (theory lct-theory)
  (proof
   (
    (unfold-single-defined-constant-globally lct%gg%subgroup)
    extensionality
    direct-inference
    (case-split ("#(x_0,b%sort)"))
    simplify
    (apply-macete-with-minor-premises 
     tr%value-of-a-defined-indicator-application)
    (apply-macete-with-minor-premises b%sort-members-are-in-b)
    simplify
    (contrapose "with(p:prop,p)")
    simplify
    )))

(def-theorem F-CARD-OF-B
  "f_card{b} == f_card{lct%gg%subgroup}"
  lemma
  reverse
  (theory lct-theory)
  (proof
   (

    (apply-macete-with-minor-premises 
     tr%equinumerous-implies-f-card-quasi-equal)
    (instantiate-existential ("id{b}"))
    (apply-macete-with-minor-premises tr%dom-of-id)
    (block 
     (script-comment "node added by `instantiate-existential' at (0 0 1)")
     (unfold-single-defined-constant-globally lct%gg%subgroup)
     extensionality
     direct-inference
     simplify
     (apply-macete-with-minor-premises b%sort-members-are-in-b))
    (apply-macete-with-minor-premises tr%id-is-injective-on-dom)
    (block 
     (script-comment "node added by `instantiate-existential' at (1)")
     sort-definedness
     simplify)

    )))

(def-theorem FINITENESS-OF-LCT%GG%SUBGROUP
  "f_indic_q{b} implies f_indic_q{lct%gg%subgroup}"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-inference
    (assume-theorem f-card-of-b)
    )))

(def-theorem LCT%ORBIT-OF-A-IS-A%COSETS
  "lct%orbit(a)=a%cosets"
  lemma
  (theory lct-theory)
  (proof
   (

    unfold-defined-constants
    extensionality
    direct-inference
    (case-split ("#(x_0,a%cosets%sort)"))
    (block 
     (script-comment "node added by `case-split' at (1)")
     simplify
     direct-and-antecedent-inference-strategy
     auto-instantiate-existential
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (1 0 0)")
      (contrapose "with(p:prop,not(p));")
      auto-instantiate-existential
      (apply-macete-with-minor-premises a%cosets-contains-a)))
    (block 
     (script-comment "node added by `case-split' at (2)")
     simplify
     direct-and-antecedent-inference-strategy
     (contrapose "with(p:prop,not(p));")
     (apply-macete-with-minor-premises 
      a%cosets%sort-defining-axiom_lct-theory)
     (unfold-single-defined-constant-globally a%cosets)
     simplify
     auto-instantiate-existential)

    )))

(def-theorem F-CARD-OF-LCT%ORBIT-AT-A
  "f_card{lct%orbit(a)} == f_card{a%cosets}"
  lemma
  (theory lct-theory)
  (proof
   (

    (assume-theorem lct%orbit-of-a-is-a%cosets)
    (apply-macete-with-minor-premises 
     tr%equinumerous-implies-f-card-quasi-equal)
    (instantiate-existential ("id{lct%orbit(a)}"))
    insistent-direct-inference
    (block 
     (script-comment "node added by `insistent-direct-inference' at (0)")
     insistent-direct-inference
     (apply-macete-with-minor-premises tr%dom-of-id)
     (block 
      (script-comment "node added by `insistent-direct-inference' at (1)")
      (backchain "with(f:sets[a%cosets%sort],f=a%cosets);")
      extensionality
      direct-inference
      simplify))
    (apply-macete-with-minor-premises tr%id-is-injective-on-dom)

    )))

(def-theorem LCT%STABILIZER-OF-A-IS-A-INTERS-B
  "lct%stabilizer(a) = a inters b"
  lemma
  (theory lct-theory)
  (proof
   (

    (unfold-single-defined-constant-globally lct%stabilizer)
    extensionality
    direct-inference
    (case-split ("#(x_0,b%sort)"))
    (block 
     (script-comment "node added by `case-split' at (1)")
     simplify
     (apply-macete-with-minor-premises subgroup-is-right%trans-stabilizer)
     (block 
      (script-comment 
       "node added by `apply-macete-with-minor-premises' at (0)")
      direct-and-antecedent-inference-strategy
      (contrapose "with(p:prop,not(p));")
      (apply-macete-with-minor-premises a%cosets-contains-a)
      simplify)
     (apply-macete-with-minor-premises a-is-a-subgroup))
    (block 
     (script-comment "node added by `case-split' at (2)")
     simplify
     (contrapose "with(p:prop,p);")
     (apply-macete-with-minor-premises b%sort-defining-axiom_lct-theory))

    )))

(def-theorem F-CARD-OF-LCT%STABILIZER-AT-A
  "f_card{lct%stabilizer(a)} == f_card{a inters b}"
  lemma
  (theory lct-theory)
  (proof
   (

    (assume-theorem lct%stabilizer-of-a-is-a-inters-b)
    (apply-macete-with-minor-premises 
     tr%equinumerous-implies-f-card-quasi-equal)
    (instantiate-existential ("id{lct%stabilizer(a)}"))
    insistent-direct-inference
    (block 
     (script-comment "node added by `insistent-direct-inference' at (0)")
     insistent-direct-inference
     (apply-macete-with-minor-premises tr%dom-of-id)
     (block 
      (script-comment "node added by `insistent-direct-inference' at (1)")
      (backchain "lct%stabilizer(a)=a inters b;")
      extensionality
      direct-inference
      simplify))
    (apply-macete-with-minor-premises tr%id-is-injective-on-dom)

    )))

(def-theorem A%COSETS-IS-A-PARTITION-OF-AB
  "partition_q{a%cosets, a set%mul b}"
  lemma
  (theory lct-theory)
  (proof
   (

    unfold-defined-constants
    insistent-direct-inference
    (block 
     (script-comment "node added by `insistent-direct-inference' at (0)")
     simplify
     direct-and-antecedent-inference-strategy
     (incorporate-antecedent "with(p:prop,not(p));")
     (force-substitution "u " "right%trans(a,g_$0)" (0 1))
     (force-substitution "v" "right%trans(a,g)" (0 1))
     (weaken (0 1 2 3))
     (instantiate-theorem overlapping-right-cosets ("a" "g_$0" "g"))
     (block 
      (script-comment "node added by `instantiate-theorem' at (0 0)")
      (contrapose "with(p:prop,p);")
      (apply-macete-with-minor-premises a-is-a-subgroup))
     simplify
     simplify)
    (block 
     (script-comment "node added by `insistent-direct-inference' at (1)")
     (weaken (0))
     simplify
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (0 0 0 0)")
      (instantiate-existential ("right%trans(a,i)"))
      (instantiate-existential ("i"))
      (block 
       (script-comment "node added by `instantiate-existential' at (0 1)")
       (unfold-single-defined-constant-globally right%trans)
       simplify
       auto-instantiate-existential))
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (0 1 0 0 0 0)")
      (incorporate-antecedent "with(x:gg,u:sets[gg],x in u);")
      (backchain "with(f,u:sets[gg],u=f);")
      (unfold-single-defined-constant-globally right%trans)
      (weaken (1))
      simplify
      direct-and-antecedent-inference-strategy
      (instantiate-existential ("g" "i"))))

    )))

(def-theorem FINITENESS-OF-A%COSETS
  "f_indic_q{gg%subgroup} implies f_indic_q{a%cosets}"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-inference
    (assume-theorem a%cosets-is-a-partition-of-ab)
    (antecedent-inference "partition_q{a%cosets,a set%mul b}")
    (apply-macete-with-minor-premises tr%finiteness-of-a-partition)
    auto-instantiate-existential
    (apply-macete-with-minor-premises finiteness-of-ab)
    )))

(def-theorem A%COSETS-ARE-EQUINUMEROUS
  "forall(c:sets[gg],
     c in a%cosets implies c equinumerous a)"
  lemma
  (theory lct-theory)
  (proof
   (
    (unfold-single-defined-constant-globally a%cosets)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, p)")
    simplify
    (contrapose "with(p:prop, p)")
    (antecedent-inference "with(p:prop, p)")
    (backchain "with(p:prop, p)")
    (weaken (0))
    (force-substitution "a" "right%trans(a,e)" (1))
    (apply-macete-with-minor-premises right-cosets-are-equinumerous)
    (apply-macete-with-minor-premises trivial-right-translation)
    )))

(def-theorem A%COSETS-HAVE-EQUAL-F-CARD
  "forall(c:sets[gg],
     f_indic_q{a} and c in a%cosets implies f_card{c} = f_card{a})"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%f-card-equal-iff-finite-and-equinumerous)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises a%cosets-are-equinumerous)
    (apply-macete-with-minor-premises a%cosets-are-equinumerous)
    )))

(def-theorem A-HAS-POSITIVE-F-CARD
  "f_indic_q{gg%subgroup} implies 0 < f_card{a}"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-inference
    (cut-with-single-formula "f_indic_q{a}")
    (apply-macete-with-minor-premises tr%positive-f-card-iff-nonempty)
    (instantiate-existential ("e"))
    simplify
    (apply-macete-with-minor-premises finiteness-of-a)
    )))

(def-theorem A%COSETS-HAS-POSITIVE-F-CARD
  "f_indic_q{gg%subgroup} implies 0 < f_card{a%cosets}"
  lemma
  (theory lct-theory)
  (proof
   (
    direct-inference
    (cut-with-single-formula "f_indic_q{a%cosets}")
    (apply-macete-with-minor-premises tr%positive-f-card-iff-nonempty)
    (instantiate-existential ("a"))
    (apply-macete-with-minor-premises a%cosets-contains-a)
    (apply-macete-with-minor-premises finiteness-of-a%cosets)
    )))


;;; Little counting theorem

(def-theorem LITTLE-COUNTING-THEOREM
  "f_indic_q{gg%subgroup}
     implies
   f_card{a set%mul b}*f_card{a inters b} = f_card{a}*f_card{b}"
  ;; "forall(b,a:sets[gg],
  ;;    subgroup(a) and subgroup(b) 
  ;;     implies 
  ;;    (f_indic_q{gg%subgroup}
  ;;     implies 
  ;;    f_card{a set%mul b}*f_card{a inters b} = f_card{a}*f_card{b}))"
  (theory groups)
  (home-theory lct-theory)
  (usages transportable-macete)
  (proof				; 50 nodes
   (
    direct-inference
    (cut-with-single-formula "0<f_card{a}")
    (cut-with-single-formula "f_indic_q{b}")
    (cut-with-single-formula "0<f_card{a%cosets}")
    (cut-with-single-formula "f_indic_q{lct%gg%subgroup}")
    (cut-with-single-formula "f_indic_q{a set%mul b}")
    (cut-with-single-formula "f_indic_q{a inters b}")
    (apply-macete-with-minor-premises f-card-of-b)
    (instantiate-transported-theorem 
     fundamental-counting-theorem 
     lct-interpretation 
     ("a"))
    (backchain "with(m,n:nn, m=n)")
    (apply-macete-with-minor-premises f-card-of-lct%orbit-at-a)
    (apply-macete-with-minor-premises f-card-of-lct%stabilizer-at-a)
    (assume-theorem a%cosets-is-a-partition-of-ab)
    (instantiate-transported-theorem 
     finite-uniform-partition-theorem 
     () 
     ("a%cosets" "a set%mul b" "f_card{a}"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises a%cosets-have-equal-f-card)
    (apply-macete-with-minor-premises a%cosets-contains-a)
    (backchain "f_card{a set%mul b}=f_card{a}*f_card{a%cosets}")
    simplify
    (apply-macete-with-minor-premises finiteness-of-a-inters-b)
    (apply-macete-with-minor-premises finiteness-of-ab)
    (apply-macete-with-minor-premises finiteness-of-lct%gg%subgroup)
    (apply-macete-with-minor-premises a%cosets-has-positive-f-card)
    (apply-macete-with-minor-premises finiteness-of-b)
    (apply-macete-with-minor-premises a-has-positive-f-card)
    )))




