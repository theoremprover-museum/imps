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


(herald counting-theorem)

(load-section basic-group-theory)
(load-section basic-cardinality)

(include-files
  (files (imps theories/groups/group-cardinality)))



;;; Counting theorem theory

(def-language COUNTING-THEOREM-LANGUAGE
  (embedded-language group-actions-language)
  (constants
    (zeta uu)))

(def-theory COUNTING-THEOREM-THEORY
  (language counting-theorem-language)
  (component-theories group-actions))


;;; Definitions

(def-constant FCT%MAPPING
  "lambda(beta:uu, 
     iota(c:sets[gg], 
       forsome(g:gg, 
         c = right%trans(stabilizer(zeta),g) and beta = act(zeta,g))))"
  (theory counting-theorem-theory))

(def-constant STABILIZER%RIGHT%COSETS
  "indic{a:sets[gg], forsome(g:gg, a = right%trans(stabilizer(zeta),g))}"
  (theory counting-theorem-theory))


;;; FCT%MAPPING lemmas

(include-files
  (files (imps theories/groups/counting-theorem-lemmas)))


;;; Cardinality lemmas

(def-theorem CARDINALITY-OF-ZETA-ORBIT
  "orbit(zeta) equinumerous stabilizer%right%cosets"
  lemma
  (theory counting-theorem-theory)
  (proof
   (
    (instantiate-existential ("fct%mapping"))
    insistent-direct-inference
    insistent-direct-inference
    (apply-macete-with-minor-premises domain-of-fct-mapping)
    (apply-macete-with-minor-premises range-of-fct-mapping)
    (apply-macete-with-minor-premises tr%injective-implies-injective-on)
    (apply-macete-with-minor-premises injectiveness-of-fct-mapping)
    )))

(def-theorem CARDINALITY-OF-A-FINITE-ZETA-ORBIT
  "f_indic_q{orbit(zeta)} 
     implies 
   f_card{orbit(zeta)} = f_card{stabilizer%right%cosets}"
  reverse
  lemma
  (theory counting-theorem-theory)
  (proof
   (
    direct-inference
    (apply-macete-with-minor-premises 
     tr%finite-and-equinumerous-implies-f-card-equal)
    (apply-macete-with-minor-premises cardinality-of-zeta-orbit)
    )))

(def-theorem STABILIZER%RIGHT%COSETS-ARE-EQUINUMEROUS
  "forall(a:sets[gg],
     a in stabilizer%right%cosets implies a equinumerous stabilizer(zeta))"
  lemma
  (theory counting-theorem-theory)
  (proof
   (
    (unfold-single-defined-constant-globally stabilizer%right%cosets)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, p)")
    simplify
    (contrapose "with(p:prop, p)")
    (antecedent-inference "with(p:prop, p)")
    (backchain "with(p:prop, p)")
    (weaken (0))
    (force-substitution 
     "stabilizer(zeta)" "right%trans(stabilizer(zeta),e)" (1))
    (apply-macete-with-minor-premises right-cosets-are-equinumerous)
    (apply-macete-with-minor-premises trivial-right-translation)
    )))

(def-theorem STABILIZER%RIGHT%COSETS-HAVE-EQUAL-F-CARD
  "forall(a:sets[gg],
     f_indic_q{stabilizer(zeta)} and a in stabilizer%right%cosets 
       implies 
     f_card{a} = f_card{stabilizer(zeta)})"
  lemma
  (theory counting-theorem-theory)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises 
     tr%f-card-equal-iff-finite-and-equinumerous)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises 
     stabilizer%right%cosets-are-equinumerous)
    (apply-macete-with-minor-premises 
     stabilizer%right%cosets-are-equinumerous)
    )))

(def-theorem FINITENESS-OF-ZETA-STABILIZER
  "f_indic_q{gg%subgroup} implies f_indic_q{stabilizer(zeta)}"
  lemma
  (theory counting-theorem-theory)
  (proof
   (
    direct-inference
    (apply-macete-with-minor-premises finiteness-of-stabilizers)
    )))

(def-theorem STABILIZER%RIGHT%COSETS-IS-A-PARTITION
  "partition_q{stabilizer%right%cosets,gg%subgroup}"
  lemma
  (theory counting-theorem-theory)
  (proof
   (
    (unfold-single-defined-constant-globally stabilizer%right%cosets)
    insistent-direct-inference
    simplify
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(v,u:sets[gg],not(u=v))")
    (backchain "with(g_$0:gg,u:sets[gg],u=right%trans(stabilizer(zeta),g_$0))")
    (backchain "with(g_$0:gg,u:sets[gg],u=right%trans(stabilizer(zeta),g_$0))")
    (backchain "with(g:gg,v:sets[gg],v=right%trans(stabilizer(zeta),g))")
    (backchain "with(g:gg,v:sets[gg],v=right%trans(stabilizer(zeta),g))")
    (weaken (0 1))
    (instantiate-theorem 
     overlapping-right-cosets ("stabilizer(zeta)" "g_$0" "g"))
    (contrapose "with(p:prop, p)")
    (apply-macete-with-minor-premises stabilizers-are-subgroups)
    simplify
    simplify
    (weaken (0))
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("right%trans(stabilizer(zeta),x)"))
    (instantiate-existential ("x"))
    (unfold-single-defined-constant-globally right%trans)
    simplify
    (instantiate-existential ("e"))
    (apply-macete-with-minor-premises subgroups-contain-e)
    (apply-macete-with-minor-premises stabilizers-are-subgroups)
    simplify
    (unfold-single-defined-constant-globally gg%subgroup)
    simplify
    )))

(def-theorem FINITENESS-OF-ZETA-ORBIT
  "f_indic_q{gg%subgroup} implies f_indic_q{orbit(zeta)}"
  (theory counting-theorem-theory)
  (proof
   (
    direct-inference
    (assume-theorem cardinality-of-zeta-orbit)
    (cut-with-single-formula 
     "f_card{orbit(zeta)} = f_card{stabilizer%right%cosets}")
    (apply-macete-with-minor-premises 
     tr%f-card-equal-iff-finite-and-equinumerous)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula 
     "partition_q{stabilizer%right%cosets,gg%subgroup}")
    (apply-macete-with-minor-premises tr%finiteness-of-a-partition)
    (antecedent-inference "partition_q{stabilizer%right%cosets,gg%subgroup};")
    (instantiate-existential ("gg%subgroup"))
    (apply-macete-with-minor-premises stabilizer%right%cosets-is-a-partition)
    )))

(def-theorem FINITENESS-OF-ORBITS
  finiteness-of-zeta-orbit
  ;; "forall(zeta:uu, 
  ;;    f_indic_q{gg%subgroup} implies f_indic_q{orbit(zeta)})"
  (theory group-actions)
  (home-theory counting-theorem-theory)
  (usages transportable-macete)
  (proof existing-theorem))


;;; Fundamental Counting Theorem

(def-theorem FUNDAMENTAL-COUNTING-THEOREM
  "f_indic_q{gg%subgroup} 
     implies 
   f_card{gg%subgroup} = f_card{stabilizer(zeta)} * f_card{orbit(zeta)}"
  ;; "forall(zeta:uu, 
  ;;    f_indic_q{gg%subgroup} 
  ;;      implies
  ;;    f_card{gg%subgroup}=f_card{stabilizer(zeta)}*f_card{orbit(zeta)})"
  (theory group-actions)
  (home-theory counting-theorem-theory)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    (cut-with-single-formula "f_indic_q{stabilizer(zeta)}")
    (cut-with-single-formula "f_indic_q{orbit(zeta)}")
    (cut-with-single-formula 
     "f_card{orbit(zeta)}=f_card{stabilizer%right%cosets}")
    (backchain "f_card{orbit(zeta)}=f_card{stabilizer%right%cosets}")
    (assume-theorem stabilizer%right%cosets-is-a-partition)
    (antecedent-inference "partition_q{stabilizer%right%cosets,gg%subgroup}")
    (apply-macete-with-minor-premises tr%finite-uniform-partition-theorem)
    direct-inference
    (apply-macete stabilizer%right%cosets-have-equal-f-card)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises rev%cardinality-of-a-finite-zeta-orbit)
    (apply-macete-with-minor-premises finiteness-of-zeta-orbit)
    (apply-macete-with-minor-premises finiteness-of-zeta-stabilizer)
    )))


;;; APPLICATIONS OF FUNDAMENTAL COUNTING THEOREM


;;; Lagrange's theorem

(def-theorem LAGRANGES-THEOREM
  "forall(a:sets[gg], 
     f_indic_q{gg%subgroup} and subgroup(a) 
       implies 
     forsome(m:nn, f_card{gg%subgroup} = m * f_card{a}))"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-transported-theorem 
     fundamental-counting-theorem 
     act->right%trans 
     ("a"))
    (force-substitution "a" "indic{g:gg,right%trans(a,g)=a}" (0))
    (instantiate-existential ("f_card{right%cosets(a)}"))
    simplify
    (apply-macete-with-minor-premises subgroup-is-right%trans-stabilizer)
    (apply-macete-with-minor-premises tr%dom-of-an-indicator)
    )))


;;; Index of a normalizer

(def-constant CONJUGATE%CLASS
  "lambda(g:gg, indic{h:gg, forsome(i:gg, h = inv(i) mul g mul i)})"
  (theory groups))

(def-constant NORMALIZER
  "lambda(g:gg, indic{h:gg, inv(h) mul g mul h = g})"
  (theory groups))

(def-theorem INDEX-OF-NORMALIZER
  "forall(g:gg, 
     f_indic_q{gg%subgroup}
       implies
     f_card{gg%subgroup} = 
     f_card{normalizer(g)}*f_card{conjugate%class(g)})"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (assume-transported-theorem 
     fundamental-counting-theorem act->conjugate)
    )))
     

;;; Index of a set normalizer

(def-constant SET%CONJUGATE%CLASS
  "lambda(a:sets[gg], 
     indic{b:sets[gg], forsome(g:gg, b = set%conjugate(a,g))})"
  (theory groups))

(def-constant SET%NORMALIZER
  "lambda(a:sets[gg], indic{g:gg, set%conjugate(a,g) = a})"
  (theory groups))

(def-theorem INDEX-OF-SET-NORMALIZER
  "forall(a:sets[gg],
     f_indic_q{gg%subgroup}
       implies
     f_card{gg%subgroup} = 
     f_card{set%normalizer(a)}*f_card{set%conjugate%class(a)})"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    (assume-transported-theorem 
     fundamental-counting-theorem act->set%conjugate)
    )))


