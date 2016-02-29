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


(herald finite-cardinality)

(load-section foundation)


;;; Parsing and printing

(def-parse-syntax equinumerous
  (left-method infix-operator-method) 
  (binding 160))

(def-parse-syntax embeds
  (left-method infix-operator-method) 
  (binding 160))

(def-print-syntax equinumerous
  (token " equinumerous ")
  (method present-non-associative-infix-operator) 
  (binding 160))

(def-print-syntax embeds
  (token " embeds ")
  (method present-non-associative-infix-operator) 
  (binding 160))


;;; Quasi-constructors

(def-quasi-constructor EQUINUMEROUS
  "lambda(a:sets[ind_1],b:sets[ind_2], 
     forsome(f:[ind_1,ind_2], bijective_on_q(f,a,b)))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))

(def-quasi-constructor EMBEDS
  "lambda(a:sets[ind_1],b:sets[ind_2], 
     forsome(f:[ind_1,ind_2],
       dom(f)=a and (ran(f) subseteq b) and injective_on_q(f,a)))"
  (language pure-generic-theory-2)
  (fixed-theories the-kernel-theory))


;;; Equinumerous lemmas

(def-theorem EQUINUMEROUS-IS-REFLEXIVE
  "forall(a:sets[ind_1], a equinumerous a)"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof				; 10 nodes
   (
    direct-inference
    (instantiate-existential ("id{a}"))
    insistent-direct-inference
    insistent-direct-inference
    (apply-macete-with-minor-premises dom-of-id)
    (apply-macete-with-minor-premises ran-of-id)
    (apply-macete-with-minor-premises id-is-injective-on-dom)
    )))

(def-theorem EQUINUMEROUS-IS-SYMMETRIC
  "forall(a:sets[ind_1],b:sets[ind_2], 
     (a equinumerous b) implies (b equinumerous a))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("inverse{f}"))
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises dom-of-inverse)
    (apply-macete-with-minor-premises injective-iff-injective-on-domain)
    simplify
    (apply-macete-with-minor-premises ran-of-inverse)
    (instantiate-theorem inverse-is-injective ("f"))
    (backchain "with(f:[ind_1,ind_2],injective_q{inverse{f}})")
    )))

(def-theorem EQUINUMEROUS-IS-TRANSITIVE
  "forall(a:sets[ind_1],b:sets[ind_2],c:sets[ind_3],
     (a equinumerous b) and (b equinumerous c) implies (a equinumerous c))"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("f_$0 oo f"))
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises domain-composition)
    (apply-macete-with-minor-premises range-composition)
    (cut-with-single-formula "injective_q{f}")
    (cut-with-single-formula "injective_q{f_$0 oo f}")
    (backchain 
     "with(f:[ind_1,ind_2],f_$0:[ind_2,ind_3], injective_q{f_$0 oo f})")
    (apply-macete-with-minor-premises injective-composition)
    simplify
    (apply-macete-with-minor-premises injective-iff-injective-on-domain)
    simplify
    )))

(def-theorem EQUALS-IMPLIES-EQUINUMEROUS
  "forall(a,b:sets[ind_1], a=b implies a equinumerous b)"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, p)")
    (apply-macete-with-minor-premises equinumerous-is-reflexive)
    )))


;;; Embeds lemmas

(def-theorem EMBEDS-IS-REFLEXIVE
  "forall(a:sets[ind_1], a embeds a)"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    (instantiate-existential ("id{a}"))
    (apply-macete-with-minor-premises dom-of-id)
    (apply-macete-with-minor-premises ran-of-id)
    (apply-macete-with-minor-premises id-is-injective-on-dom)
    )))

(def-theorem EMBEDS-IS-TRANSITIVE
  "forall(a:sets[ind_1],b:sets[ind_2],c:sets[ind_3],
     (a embeds b) and (b embeds c) implies (a embeds c))"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("f_$1 oo f_$0"))
    (apply-macete-with-minor-premises domain-composition)
    (apply-macete-with-minor-premises tr%subseteq-transitivity)
    auto-instantiate-existential
    (apply-macete-with-minor-premises composition-decreases-range)
    (apply-macete-with-minor-premises tr%injective-implies-injective-on)
    (apply-macete-with-minor-premises injective-composition)
    (apply-macete-with-minor-premises injective-iff-injective-on-domain)
    direct-inference
    (weaken (0 1 3 5 6 7))
    simplify
    (weaken (0 1 2 3 5 6 7))
    insistent-direct-inference-strategy
    simplify
    )))

(def-theorem EQUINUMEROUS-IMPLIES-EMBEDS
  "forall(a:sets[ind_1],b:sets[ind_2], 
     (a equinumerous b) implies (a embeds b))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (incorporate-antecedent "with(b:sets[ind_2],f:[ind_1,ind_2],ran{f}=b)")
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify
    )))

(def-theorem EMBEDS-IMPLIES-EQUINUMEROUS-TO-SUBSET
  "forall(a:sets[ind_1],b:sets[ind_2], 
     (a embeds b) 
      implies 
     forsome(c:sets[ind_2], a equinumerous c and c subseteq b))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("ran{f_$1}"))
    (instantiate-existential ("f_$1"))
    insistent-direct-inference
    )))

(def-theorem EQUINUMEROUS-EMBEDS-TRANSITIVITY
  "forall(a:sets[ind_1],b:sets[ind_2],c:sets[ind_3],
     (a equinumerous b) and (b embeds c) implies (a embeds c))"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof
   (
    direct-inference-strategy
    (apply-macete-with-minor-premises embeds-is-transitive)
    (instantiate-existential ("b"))
    (apply-macete-with-minor-premises equinumerous-implies-embeds)
    )))
  
(def-theorem EMBEDS-EQUINUMEROUS-TRANSITIVITY
  "forall(a:sets[ind_1],b:sets[ind_2],c:sets[ind_3],
     (a embeds b) and (b equinumerous c) implies (a embeds c))"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof
   (
    direct-inference-strategy
    (apply-macete-with-minor-premises embeds-is-transitive)
    (instantiate-existential ("b"))
    (apply-macete-with-minor-premises tr%equinumerous-implies-embeds)
    )))

(def-theorem EMBEDS-IN-EMPTY-INDIC
  "forall(a:sets[ind_1],
     (a embeds empty_indic{ind_2}) iff a=empty_indic{ind_1})"
  reverse
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (force-substitution "a" "dom{f_$1}" (0))
    extensionality
    direct-inference
    simplify
    (contrapose "with(a,b:sets[ind_2], a subseteq b)")
    (instantiate-existential ("f_$1(x_0)"))
    (apply-macete-with-minor-premises range-domain-membership)
    (apply-macete-with-minor-premises domain-membership-iff-defined)
    simplify-insistently
    simplify
    (force-substitution "a" "empty_indic{ind_1}" (0))
    (weaken (0))
    (instantiate-existential ("lambda(x:ind_1,?ind_2)"))
    extensionality
    direct-inference
    simplify
    insistent-direct-inference-strategy
    simplify-insistently
    insistent-direct-inference-strategy
    (antecedent-inference "with(p,q,r:prop, p and q and r)")
    (contrapose "with(x_$6:ind_1,x_$6 in empty_indic{ind_1})")
    simplify-insistently
    )))

(def-theorem EQUINUMEROUS-TO-EMPTY-INDIC
  "forall(a:sets[ind_1],
     (a equinumerous empty_indic{ind_2}) iff a=empty_indic{ind_1})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-inference-strategy
    (apply-macete-with-minor-premises rev%embeds-in-empty-indic)
    (apply-macete-with-minor-premises equinumerous-implies-embeds)
    (force-substitution "a" "empty_indic{ind_1}" (0))
    (instantiate-existential ("lambda(x:ind_1,?ind_2)"))
    insistent-direct-inference-strategy
    extensionality
    direct-inference
    simplify
    extensionality
    direct-inference
    simplify
    simplify
    (beta-reduce-antecedent "with(p,q,r:prop, p and q and r)")
    )))

(def-theorem SUBSET-EMBEDS-IN-SUPERSET
  "forall(a,b:sets[ind_1],
     (a subseteq b) implies (a embeds b))"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("id{a}"))
    (apply-macete-with-minor-premises dom-of-id)
    (apply-macete-with-minor-premises ran-of-id)
    (apply-macete-with-minor-premises id-is-injective-on-dom)
    )))




