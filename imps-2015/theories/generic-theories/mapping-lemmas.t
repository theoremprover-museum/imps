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


(herald MAPPING-LEMMAS)

(include-files 
 (files (imps theories/generic-theories/indicator-lemmas)
	(imps theories/generic-theories/mappings)))


;;; Preliminary mapping lemmas

(def-theorem UNARY-ETA-REDUCTION
  "forall(f:[ind_1,ind_2], lambda(x:ind_1,f(x))=f);"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    extensionality
    simplify
    )))


;;; Domain and range lemmas

(def-theorem DOMAIN-MEMBERSHIP-IFF-DEFINED
  "forall(x:ind_1,f:[ind_1,ind_2], x in dom(f) iff #(f(x)))"
  reverse
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem RANGE-DOMAIN-MEMBERSHIP
  "forall(x:ind_1,f:[ind_1,ind_2], f(x) in ran{f} iff x in dom(f))"
  reverse
  (theory pure-generic-theory-2)
  (usages transportable-macete transportable-rewrite)
  (proof
   (
    simplify-insistently
    direct-and-antecedent-inference-strategy
    simplify-insistently
    (instantiate-existential ("x"))
    )))

(def-theorem MEMBERSHIP-IN-A-DOMAIN
  "forall(x:ind_1,a:sets[ind_1],f:[ind_1,ind_2], 
     dom{f}=a and #(f(x)) implies x in a)"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (force-substitution "a" "dom{f}" (0))
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    )))

(def-theorem MEMBERSHIP-IN-A-RANGE
  "forall(x:ind_1,y:ind_2,b:sets[ind_2],f:[ind_1,ind_2],
     ran{f}=b and y=f(x) implies y in b)"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (force-substitution "b" "ran{f}" (0))
    (force-substitution "y" "f(x)" (0))
    (apply-macete-with-minor-premises tr%range-domain-membership)
    simplify-insistently
    )))

(def-theorem DOM-OF-AN-INDICATOR
  "forall(a:sets[ind_1], dom{a}=a)"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    extensionality
    extensionality
    direct-inference
    simplify-insistently
    (case-split-on-conditionals (0))
    )))


;;; Composition lemmas

(def-theorem ASSOCIATIVITY-OF-COMPOSITION
  "forall(f:[ind_3,ind_4],g:[ind_2,ind_3],h:[ind_1,ind_2], 
     (f oo g) oo h = f oo (g oo h))"
  reverse
  (theory pure-generic-theory-4)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    extensionality
    direct-inference
    simplify
    )))

(def-theorem COMPOSITION-DECREASES-DOMAIN
  "forall(f:[ind_1,ind_2], g:[ind_2,ind_3], 
     dom{g oo f} subseteq dom{f})"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem COMPOSITION-DECREASES-RANGE
  "forall(f:[ind_1,ind_2], g:[ind_2,ind_3], 
     ran{g oo f} subseteq ran{g})"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof
   (
    simplify-insistently
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    )))

(def-theorem DOMAIN-COMPOSITION 		
  "forall(f:[ind_1,ind_2], g:[ind_2,ind_3], 
     ran{f} subseteq dom{g} implies dom{g oo f} = dom{f})"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof
   (

    simplify-insistently
    direct-and-antecedent-inference-strategy
    extensionality
    direct-and-antecedent-inference-strategy
    simplify
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,not(p));")
    (instantiate-universal-antecedent "with(p:prop,forall(x_$0:ind_2,p));"
				      ("f(x_0)"))
    (instantiate-universal-antecedent "with(p:prop,forall(x_$1:ind_1,p));" ("x_0")))))


;;;    direct-and-antecedent-inference-strategy
;;;    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
;;;    (apply-macete-with-minor-premises tr%composition-decreases-domain)
;;;    insistent-direct-inference-strategy
;;;    (instantiate-universal-antecedent "with(a,b:sets[ind_2], a subseteq b)" ("f(x_$1)"))
;;;    (contrapose "with(p:prop, not(p))")
;;;    (apply-macete-with-minor-premises tr%range-domain-membership)
;;;    simplify-insistently
;;;    (incorporate-antecedent "with(x_$1:ind_1,f:[ind_1,ind_2],x_$1 in dom{f});")
;;;    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
;;;    simplify
;;;    )))

(def-theorem RANGE-COMPOSITION 		
  "forall(f:[ind_1,ind_2], g:[ind_2,ind_3], 
     dom{g} subseteq ran{f} implies ran{g oo f} = ran{g})"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof
   (
   
    simplify-insistently
    direct-and-antecedent-inference-strategy
    extensionality
    direct-and-antecedent-inference-strategy
    simplify
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      auto-instantiate-existential)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0)")
      (contrapose "with(p:prop,not(p));")
      (instantiate-universal-antecedent "with(p:prop,forall(x_$0:ind_2,p));"
					("x"))
      (instantiate-existential ("x_$1"))
      simplify))))



;;; direct-and-antecedent-inference-strategy
;;;    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
;;;    (apply-macete-with-minor-premises tr%composition-decreases-range)
;;;    direct-and-antecedent-inference-strategy
;;;    insistent-direct-inference
;;;    simplify-insistently
;;;    direct-and-antecedent-inference-strategy
;;;    (instantiate-universal-antecedent 
;;;     "with(a,b:sets[ind_2], a subseteq b)" ("x"))
;;;    (contrapose "with(p:prop, not(p))")
;;;    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
;;;    (incorporate-antecedent "with(x:ind_2,f:[ind_1,ind_2],x in ran{f});")
;;;    simplify-insistently
;;;    direct-and-antecedent-inference-strategy
;;;    (instantiate-existential ("x_$1"))
;;;    simplify
;;;    )))

(def-theorem INJECTIVE-COMPOSITION
  "forall(f:[ind_1,ind_2], g:[ind_2,ind_3], 
     injective_q{f} and injective_on_q{g,ran{f}} implies injective_q{g oo f})"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    direct-inference
    (backchain "with(f:[ind_1,ind_2],injective_q{f})")
    (backchain 
     "with(g:[ind_2,ind_3],f:[ind_1,ind_2], injective_on_q{g,ran{f}})")
    (incorporate-antecedent "with(x,y:ind_3, x=y)")
    (weaken (0 1))
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$0"))
    (instantiate-existential ("x_$1"))
    simplify
    )))


;;; Image and inverse image lemmas

(def-theorem IMAGE-OF-DOMAIN-IS-RANGE
  "forall(f:[ind_1,ind_2], image{f,dom{f}} = ran{f})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    insistent-direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$1"))
    insistent-direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x"))
    )))

(def-theorem IMAGE-SUBSET-OF-RANGE-CHARACTERIZATION
  "forall(s:sets[ind_1],f:[ind_1,ind_2], 
     s subseteq dom{f} implies image{f,s} subseteq ran{f})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    )))

(def-theorem IMAGE-IS-MONOTONE-WRT-SUBSETEQ
  "forall(f:[ind_1,ind_2],a,b:sets[ind_1],
     (a subseteq b) implies (image(f,a) subseteq image(f,b)))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (backchain "with(b,a:sets[ind_1],a subseteq b)")
    )))

(def-theorem DIRECT-IMAGE-DISJOINTNESS-CONVERSION
  "forall(f:[ind_1,ind_2],a:sets[ind_1],b:sets[ind_2],
     empty_indic_q(b inters image(f,a)) iff empty_indic_q(inv_image(f,b) inters a))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, forall(x_$0:ind_2,p))")
    auto-instantiate-existential
    (contrapose "with(p:prop, forall(x_$0:ind_1,p))")
    auto-instantiate-existential
    simplify
    )))

(def-theorem DIRECT-IMAGE-SUBSET-CONVERSION 	
  "forall(f:[ind_1,ind_2],a:sets[ind_1],b:sets[ind_2],
     total_q(f,[ind_1,ind_2]) 
      implies 
     (image(f,a) subseteq b iff a subseteq inv_image(f,b)))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, forall(x_$0:ind_2,p))")
    auto-instantiate-existential
    (auto-instantiate-universal-antecedent "with(p:prop, forall(x_$0:ind_1,p))")
    simplify
    )))

(def-theorem INVERSE-IMAGE-UNION-PRESERVATION
  "forall(f:[ind_1,ind_2],a,b:sets[ind_2], 
     inv_image(f,a union b) = inv_image(f,a) union inv_image(f,b))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (contrapose "with(y:ind_2,a:sets[ind_2], y in a)")
    (case-split ("#(f(x_$2))"))
    (apply-macete-with-minor-premises tr%membership-in-union)
    simplify
    simplify
    (apply-macete-with-minor-premises tr%membership-in-union)
    simplify
    (apply-macete-with-minor-premises tr%membership-in-union)
    simplify
    )))

(def-theorem INVERSE-IMAGE-INTERS-PRESERVATION
  "forall(f:[ind_1,ind_2],a,b:sets[ind_2], 
     inv_image(f,a inters b) = inv_image(f,a) inters inv_image(f,b))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    (apply-macete-with-minor-premises tr%membership-in-intersection)
    )))

(def-theorem MEANING-OF-INVERSE-IMAGE-MEMBERSHIP 
  "forall(f:[ind_1,ind_2],x:ind_1,o:sets[ind_2],
     x in inv_image(f,o) iff f(x) in o)"
 (theory pure-generic-theory-2)
 (usages transportable-macete)
 (proof (simplify-insistently)))

(def-compound-macete DIRECT-IMAGE-TO-INVERSE-IMAGE-CONVERSION-MACETE
  (repeat
   tr%direct-image-disjointness-conversion
   tr%direct-image-subset-conversion
   tr%inverse-image-union-preservation
   tr%inverse-image-inters-preservation))

(def-compound-macete INDICATOR-FACTS-MACETE
  (repeat
   tr%meaning-of-indic-from-pred-element
   tr%meaning-of-inverse-image-membership))


;;; Id lemmas

(def-theorem DOM-OF-ID
  "forall(a:sets[ind_1], dom{id{a}} = a)"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    extensionality
    direct-inference
    simplify-insistently
    (case-split-on-conditionals (0))
    )))

(def-theorem RAN-OF-ID
  "forall(a:sets[ind_1], ran{id{a}} = a)"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    extensionality
    direct-inference
    simplify-insistently
    (case-split-on-conditionals (0))
    (antecedent-inference "with(p:prop, forsome(x_$1:ind_1,p))")
    (incorporate-antecedent "with(x,y:ind_1, x=y)")
    (case-split-on-conditionals (0))
    (contrapose "with(p:prop, not(p))")
    (instantiate-existential ("x_0"))
    simplify
    )))

(def-theorem ID-IS-INJECTIVE-ON-DOM
  "forall(a:sets[ind_1], injective_on_q{id{a},a})"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    insistent-direct-inference-strategy
    (antecedent-inference "with(p,q,r:prop, p and q and r)")
    (incorporate-antecedent "with(x,y:ind_1, x = y)")
    simplify-insistently
    )))

(def-theorem COMPOSITION-WITH-ID-RIGHT
  "forall(f:[ind_1,ind_2], a:sets[ind_1], f oo id{a} = restrict{f,a})"
  (theory pure-generic-theory-2)
  (usages transportable-macete transportable-rewrite)
  (proof
   (
    direct-inference
    extensionality
    direct-inference
    simplify
    (case-split-on-conditionals (0)))))

(def-theorem COMPOSITION-WITH-ID-LEFT
  "forall(f:[ind_1,ind_2],a:sets[ind_2], 
     id{a} oo f = restrict{f,inv_image{f,a}})"
  (theory pure-generic-theory-2)
  (usages transportable-macete transportable-rewrite)
  (proof
   (
    direct-inference
    extensionality
    direct-inference
    simplify
    (case-split-on-conditionals (0))
    )))

(def-theorem COMPOSITION-WITH-TOTAL-ID-LEFT
  "forall(f:[ind_1,ind_2],a:sets[ind_2], 
     total_q{a,sets[ind_2]} implies id{a} oo f = f)"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    extensionality
    direct-inference
    (case-split ("#(f(x_0))"))
    simplify
    simplify
    )))

(def-theorem COMPOSITION-WITH-TOTAL-ID-RIGHT
  "forall(f:[ind_1,ind_2], a:sets[ind_1], 
     total_q{a,sets[ind_1]} implies f oo id{a} = f)"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    extensionality
    direct-inference
    (case-split ("#(f(x_0))"))
    simplify
    simplify
    )))


;;; Surjective, injective, and bijective lemmas

(def-theorem SURJECTIVE-ON-LEMMA
  "forall(a:sets[ind_1],b:sets[ind_2],f:[ind_1,ind_2],x:ind_1,
     surjective_on_q(f,a,b) and (x in a) implies (f(x) in b))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (force-substitution "b" "ran{f}" (0))
    (apply-macete-with-minor-premises tr%range-domain-membership)
    simplify
    )))

(def-theorem DOMAIN-OF-A-BIJECTIVE-COMPOSITION
  "forall(a:sets[ind_1],b:sets[ind_2],c:sets[ind_3],f:[ind_1,ind_2],g:[ind_2,ind_3], 
     bijective_on_q(f,a,b) and bijective_on_q(g,b,c) implies dom(g oo f) = a)"
 (theory pure-generic-theory-3)
 (usages transportable-macete)
 (proof
  (
   direct-and-antecedent-inference-strategy
   (apply-macete-with-minor-premises tr%domain-composition)
   )))

(def-theorem RANGE-OF-A-BIJECTIVE-COMPOSITION
  "forall(a:sets[ind_1],b:sets[ind_2],c:sets[ind_3],f:[ind_1,ind_2],g:[ind_2,ind_3], 
     bijective_on_q(f,a,b) and bijective_on_q(g,b,c) implies ran(g oo f) = c)"
 (theory pure-generic-theory-3)
 (usages transportable-macete)
 (proof
  (
   direct-and-antecedent-inference-strategy
   (apply-macete-with-minor-premises tr%range-composition)
   )))

(def-theorem INJECTIVE-AND-SURJECTIVE-IS-TOTAL
  "forall(f:[ind_1,ind_2], 
     injective_q{f} and surjective_q{f} implies total_q{f,[ind_1,ind_2]})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem INJECTIVE-IMPLIES-INJECTIVE-ON
  "forall(f:[ind_1,ind_2],a:sets[ind_1], 
     injective_q{f} implies injective_on_q{f,a})" 
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    insistent-direct-inference-strategy
    simplify
    )))

(def-theorem INJECTIVE-IFF-INJECTIVE-ON-DOMAIN
  "forall(f:[ind_1,ind_2],a:sets[ind_1], 
     injective_q{f} iff injective_on_q{f,dom{f}})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises injective-implies-injective-on)
    insistent-direct-inference
    direct-inference
    (backchain "with(f:[ind_1,ind_2],injective_on_q{f,dom{f}});")
    simplify
    )))

(def-theorem RANGE-OF-BIJECTION-ON-SINGLETON
  "forall(f:[ind_1,ind_2],a:sets[ind_1],b:sets[ind_2],
     bijective_on_q{f,a,b} and forsome(x:ind_1,a=singleton{x}) 
      implies
     forsome(y:ind_2,b=singleton{y}))" 
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(y:ind_1, y in a iff y=x)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (cut-with-single-formula "#(f(x))")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (apply-macete-with-minor-premises tr%singletons-have-a-unique-member)
      (instantiate-existential ("f(x)"))
      (backchain-backwards "with(b:sets[ind_2],f:[ind_1,ind_2],ran{f}=b);")
      beta-reduce-insistently
      simplify
      (apply-macete-with-minor-premises eliminate-iota-macete)
      direct-inference
      (instantiate-existential ("x"))
      (block 
       (script-comment "`direct-inference' at (1)")
       direct-and-antecedent-inference-strategy
       (backchain "with(i,b_$0:ind_2,b_$0=i);")
       (instantiate-universal-antecedent "with(p:prop,forall(y:ind_1,p));"
					 ("x_$1"))
       (contrapose "with(x_$1:ind_1,a:sets[ind_1],not(x_$1 in a));")
       (backchain-backwards "with(a:sets[ind_1],f:[ind_1,ind_2],dom{f}=a);")
       (apply-macete-with-minor-premises domain-membership-iff-defined)))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises rev%domain-membership-iff-defined)
      (force-substitution "dom{f}" "singleton{x}" (0))
      (weaken (0 1 2 3 4))
      simplify-insistently))
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (backchain "with(x:ind_1,a:sets[ind_1],a=singleton{x});")
     (weaken (0 1 2 3))
     simplify-insistently)
    )))

(def-theorem RESTRICTED-TO-RANGE-COMPOSITION-LEMMA
  "forall(phi:[ind_1,ind_2],f:[ind_2,ind_3],
     f oo phi==(restrict{f,ran{phi}}) oo phi)"
  (theory generic-theory-3)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    simplify-insistently
    extensionality
    direct-and-antecedent-inference-strategy
    (case-split ("#(phi(x_0))"))
    simplify
    (cut-with-single-formula "forsome(x_$1:ind_1,phi(x_0)=phi(x_$1))")
    simplify
    (instantiate-existential ("x_0"))
    simplify

    )))

(def-theorem DOMAIN-OF-A-RESTRICTION
  "forall(phi:[ind_1,ind_2], s:sets[ind_1], s subseteq dom{phi} implies
                             s=dom{restrict{phi,s}})"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    simplify
    (apply-macete-with-minor-premises rev%domain-membership-iff-defined)
    (backchain "with(phi:[ind_1,ind_2],s:sets[ind_1],s subseteq dom{phi});")
    insistent-direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy

    )))

(def-theorem IMAGE-OF-A-RESTRICTION
  "forall(phi:[ind_1,ind_2], s:sets[ind_1],image{restrict{phi,s},s}=image{phi,s})"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$1"))
    (contrapose "with(phi:[ind_1,ind_2],x_$1:ind_1,s:sets[ind_1],x_$2:ind_2,
  x_$2=if(x_$1 in s, phi(x_$1), ?ind_2));")
    simplify
    insistent-direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    simplify

    )))


(def-theorem INJECTIVITY-OF-A-RESTRICTION
  "forall(phi:[ind_1,ind_2], s:sets[ind_1],injective_q{phi} 
              implies injective_q{restrict{phi,s}})"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    
    insistent-direct-inference-strategy
    (backchain "with(phi:[ind_1,ind_2],injective_q{phi});")
    (case-split ("x_1 in s " "x_2 in s"))
    (contrapose "with(x_2,x_1:ind_1,phi:[ind_1,ind_2],s:sets[ind_1],
  restrict{phi,s}(x_1)=restrict{phi,s}(x_2));")
    simplify
    (contrapose "with(x_2,x_1:ind_1,phi:[ind_1,ind_2],s:sets[ind_1],
  restrict{phi,s}(x_1)=restrict{phi,s}(x_2));")
    simplify
    (contrapose "with(x_2,x_1:ind_1,phi:[ind_1,ind_2],s:sets[ind_1],
  restrict{phi,s}(x_1)=restrict{phi,s}(x_2));")
    simplify
    (contrapose "with(x_2,x_1:ind_1,phi:[ind_1,ind_2],s:sets[ind_1],
  restrict{phi,s}(x_1)=restrict{phi,s}(x_2));")
    simplify

    )))
