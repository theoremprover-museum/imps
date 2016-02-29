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


(herald INVERSE-LEMMAS)

(include-files 
 (files (imps theories/generic-theories/mappings)))


;;; Inverse lemmas

(def-theorem INVERSE-COMPOSES-TO-ID
  "forall(f:[ind_1,ind_2], inverse{f} oo f =id{ran{inverse{f}}})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    extensionality
    direct-inference
    (case-split ("#(f(x_0))"))
    (block 
     (script-comment "node added by `case-split' at (1)")
     simplify
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0)")
      (backchain "with(i,x_0:ind_1,x_0=i);")
      (eliminate-defined-iota-expression 1 u)
      simplify)
     (block 
      (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1)")
      (contrapose "with(p:prop,not(p));")
      (instantiate-existential ("f(x_0)"))
      (eliminate-defined-iota-expression 0 u)
      simplify))
    (block 
     (script-comment "node added by `case-split' at (2)")
     simplify
     direct-inference
     (contrapose "with(p:prop,p);")
     (backchain "with(p:prop,p);")
     (eliminate-defined-iota-expression 0 u))
    )))

(def-theorem INVERSE-IS-INJECTIVE
  "forall(f:[ind_1,ind_2], injective_q{inverse{f}})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    insistent-direct-inference
    simplify
    direct-inference
    (cut-with-single-formula "#(iota(y:ind_1,f(y)=x_$0))")
    (cut-with-single-formula "#(iota(y:ind_1,f(y)=x_$1))")
    (incorporate-antecedent "with(x,y:ind_1, x=y)")
    (eliminate-defined-iota-expression 0 u)
    (eliminate-defined-iota-expression 0 v)
    direct-inference
    (force-substitution "x_$0" "f(u)" (0))
    simplify
    )))

(def-theorem INVERSE-DEFINED-WITHIN-RANGE
  "forall(f:[ind_1,ind_2], 
     injective_q(f) implies ran(f) subseteq dom{inverse{f}})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (instantiate-existential ("x"))
    (instantiate-universal-antecedent 
     "with(f:[ind_1,ind_2],injective_q{f});" 
     ("x" "j"))
    )))

(def-theorem INVERSE-DEFINED-ONLY-IN-RANGE
  "forall(f:[ind_1,ind_2], dom{inverse{f}} subseteq ran(f))"
  lemma
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises eliminate-forsome-macete)
    (force-substitution "x_$0=f(i)" "f(i)=x_$0" (0))
    direct-and-antecedent-inference-strategy
    )))

(def-theorem DOM-OF-INVERSE
  "forall(f:[ind_1,ind_2], 
     injective_q(f) implies dom{inverse{f}} = ran(f))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (apply-macete-with-minor-premises inverse-defined-only-in-range)
    (apply-macete-with-minor-premises inverse-defined-within-range)
    )))

(def-theorem INVERSE-RANGE-WITHIN-DOMAIN
  "forall(f:[ind_1,ind_2], 
     injective_q(f) implies dom(f) subseteq ran{inverse{f}})"
  lemma
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    simplify-insistently
    direct-inference
    (instantiate-existential ("f(x_$0)"))
    (apply-macete-with-minor-premises eliminate-iota-macete)
    simplify
    )))

(def-theorem INVERSE-RANGE-ONLY-IN-DOMAIN
  "forall(f:[ind_1,ind_2], ran{inverse{f}} subseteq dom(f))"
  lemma
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    insistent-direct-inference
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (force-substitution "x_$0" "iota(y:ind_1,f(y)=x_$1)" (0))
    (eliminate-defined-iota-expression 0 u)
    )))

(def-theorem RAN-OF-INVERSE
  "forall(f:[ind_1,ind_2], 
       injective_q(f) implies ran{inverse{f}} = dom(f))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (apply-macete-with-minor-premises inverse-range-within-domain)
    (apply-macete-with-minor-premises inverse-range-only-in-domain)
    )))

(def-theorem INVERSE-IS-A-LEFT-INVERSE
  "forall(f:[ind_1,ind_2],
     injective_q(f) implies inverse{f} oo f = id{dom{f}})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    extensionality
    direct-inference
    simplify
    (case-split-on-conditionals (0))
    (apply-macete-with-minor-premises eliminate-iota-macete)
    simplify
    )))

(def-theorem INVERSE-IS-A-LEFT-INVERSE-APPLIED 
  "forall(f:[ind_1,ind_2], x:ind_1,
     injective_q(f) and #(f(x)) implies inverse{f}(f(x)) = x)"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (eliminate-iota 0)
    (instantiate-existential ("x"))
    (backchain "with(f:[ind_1,ind_2],injective_q{f});"))))

(def-theorem INVERSE-IS-A-RIGHT-INVERSE
  "forall(f:[ind_1,ind_2], 
     injective_q(f) implies f oo inverse{f} = id{ran{f}})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof				; 46 nodes
   (
    direct-and-antecedent-inference-strategy
    extensionality
    direct-inference
    simplify
    direct-and-antecedent-inference-strategy
    (block
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 0)")
     (eliminate-iota 0)
     (instantiate-existential ("x"))
     simplify)
    (block
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (1)")
     (contrapose "with(p:prop,not(p));")
     (instantiate-existential ("iota(y:ind_1,f(y)=x_0)"))
     (eliminate-defined-iota-expression 0 u))
    )))

(def-theorem INVERSE-IS-A-RIGHT-INVERSE-APPLIED  
  "forall(f:[ind_1,ind_2], x:ind_2,
     injective_q(f) and x in ran{f} implies f(inverse{f}(x)) = x)"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem inverse-is-a-right-inverse ("f"))
    (contrapose "with(f:[ind_2,ind_2],f=f);")
    extensionality
    (apply-macete-with-minor-premises tr%restricted-to-range-composition-lemma)
    beta-reduce-insistently
    (instantiate-existential ("x_$1"))
    (contrapose "with(p:prop,not(p));")
    (case-split ("forsome(x:ind_1,x_$1=f(x))"))
    simplify
    (contrapose "with(x_$1:ind_2,f:sets[ind_2],x_$1 in f);")
    (apply-macete-with-minor-premises indicator-facts-macete)
    simplify)))

(def-theorem IMAGE-UNDER-INVERSE-OF-INJECTIVE-MAPPING
  "forall(f:[ind_1,ind_2],a:sets[ind_1],b:sets[ind_2],
     injective_q{f} and image{f,a}=b and a subseteq dom{f}
      implies 
     image{inverse{f},b}=a)"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof				
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    (block 
     (script-comment "node added by `direct-inference' at (0)")
     insistent-direct-inference
     simplify
     direct-and-antecedent-inference-strategy
     (backchain "with(i,x_$2:ind_1,x_$2=i);")
     (eliminate-defined-iota-expression 0 u)
     (contrapose "with(b,f:sets[ind_2],f=b);")
     extensionality
     (instantiate-existential ("x_$1"))
     simplify
     direct-and-antecedent-inference-strategy
     (contrapose 
      "with(u:ind_1,x_$1,i:ind_2, forall(u_1:ind_1,i=x_$1 implies u=u_1));")
     (instantiate-existential ("x"))
     (contrapose "with(p:prop,not(p));")
     simplify)
    (block 
     (script-comment "node added by `direct-inference' at (1)")
     insistent-direct-inference
     simplify
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("f(x_$0)"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 0)")
      (contrapose "with(b,f:sets[ind_2],f=b);")
      extensionality
      (instantiate-existential ("x_$0"))
      (instantiate-existential ("f(x_$0)"))
      simplify
      (apply-macete-with-minor-premises indicator-facts-macete)
      beta-reduce-with-minor-premises
      (instantiate-existential ("x_$0"))
      simplify
      (instantiate-universal-antecedent
       "with(f:[ind_1,ind_2],a:sets[ind_1],a subseteq dom{f});"
       ("x_$0"))
      (incorporate-antecedent 
       "with(x_$0:ind_1,f:[ind_1,ind_2],x_$0 in dom{f});")
      (apply-macete-with-minor-premises domain-membership-iff-defined))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 1)")
      (eliminate-iota 0)
      (instantiate-existential ("x_$0"))
      (backchain "with(f:[ind_1,ind_2],injective_q{f});"))
     (instantiate-universal-antecedent
      "with(f:[ind_1,ind_2],a:sets[ind_1],a subseteq dom{f});"
      ("x_$0")))
    )))

(def-theorem INVERSE-INVERSE-IS-RESTRICTION
  "forall(f:[ind_1,ind_2], 
     injective_q{f} implies inverse{inverse{f}}=restrict{f,dom{f}})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    extensionality
    direct-inference
    simplify
    (case-split-on-conditionals (0))
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    simplify
    (force-substitution "x_0" "iota(y:ind_1,f(y)=b)" (0))
    (eliminate-defined-iota-expression 0 u)
    (apply-macete-with-minor-premises eliminate-iota-macete)
    simplify
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, not(p))")
    (force-substitution "x_0" "iota(y:ind_1,f(y)=i)" (0))
    (eliminate-defined-iota-expression 0 u)
    )))

(def-theorem SURJECTIVE-INVERSE
  "forall(a:sets[ind_1],f:[ind_1,ind_2],
      injective_on_q(f,a) and dom(f)=a 
        implies 
      surjective_on_q{inverse{f},ran{f},a})"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises dom-of-inverse)
    insistent-direct-inference-strategy
    (backchain "with(f:[ind_1,ind_2],a:sets[ind_1],injective_on_q{f,a});")
    direct-inference
    (apply-macete-with-minor-premises tr%membership-in-a-domain)
    auto-instantiate-existential
    (apply-macete-with-minor-premises tr%membership-in-a-domain)
    auto-instantiate-existential
    (apply-macete-with-minor-premises ran-of-inverse)
    )))

(def-theorem INVERSE-COMPOSITION-IMAGE-LEMMA
  "forall(phi:[ind_1,ind_3],psi:[ind_2,ind_3],
    injective_q{psi} and ran{psi}=ran{phi}
     implies 
    image{(inverse{psi}) oo phi,dom{phi}}=dom{psi})"
  (theory pure-generic-theory-3)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "psi(x_$3) in ran{psi}")
    (incorporate-antecedent 
     "with(x_$3:ind_2,psi:[ind_2,ind_3],psi(x_$3) in ran{psi});")
    (backchain 
     "with(phi:[ind_1,ind_3],psi:[ind_2,ind_3],ran{psi}=ran{phi});")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x"))
    (cut-with-single-formula "psi(b)=psi(x_$3)")
    (backchain "with(psi:[ind_2,ind_3],injective_q{psi});")
    (apply-macete-with-minor-premises tr%range-domain-membership)
    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    )))

(def-theorem inverse-defined-only-in-range-existential
  "forall(f:[ind_1,ind_2],y:ind_2,
     #(inverse{f}(y)) implies forsome(x:ind_1,y=f(x)))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("(inverse{f}(y_$0))"))
    simplify-insistently
    (eliminate-defined-iota-expression 0 z))))
