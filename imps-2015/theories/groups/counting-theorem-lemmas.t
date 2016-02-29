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


(herald counting-theorem-lemmas)



;;; Lemmas for the Fundamental Counting Theorem

(def-theorem EQUAL-ACTIONS-IMPLIES-EQUAL-RIGHT-TRANS
  "forall(g,h:gg, alpha:uu, 
     act(alpha,g)=act(alpha,h) 
      implies
     right%trans(stabilizer(alpha),g)=right%trans(stabilizer(alpha),h))"
  lemma
  (theory group-actions)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally right%trans)
    extensionality
    direct-inference
    beta-reduce-repeatedly
    (raise-conditional (0))
    simplify
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally stabilizer)
    simplify
    (backchain "with(h,i_$0,x_0:gg,x_0=i_$0 mul h)")
    (weaken (0))
    (instantiate-existential ("i_$0 mul h mul inv(g)"))
    (apply-macete-with-minor-premises mul-associativity)
    (apply-macete-with-minor-premises act-associativity)
    (apply-macete-locally action-by-stabilizer-member (0) "act(alpha,i_$0)")
    (apply-macete-with-minor-premises action-macete)
    (instantiate-existential ("g"))
    (apply-macete-with-minor-premises simplify-actions)
    simplify
    (raise-conditional (0))
    simplify
    (weaken (2 3))
    (unfold-single-defined-constant-globally stabilizer)
    simplify
    (backchain "with(h,i_$0,x_0:gg,x_0=i_$0 mul h)")
    (weaken (0))
    (instantiate-existential ("i_$0 mul g mul inv(h)"))
    (apply-macete-with-minor-premises mul-associativity)
    (apply-macete-with-minor-premises act-associativity)
    (apply-macete-locally action-by-stabilizer-member (0) "act(alpha,i_$0)")
    (apply-macete-with-minor-premises action-macete)
    (instantiate-existential ("h"))
    (apply-macete-with-minor-premises simplify-actions)
    simplify
    (raise-conditional (0))
    simplify
    auto-instantiate-existential
    )))

(def-theorem EQUAL-RIGHT-TRANS-IMPLIES-EQUAL-ACTIONS
  "forall(g,h:gg, alpha:uu, 
     right%trans(stabilizer(alpha),g)=right%trans(stabilizer(alpha),h)
      implies
     act(alpha,g)=act(alpha,h))"
  lemma
  (theory group-actions)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally right%trans)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, p)")
    extensionality
    beta-reduce-repeatedly
    (raise-conditional (0))
    simplify
    (raise-conditional (0))
    simplify
    (contrapose "with(p:prop, p)")
    (instantiate-universal-antecedent "with(p:prop,p)" ("g"))
    (instantiate-universal-antecedent 
     "with(g:gg,alpha:uu, 
        forall(i_$2:gg, not(i_$2 in stabilizer(alpha)) or not(g=i_$2 mul g)))" 
     ("e"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises subgroups-contain-e)
    (apply-macete-with-minor-premises stabilizers-are-subgroups)
    (simplify-antecedent "with(g:gg,not(g=e mul g))")
    (force-substitution "g" "i_$1 mul h" (0))
    (apply-macete-with-minor-premises act-associativity)
    (apply-macete-locally action-by-stabilizer-member (0) "act(alpha,i_$1)")
    )))

(def-theorem EQUAL-ACTIONS-IFF-EQUAL-RIGHT-TRANS
  "forall(g,h:gg, alpha:uu, 
     act(alpha,g)=act(alpha,h) 
      iff
     right%trans(stabilizer(alpha),g)=right%trans(stabilizer(alpha),h))"
  reverse
  (theory group-actions)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises equal-actions-implies-equal-right-trans)
    (apply-macete-with-minor-premises equal-right-trans-implies-equal-actions)
    )))

(def-theorem DOMAIN-OF-FCT-MAPPING
  "dom{fct%mapping}=orbit(zeta)"
  lemma
  (theory counting-theorem-theory)
  (proof
   (

    unfold-defined-constants
    extensionality
    direct-inference
    simplify
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0)")
     (contrapose "with(p:prop,p);")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     (contrapose "with(p:prop,p);")
     (antecedent-inference-strategy (0))
     auto-instantiate-existential)
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (1 0)")
     (contrapose "with(p:prop,p);")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     (instantiate-existential ("right%trans(stabilizer(zeta),g)"))
     (instantiate-existential ("g"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 1 0 0)")
      (antecedent-inference-strategy (0 1))
      (backchain 
       "with(g_$0:gg,j_$0:sets[gg], j_$0=right%trans(stabilizer(zeta),g_$0));")
      (apply-macete-with-minor-premises 
       rev%equal-actions-iff-equal-right-trans)))

    )))

(def-theorem RANGE-OF-FCT-MAPPING
  "ran{fct%mapping}=stabilizer%right%cosets"
  lemma
  (theory counting-theorem-theory)
  (proof
   (

    unfold-defined-constants
    extensionality
    direct-inference
    simplify
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (0 0)")
     (contrapose "with(p:prop,p);")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     (contrapose "with(p:prop,p);")
     (antecedent-inference-strategy (0))
     (instantiate-existential ("g")))
    (block 
     (script-comment 
      "node added by `direct-and-antecedent-inference-strategy' at (1 0)")
     (contrapose "with(p:prop,p);")
     (instantiate-existential ("act(zeta,g)"))
     (backchain "with(p:prop,p);")
     (weaken (0))
     (apply-macete-with-minor-premises eliminate-iota-macete)
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("g"))
     (block 
      (script-comment 
       "node added by `direct-and-antecedent-inference-strategy' at (1 0 0 0 0 0 0)")
      (backchain 
       "with(g_$1:gg,b:sets[gg], b=right%trans(stabilizer(zeta),g_$0));")
      (apply-macete-with-minor-premises 
       rev%equal-actions-iff-equal-right-trans)))  

    )))

(def-theorem INJECTIVENESS-OF-FCT-MAPPING
  "injective_q{fct%mapping}"
  lemma
  (theory counting-theorem-theory)
  (proof
   (
    unfold-defined-constants
    insistent-direct-inference
    beta-reduce-repeatedly
    direct-inference
    (cut-with-single-formula 
     "#(iota(c:sets[gg], forsome(g:gg,
         c=right%trans(stabilizer(zeta),g) and x_1=act(zeta,g))))")
    (cut-with-single-formula 
     "#(iota(c:sets[gg], forsome(g:gg,
         c=right%trans(stabilizer(zeta),g) and x_2=act(zeta,g))))")
    (contrapose "with(x,y:sets[gg], x=y)")
    (eliminate-defined-iota-expression 0 u)
    (eliminate-defined-iota-expression 0 v)
    (weaken (5 6))
    (contrapose "with(x_2,x_1:uu,not(x_1=x_2));")
    (antecedent-inference-strategy (1 3))
    (backchain "with(g_$0:gg,x_1:uu,x_1=act(zeta,g_$0))")
    (backchain "with(g:gg,x_2:uu,x_2=act(zeta,g))")
    (apply-macete-with-minor-premises equal-actions-iff-equal-right-trans)
    )))

