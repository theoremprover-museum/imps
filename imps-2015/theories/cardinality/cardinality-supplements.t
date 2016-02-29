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

(herald cardinality-supplements)

(load-section basic-cardinality)

;;;Some lemmas

(def-script set-equality-script 0
  (
   (label-node top)
   (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
   direct-inference
   (jump-to-node top)
   (for-nodes
    (unsupported-descendents)
    (block
      insistent-direct-inference
      (apply-macete-with-minor-premises indicator-facts-macete)
      beta-reduce-repeatedly))
   ))


(def-script set-containment-script 0
  (

   insistent-direct-inference
   (apply-macete-with-minor-premises indicator-facts-macete)
   beta-reduce-repeatedly

   ))


(def-theorem equality-of-conditional-term
  "forall(x,y:ind_1,p:prop, if(p,x,?ind_1)=y iff (p and x=y))"
  (proof

   (
    (raise-conditional (0))
    ))
  (theory pure-generic-theory-1)
  (usages transportable-macete))


(def-theorem equality-of-conditional-term-backwards
  "forall(x,y:ind_1,p:prop, y=if(p,x,?ind_1) iff (p and x=y))"
  (proof

   (

    
    (force-substitution "y=if(p,x,?ind_1)" "if(p,x,?ind_1)=y" (0))
    (move-to-sibling 1)
    direct-and-antecedent-inference-strategy
    (raise-conditional (0))

    ))
  (theory pure-generic-theory-1)
  (usages transportable-macete))

(def-theorem indic-free-characterization-of-dom
  "forall(f:[ind_1,ind_2], a:sets[ind_1], 
          dom{f}=a iff forall(x:ind_1, x in a iff #(f(x))))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (

    
    (apply-macete-with-minor-premises rev%domain-membership-iff-defined)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify-insistently
    simplify-insistently

    )))

(def-theorem indic-free-characterization-of-ran
  "forall(f:[ind_1,ind_2], a:sets[ind_2], 
              ran{f}=a iff forall(y:ind_2, y in a iff forsome(x:ind_1, f(x)=y)))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (

    
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(f:[ind_1,ind_2],a:sets[ind_2],a subseteq ran{f});"
     ("y"))
    (incorporate-antecedent "with(y:ind_2,f:[ind_1,ind_2],y in ran{f});")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$1"))
    (instantiate-universal-antecedent
     "with(a:sets[ind_2],f:[ind_1,ind_2],ran{f} subseteq a);"
     ("y"))
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (instantiate-existential ("x"))
    set-containment-script
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(y:ind_2,p));")
    (instantiate-existential ("x"))
    set-containment-script
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(y:ind_2,p iff p));"
				      ("x_$1"))
    (instantiate-existential ("x"))
    )))



(def-theorem diff-conditionally-one-to-one
  "forall(a,b,c:sets[ind_1], 
             c subseteq a and c subseteq b implies 
               a diff c = b diff c iff a = b)"
  (theory pure-generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "a = (a diff c) union c")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%diff-union-equal-whole)
    (backchain "with(c,f,a:sets[ind_1],a=f union c);")
    (backchain "with(b,c,a:sets[ind_1],a diff c=b diff c);")
    (apply-macete-with-minor-premises tr%diff-union-equal-whole)
    simplify
    )))


(def-theorem diff-conditionally-onto
  "forall(a,b:sets[ind_1],
            a disj b implies (a union b) diff b = a)"
  (theory pure-generic-theory-1)
  (proof
   (


    direct-and-antecedent-inference-strategy
    set-equality-script
    direct-and-antecedent-inference-strategy
    direct-and-antecedent-inference-strategy
    (backchain "with(b,a:sets[ind_1],a disj b);")
    (weaken (0))     

    )))

(def-theorem f_card_difference
  "forall(s,t:sets[ind_1], x:ind_1, f_indic_q{s} and t subseteq s
                                     implies
                                  f_card{s diff t}=f_card{s}-f_card{t})"
  (theory generic-theory-1)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (force-substitution "s" "(s diff t) union t" (1))
    (move-to-sibling 1)
    insistent-direct-inference
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    simplify-insistently
    simplify-insistently
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises f-card-disjoint-union)
    (move-to-sibling 1)
    (apply-macete-with-minor-premises subset-of-finite-indic-is-finite)
    auto-instantiate-existential
    simplify-with-minor-premises
    (apply-macete-with-minor-premises subset-of-finite-indic-is-finite)
    (instantiate-existential ("s"))
    simplify-insistently
    simplify-insistently

    )))

(def-theorem subsets-of-finite-cardinality
  "forall(s:sets[ind_1], l:zz, l<=f_card{s} and 0<=l
                           implies 
                         forsome(t:sets[ind_1], t subseteq s and f_card{t}=l))"
  (theory generic-theory-1)
  (proof
   (



    (induction trivial-integer-inductor ("l"))
    (block 
     (script-comment "`induction' at (0 0 0 0 0 0 0 0)")
     simplify
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("empty_indic{ind_1}"))
     (block 
      (script-comment "`instantiate-existential' at (0 0)")
      simplify-insistently)
     (apply-macete-with-minor-premises empty-indic-has-f-card-zero-rewrite))
    (block 
     (script-comment "`induction' at (0 0 0 0 0 0 0 1 0 0 0 0 0)")
     (antecedent-inference "with(p:prop,p implies p);")
     (simplify-antecedent "with(p:prop,not(p));")
     (block 
      (script-comment "`antecedent-inference' at (1)")
      (antecedent-inference "with(p:prop,forsome(t:sets[ind_1],p));")
      (cut-with-single-formula "forsome(x:ind_1, x in s diff t)")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(f:sets[ind_1],nonempty_indic_q{f});")
       (instantiate-existential ("t union singleton{x}"))
       (block 
	(script-comment "`instantiate-existential' at (0 0)")
	simplify-insistently
	direct-and-antecedent-inference-strategy
	(backchain "with(p:prop,p and p);")
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
	 simplify
	 (incorporate-antecedent "with(x:ind_1,f:sets[ind_1],x in f);")
	 simplify-insistently))
       (block 
	(script-comment "`instantiate-existential' at (0 1)")
	(apply-macete-with-minor-premises f-card-disjoint-union)
	(block 
	 (script-comment "`apply-macete-with-minor-premises' at (0)")
	 (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
	 simplify)
	(block 
	 (script-comment "`apply-macete-with-minor-premises' at (1)")
	 (cut-with-single-formula "f_card{singleton{x}}=1")
	 (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite))
	(block 
	 (script-comment "`apply-macete-with-minor-premises' at (2)")
	 (incorporate-antecedent "with(x:ind_1,f:sets[ind_1],x in f);")
	 simplify-insistently
	 direct-and-antecedent-inference-strategy
	 simplify
	 (contrapose "with(p:prop,not(p));")
	 simplify)))
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (contrapose "with(s:sets[ind_1],t_$0:zz,1+t_$0<=f_card{s});")
       (cut-with-single-formula "s=t")
       simplify
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(incorporate-antecedent "with(f:sets[ind_1],empty_indic_q{f});")
	simplify-insistently
	direct-and-antecedent-inference-strategy
	(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	direct-and-antecedent-inference-strategy
	simplify))))
    )))

(def-theorem cardinality-reduction
  "forall(s:sets[ind_1], n:zz, 1<=n implies (f_card{s}=n iff 
    forsome(x:ind_1, x in s and f_card{s diff singleton{x}}=n-1)))"
  (theory generic-theory-1)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
     (apply-macete-with-minor-premises f_card_difference)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
      simplify
      (apply-macete-with-minor-premises rev%positive-f-card-iff-nonempty)
      simplify)
     simplify-insistently)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0)")
     (cut-with-single-formula "f_indic_q{s}")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(r:rr,n:nn,n=r);")
      (apply-macete-with-minor-premises f_card_difference)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (0)")
       (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
       simplify)
      simplify-insistently)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises iota-free-definition-of-f-indic-q)
      (force-substitution "s"
			  "(s diff singleton{x}) union singleton{x}"
			  (0))
      (block 
       (script-comment "`force-substitution' at (0)")
       (apply-macete-with-minor-premises f-card-disjoint-union)
       (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	(apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
	simplify)
       (block 
	(script-comment "`apply-macete-with-minor-premises' at (1)")
	(apply-macete-with-minor-premises iota-free-definition-of-f-indic-q)
	(apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
	(instantiate-existential ("1")))
       simplify-insistently)
      (block 
       (script-comment "`force-substitution' at (1)")
       (apply-macete-with-minor-premises tr%diff-union-equal-whole)
       simplify-insistently)))

    )))

(def-compound-macete compute-card
  (repeat cardinality-reduction simplify empty-indic-has-f-card-zero))
  
(def-theorem cardinality-3
  "forall(s:sets[ind_1],f_card{s}=3 iff 
    forsome(x,y,z:ind_1, not(x=y) and not(x=z) and not(y=z) and 
                         s = singleton{x} union singleton{y} union singleton{z}))"
  (theory generic-theory-1)
  (proof
   (


    (apply-macete-with-minor-premises compute-card)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0 0 0)")
     (instantiate-existential ("x" "x_$17" "x_$16"))
     simplify
     (block 
      (script-comment "`instantiate-existential' at (0 3)")
      (incorporate-antecedent "with(f:sets[ind_1],f=f);")
      (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(x_$2:ind_1,p));"
					("x_$2"))
      simplify
      simplify
      simplify))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
     (incorporate-antecedent "with(f,s:sets[ind_1],s=f);")
     (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("x"))
     simplify
     (block 
      (script-comment "`instantiate-existential' at (0 1)")
      (instantiate-existential ("y"))
      simplify
      simplify
      (block 
       (script-comment "`instantiate-existential' at (0 2)")
       (instantiate-existential ("z"))
       simplify
       simplify
       simplify
       simplify)))
    )))