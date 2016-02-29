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

(herald combinatorics)

(include-files (files (imps theories/cardinality/cardinality-supplements)))

(comment
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


;;;(def-language pure-generic-theory-1-with-a-subsort
;;;  (embedded-language pure-generic-theory-1)
;;;  (sorts (a ind_1)))
;;;
;;;(def-theory pure-generic-theory-1-with-a-subsort
;;;  (language pure-generic-theory-1-with-a-subsort)
;;;  (component-theories pure-generic-theory-1))


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

 )

(def-constant power
  "lambda(s:sets[ind_1], indic{a:sets[ind_1], a subseteq s})"
  (theory generic-theory-1))

(comment 
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

 )


(def-constant filter
  "lambda(x:ind_1, indic{a:sets[ind_1], x in a})"
  (theory generic-theory-1))

(def-theorem power-decomposition
  "forall(s:sets[ind_1], x:ind_1, n:nn, 
            x in s 
            implies
         power(s)=power(s diff singleton{x}) union 
                  power(s) inters filter(x))"
  (theory generic-theory-1)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    set-equality-script
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,not(p));")
    simplify-insistently
    (contrapose "with(p:prop,not(p));")
    simplify
    direct-and-antecedent-inference-strategy
    set-containment-script
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f,x:sets[ind_1],x subseteq f);")
    simplify-insistently
    )))

(def-theorem power-disjointness
  "forall(s:sets[ind_1], x:ind_1, n:nn, 
         power(s diff singleton{x}) disj power(s) inters filter(x))"
  (theory generic-theory-1)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    simplify-insistently
    
    )))

(def-theorem power-reduction
  "forall(s:sets[ind_1], x:ind_1, x in s 
             implies
            power(s) inters filter(x) equinumerous power(s diff singleton{x}))"
  (theory generic-theory-1)
  (proof
   (

    

    direct-and-antecedent-inference-strategy
    (instantiate-existential ("lambda(t:sets[ind_1],
     if(t in power(s) inters filter(x), t diff singleton{x}, ?sets[ind_1]))"))
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises tr%indic-free-characterization-of-dom)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify
    (weaken (0))
    unfold-defined-constants
    (apply-macete-with-minor-premises tr%indic-free-characterization-of-ran)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%equality-of-conditional-term)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("y_$0 union singleton{x}"))
    set-containment-script
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f,y_$0:sets[ind_1],y_$0 subseteq f);")
    simplify-insistently
    simplify
    simplify-insistently
    (apply-macete-with-minor-premises diff-conditionally-onto)
    (incorporate-antecedent "with(f,y_$0:sets[ind_1],y_$0 subseteq f);")
    simplify-insistently
    (incorporate-antecedent "with(y_$0,f:sets[ind_1],f=y_$0);")
    (move-to-ancestor 1)
    (backchain-backwards "with(y_$0,f:sets[ind_1],f=y_$0);")
    set-containment-script
    direct-and-antecedent-inference-strategy
    simplify
    (weaken (1))
    (incorporate-antecedent "with(p:prop,p and p and p);")
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%equality-of-conditional-term)
    (apply-macete-with-minor-premises tr%equality-of-conditional-term-backwards)
    (apply-macete-with-minor-premises diff-conditionally-one-to-one)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(x_$0:sets[ind_1],x:ind_1,s:sets[ind_1],
  x_$0 in power(s) inters filter(x));")
    unfold-defined-constants
    simplify-insistently
    (incorporate-antecedent "with(x_$3:sets[ind_1],x:ind_1,s:sets[ind_1],
  x_$3 in power(s) inters filter(x));")
    unfold-defined-constants
    simplify-insistently

    )))

(def-constant combinations
  "lambda(s:sets[ind_1], n:nn, indic{a:sets[ind_1], a subseteq s and f_card{a}=n})"
  (theory generic-theory-1))

(def-theorem combination-decomposition
  "forall(s:sets[ind_1], x:ind_1, n:nn, 
            x in s 
            implies
         combinations(s,n)=combinations(s diff singleton{x},n) union 
                           combinations(s,n) inters filter(x))"
  (theory generic-theory-1)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    set-equality-script
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,not(p));")
    simplify-insistently
    (contrapose "with(p:prop,not(p));")
    simplify
    direct-and-antecedent-inference-strategy
    set-containment-script
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f,x:sets[ind_1],x subseteq f);")
    simplify-insistently
    )))


(def-theorem combination-disjointness
  "forall(s:sets[ind_1], x:ind_1, n:nn, 
         combinations(s diff singleton{x},n) disj combinations(s,n) inters filter(x))"
  (theory generic-theory-1)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    simplify-insistently
    
    )))



(def-theorem combination-reduction
  "forall(s:sets[ind_1], x:ind_1, n:nn, 
           x in s and 1<=n
             implies
       combinations(s,n) inters filter(x) equinumerous
       combinations(s diff singleton{x},n-1))"
  (theory  generic-theory-1)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (instantiate-existential ("lambda(t:sets[ind_1],
     if(t in combinations(s,n) inters filter(x), t diff singleton{x}, ?sets[ind_1]))"))
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises tr%indic-free-characterization-of-dom)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify
    (weaken (0))
    unfold-defined-constants
    (apply-macete-with-minor-premises tr%indic-free-characterization-of-ran)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%equality-of-conditional-term)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("y_$0 union singleton{x}"))
    set-containment-script
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f,y_$0:sets[ind_1],y_$0 subseteq f);")
    simplify-insistently
    simplify
    (apply-macete-with-minor-premises f-card-disjoint-union)
    (apply-macete-with-minor-premises singleton-has-f-card-one-lemma-2)
    (move-to-ancestor 1)
    (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
    simplify
    (apply-macete-with-minor-premises iota-free-definition-of-f-indic-q)
    (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
    (instantiate-existential ("1"))
    (incorporate-antecedent "with(f,s,y_$0:sets[ind_1],y_$0 subseteq s diff f);")
    simplify-insistently
    simplify-insistently
    (apply-macete-with-minor-premises diff-conditionally-onto)
    (incorporate-antecedent "with(f,y_$0:sets[ind_1],y_$0 subseteq f);")
    simplify-insistently
    (incorporate-antecedent "with(y_$0,f:sets[ind_1],f=y_$0);")
    (move-to-ancestor 1)
    (backchain-backwards "with(y_$0,f:sets[ind_1],f=y_$0);")
    set-containment-script
    direct-and-antecedent-inference-strategy
    simplify
    (backchain-backwards "with(y_$0,f:sets[ind_1],f=y_$0);")
    (apply-macete-with-minor-premises f_card_difference)
    (move-to-sibling 1)
    simplify-insistently
    (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
    simplify
    (weaken (1))
    (incorporate-antecedent "with(p:prop,p and p and p);")
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%equality-of-conditional-term)
    (apply-macete-with-minor-premises tr%equality-of-conditional-term-backwards)
    (apply-macete-with-minor-premises diff-conditionally-one-to-one)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(x_$0:sets[ind_1],x:ind_1,n:nn,s:sets[ind_1],
  x_$0 in combinations(s,n) inters filter(x));")
    unfold-defined-constants
    simplify-insistently
    (incorporate-antecedent "with(x_$3:sets[ind_1],x:ind_1,n:nn,s:sets[ind_1],
  x_$3 in combinations(s,n) inters filter(x));")
    unfold-defined-constants
    simplify-insistently
    )))


;;; Induction on finite sets:

(def-theorem power-card
  "forall(s:sets[ind_1],f_indic_q{s} implies f_card{power(s)}=2^f_card{s})"
  (theory  generic-theory-1)
  (usages transportable-macete)
  (proof
   (

    
    (block
     (script-comment "This is the basic set induction script.")
     (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "forsome(m:zz, 0<=m and n=m)")
     (move-to-sibling 1)
     (instantiate-existential ("n"))
     (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
     (backchain "with(n:nn,n=n);")
     (antecedent-inference "with(p:prop,forsome(m:zz,p));")
     (backchain "with(p:prop,p and p);")
     (incorporate-antecedent "with(n:nn,n=n);")
     (backchain "with(p:prop,p);")
     (antecedent-inference "with(p:prop,p);")
     (weaken (0))
     (cut-with-single-formula
      "forall(s:sets[ind_1], f_card{s}=m implies f_card{power(s)}=2^m)")
     (backchain "with(p:prop,forall(s:sets[ind_1],p));")
     (induction trivial-integer-inductor ("m"))
     )
    beta-reduce-repeatedly
    simplify
    (apply-macete-with-minor-premises empty-indic-has-f-card-zero)
    (apply-macete-with-minor-premises tr%singleton-has-f-card-one)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,p);")
    (instantiate-existential ("empty_indic{ind_1}"))
    (weaken (0))
    (unfold-single-defined-constant (0) power)
    set-equality-script
    direct-and-antecedent-inference-strategy
    set-equality-script
    (apply-macete-with-minor-premises indicator-facts-macete)
    (incorporate-antecedent "with(p:prop,p);")
    simplify-insistently
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) power)
    (cut-with-single-formula "forsome(x:ind_1, x in s)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises rev%positive-f-card-iff-nonempty)
    simplify
    (antecedent-inference "with(s:sets[ind_1],nonempty_indic_q{s});")
    (instantiate-universal-antecedent "with(p:prop,forall(s:sets[ind_1],p));"
				      ("s diff singleton{x}"))
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises f_card_difference)
    (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
    simplify
    simplify-insistently
    (force-substitution "power(s)"
			"power(s diff singleton{x}) union 
                  power(s) inters filter(x)"
			(0))
    (apply-macete-with-minor-premises power-decomposition)
    (apply-macete-with-minor-premises tr%f-card-disjoint-union)
    (cut-with-single-formula "f_card{power(s) inters filter(x)}=f_card{power(s diff singleton{x})}")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%f-card-equal-iff-finite-and-equinumerous)
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (apply-macete-with-minor-premises power-reduction)
    (apply-macete-with-minor-premises power-reduction)
    (unfold-single-defined-constant (0) power)
    (unfold-single-defined-constant (0) power)
    (backchain "with(f:sets[sets[ind_1]],f_card{f}=f_card{f});")
    (case-split ("t=0"))
    simplify
    (apply-macete-with-minor-premises exp-out)
    simplify
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    (cut-with-single-formula "f_card{power(s) inters filter(x)}=f_card{power(s diff singleton{x})}")
    (backchain "with(f:sets[sets[ind_1]],f_card{f}=f_card{f});")
    auto-instantiate-existential
    (apply-macete-with-minor-premises power-disjointness)
    (apply-macete-with-minor-premises power-decomposition)

    )))


(include-files
  (files    (imps theories/reals/comb-ident)))

(def-theorem subset-equal-if-equal-cardinality
  "forall(s,a:sets[ind_1], a subseteq s and f_card{a}=f_card{s} implies a=s)"
  (theory  generic-theory-1)
  (proof
   (

    
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "s subseteq a iff f_card{s diff a}=0")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises empty-indic-has-f-card-zero)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    set-containment-script
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,not(p));")
    simplify
    simplify-insistently
    set-containment-script
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "s diff a subseteq empty_indic{ind_1};")
    simplify-insistently
    (backchain "with(p:prop,p iff p);")
    (apply-macete-with-minor-premises f_card_difference)
    simplify
    )))


(def-theorem comb-reduction-schema
  "forall(p:[zz,zz,prop],
     forall(k,m:zz,
       1<=k and k<=m and p(m,k-1) and p(m,k) implies p(1+m,k))
      and 
     forall(k:zz,0<=k implies p(k,0))
      and 
     forall(j:zz,0<=j implies p(j,j))
      implies 
     forall(m,k:zz,k<=m and 0<=k implies p(m,k)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(m:zz,0<=m implies forall(k,j:zz,0<=k and k<=j and j<=m implies p(j,k)))")
    (backchain "with(p:prop,forall(m:zz,0<=m implies forall(k,j:zz,p)));")
    (instantiate-existential ("m"))
    simplify
    simplify
    (weaken (4 3))
    (induction trivial-integer-inductor ("m"))
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "k=0 and j=0")
    simplify
    simplify
    (case-split ("k=0"))
    simplify
    (case-split ("j<=t"))
    (backchain "forall(k,j:zz,
  with(p:prop,p and p and p)
   implies 
  with(p:[zz,zz,prop],p(j,k)));")
    direct-and-antecedent-inference-strategy
    (case-split ("k=j"))
    (backchain "with(j,k:zz,k=j);")
    simplify
    (force-substitution "j" "1+(j-1)" (0))
    (backchain "with(r:rr,
  forall(k,m:zz,
    with(p:prop,p and p and p and p)
     implies 
    with(p:[zz,zz,prop],p(r,k))));")
    direct-and-antecedent-inference-strategy
    (backchain "forall(k,j:zz,
  with(p:prop,p and p and p)
   implies 
  with(p:[zz,zz,prop],p(j,k)));")
    simplify
    (backchain "forall(k,j:zz,
  with(p:prop,p and p and p)
   implies 
  with(p:[zz,zz,prop],p(j,k)));")
    simplify
    simplify
    (backchain "forall(k,j:zz,
  with(p:prop,p and p and p)
   implies 
  with(p:[zz,zz,prop],p(j,k)));")
    simplify
    simplify
    )))
   

(def-theorem combinations-card
  "forall(s:sets[ind_1],k:zz,
     f_indic_q{s} and 0<=k and k<=f_card{s}
      implies 
     f_card{combinations(s,k)}=comb(f_card{s},k))"
  (theory generic-theory-1)
  (proof
   (


    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(m:zz, 0<=m and n=m)")
    (move-to-sibling 1)
    (instantiate-existential ("n"))
    (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
    (backchain "with(n:nn,n=n);")
    (antecedent-inference "with(p:prop,forsome(m:zz,p));")
    (backchain "with(p:prop,p and p);")
    (incorporate-antecedent "with(n:nn,n=n);")
    (backchain "with(p:prop,p and p);")
    (antecedent-inference "with(p:prop,p and p);")
    (weaken (0))
    direct-and-antecedent-inference-strategy
    (contrapose "with(s:sets[ind_1],k:zz,k<=f_card{s});")
    (backchain "with(m:zz,n:nn,n=m);")
    (contrapose "with(p:prop,not(p));")
    (incorporate-antecedent "with(m:zz,n:nn,n=m);")
    (cut-with-single-formula
	"forall(s:sets[ind_1], f_card{s}=m implies f_card{combinations(s,k)}=comb(m,k))")
    direct-inference
    (backchain "with(p:prop,forall(s:sets[ind_1],p));")
    (force-substitution "forall(s:sets[ind_1],
    f_card{s}=m implies 
    f_card{combinations(s,k)}=comb(m,k))"
			"lambda(m,k:zz,forall(s:sets[ind_1],
    f_card{s}=m implies 
    f_card{combinations(s,k)}=comb(m,k)))(m,k)"
			(0))
    (move-to-sibling 1)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises comb-reduction-schema)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (weaken (7 6 5))
    (cut-with-single-formula "forsome(x:ind_1, x in s_$0)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises rev%positive-f-card-iff-nonempty)
    simplify
    (antecedent-inference "with(s_$0:sets[ind_1],nonempty_indic_q{s_$0});")
    (instantiate-universal-antecedent "with(k_$0:zz,r:rr,m_$0:zz,
  forall(s_$0:sets[ind_1],
    f_card{s_$0}=m_$0
     implies 
    f_card{combinations(s_$0,r)}=comb(m_$0,k_$0-1)));"
				      ("s_$0 diff singleton{x}"))
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises f_card_difference)
    (move-to-sibling 1)
    set-containment-script
    simplify
    (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
    simplify
    (force-substitution 
     "combinations(s_$0,k_$0)"
     "combinations(s_$0 diff singleton{x},k_$0) union combinations(s_$0,k_$0) inters filter(x)"
     (0))
    (move-to-sibling 1)
    (apply-macete-with-minor-premises combination-decomposition)
    (apply-macete-with-minor-premises tr%f-card-disjoint-union)
    (cut-with-single-formula "f_card{combinations(s_$0 diff singleton{x},k_$0-1)}=
  f_card{combinations(s_$0,k_$0) inters filter(x)}")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%finite-and-equinumerous-implies-f-card-equal)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
    (move-to-sibling 1)
    (unfold-single-defined-constant (0) combinations)
    (apply-macete-with-minor-premises combination-reduction)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) combinations)
    (backchain-backwards "with(f:sets[sets[ind_1]],f_card{f}=f_card{f});")
    (backchain "with(r:rr,m_$0:zz,f:sets[sets[ind_1]],
  f_card{f}=comb(m_$0,r));")
    (backchain "with(p:prop,forall(s:sets[ind_1],p));")
    (apply-macete-with-minor-premises f_card_difference)
    (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
    (apply-macete-with-minor-premises comb-ident)
    simplify
    set-containment-script
    simplify
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    (cut-with-single-formula "f_card{combinations(s_$0 diff singleton{x},k_$0-1)}=
  f_card{combinations(s_$0,k_$0) inters filter(x)}")
    (backchain-backwards "with(f:sets[sets[ind_1]],f_card{f}=f_card{f});")
    (backchain "with(r:rr,m_$0:zz,f:sets[sets[ind_1]],
  f_card{f}=comb(m_$0,r));")
    (instantiate-existential ("comb(m_$0,k_$0-1)"))
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    (instantiate-existential ("f_card{combinations(s_$0 diff singleton{x},k_$0)}"))
    (unfold-single-defined-constant (0) combinations)
    (apply-macete-with-minor-premises combination-disjointness)
    (apply-macete-with-minor-premises comb-0-value-lemma)
    (apply-macete-with-minor-premises tr%singleton-has-f-card-one)
    (instantiate-existential ("empty_indic{ind_1}"))
    (unfold-single-defined-constant (0) combinations)
    set-equality-script
    (apply-macete-with-minor-premises empty-indic-has-f-card-zero)
    direct-and-antecedent-inference-strategy
    direct-and-antecedent-inference-strategy
    (backchain "with(f,x_$4:sets[ind_1],x_$4=f);")
    (weaken (0))
    simplify-insistently
    (apply-macete-with-minor-premises empty-indic-has-f-card-zero)
    (unfold-single-defined-constant (0) combinations)
    (apply-macete-with-minor-premises comb-m-value-lemma)
    (apply-macete-with-minor-premises tr%singleton-has-f-card-one)
    (instantiate-existential ("s"))
    (unfold-single-defined-constant (0) combinations)
    set-equality-script
    (apply-macete-with-minor-premises subset-equal-if-equal-cardinality)
    direct-and-antecedent-inference-strategy
    simplify
    (unfold-single-defined-constant (0) combinations)


    )))
