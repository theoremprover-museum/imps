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


(herald linear-order)

(load-section partial-orders)
(load-section basic-cardinality)

(def-theorem removing-an-element-from-a-finite-set
  "forall(s:sets[ind_1], x:ind_1, f_indic_q{s} and x in s implies 
                         f_card{s}=f_card{s diff singleton{x}}+1)"
  (usages transportable-macete)
  (theory generic-theory-1)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (force-substitution "s" "(s diff singleton{x}) union singleton{x}
" (0))
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%diff-union-equal-whole)
    simplify-insistently
    (apply-macete-with-minor-premises f-card-disjoint-union)
    (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
    (cut-with-single-formula "#(f_card{s diff singleton{x}})")
    simplify
    (apply-macete-with-minor-premises subset-of-finite-indic-is-finite)
    (instantiate-existential ("s"))
    simplify-insistently
    (apply-macete-with-minor-premises iota-free-definition-of-f-indic-q)
    (apply-macete-with-minor-premises singleton-has-f-card-one-rewrite)
    (instantiate-existential ("1"))
    (apply-macete-with-minor-premises tr%diff-with-indic-is-disj-from-indic)
    )))

(def-constant maximal
  "lambda(x:uu,s:sets[uu], x in s and forall(y:uu, y in s and x prec y implies x=y))"
  (theory partial-order))



(def-theorem finite-sets-have-maximal-elements
  "forall(s:sets[uu], f_indic_q{s} and nonempty_indic_q{s} 
                       implies 
                      forsome(x:uu, maximal(x,s)))"
  (theory partial-order)
  (usages transportable-macete)
  (proof
   (

    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(m:zz, 1<=m and n=m)")
    (move-to-sibling 1)
    (instantiate-existential ("n"))
    (backchain-backwards "with(n:nn,n=n);")
    (force-substitution "1" "f_card{singleton{x}}" (0))
    (apply-macete-with-minor-premises tr%f-card-leq-iff-finite-and-embeds)
    (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
    direct-and-antecedent-inference-strategy
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%subset-embeds-in-superset)
    simplify-insistently
    (instantiate-existential ("n"))
    (apply-macete-with-minor-premises tr%singleton-has-f-card-one-rewrite)
    (antecedent-inference "with(p:prop,forsome(m:zz,p));")
    (incorporate-antecedent "with(n:nn,n=n);")
    (backchain "with(p:prop,p and p);")
    (antecedent-inference "with(p:prop,p and p);")
    (weaken (0))
    (weaken (1))
    (cut-with-single-formula "forall(s:sets[uu], f_card{s}=m implies forsome(x_$4:uu,maximal(x_$4,s)))")
    (backchain "with(p:prop,forall(s:sets[uu],p));")
    (induction trivial-integer-inductor ("m"))
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%singleton-has-f-card-one)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("y"))
    (unfold-single-defined-constant (0) maximal)
    (backchain "with(p:prop,p);")
    (backchain "with(p:prop,p);")
    (apply-macete-with-minor-premises tr%singleton-equality-conversion)
    simplify
    (cut-with-single-formula "forsome(x:uu, x in s)")
    (antecedent-inference "with(s:sets[uu],nonempty_indic_q{s});")
    (instantiate-universal-antecedent "with(p:prop,forall(s:sets[uu],p));"
				      ("s diff singleton{x}"))
    (contrapose "with(p:prop,not(p));")
    (cut-with-single-formula "f_card{s}=f_card{s diff singleton{x}}+1")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%removing-an-element-from-a-finite-set)
    simplify
    (case-split ("x_$9 prec x"))
    (instantiate-existential ("x"))
    (unfold-single-defined-constant (0) maximal)
    direct-and-antecedent-inference-strategy
    (contrapose "with(f:sets[uu],x_$9:uu,maximal(x_$9,f));")
    (unfold-single-defined-constant (0) maximal)
    (contrapose "with(p:prop,not(p));")
    (antecedent-inference "with(p:prop,p and p);")
    (contrapose "with(p:prop,forall(y_$0:uu,p));")
    (instantiate-existential ("y"))
    simplify-insistently
    (apply-macete-with-minor-premises prec-transitivity)
    auto-instantiate-existential
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises prec-anti-symmetry)
    simplify
    (instantiate-existential ("x_$9"))
    (incorporate-antecedent "with(f:sets[uu],x_$9:uu,maximal(x_$9,f));")
    (unfold-single-defined-constant-globally maximal)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(x_$9:uu,f,s:sets[uu],x_$9 in s diff f);")
    simplify-insistently
    simplify
    (backchain "with(p:prop,forall(y_$0:uu,p));")
    (cut-with-single-formula "not(x=y)")
    (move-to-ancestor 1)
    simplify-insistently
    (simplify-antecedent "with(y,x_$9:uu,x_$9 prec y);")
    (apply-macete-with-minor-premises tr%rev%positive-f-card-iff-nonempty)
    simplify


    )))


(def-renamer third-renamer
  (pairs
   (maximal minimal)))

(def-transported-symbols (maximal)
  (translation order-reverse)
  (renamer third-renamer))

(def-theorem finite-sets-have-minimal-elements
  "forall(s:sets[uu], f_indic_q{s} and nonempty_indic_q{s} 
                       implies 
                      forsome(x:uu, minimal(x,s)))"
  (theory partial-order)
  (usages transportable-macete)
  (proof
   (

    
    (apply-macete-with-minor-premises tr%finite-sets-have-maximal-elements)
    )))


(def-theory linear-order
  (component-theories partial-order)
  (axioms
   (totality-of-order
    "forall(a,b:uu, a prec b or b prec a)")))

(def-constant maximum
  "lambda(x:uu, s:sets[uu], x in s and forall(y:uu, y in s implies y prec x))"
  (theory partial-order))


(def-theorem maximal-is-maximum
  "forall(a:uu, s:sets[uu], maximal(a,s) implies maximum(a,s))"
  (usages transportable-macete)
  (theory linear-order)
  (proof
   (


    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "y prec a or a prec a")
    (move-to-ancestor 1)
    (cut-with-single-formula "y prec a or a prec y")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises totality-of-order)
    (antecedent-inference "with(p:prop,p or p);")
    (instantiate-universal-antecedent "with(p:prop,forall(y:uu,p));" ("y"))
    simplify

    )))
    
(def-renamer fourth-renamer
  (pairs
   (maximum minimum)))

(def-transported-symbols (maximum)
  (translation order-reverse)
  (renamer fourth-renamer))

(def-translation linear-order-reverse
  (source linear-order)
  (target linear-order)
  (core-translation order-reverse)
  (theory-interpretation-check using-simplification))

(def-theorem minimal-is-minimum
  "forall(a:uu, s:sets[uu], minimal(a,s) implies minimum(a,s))"
  (theory linear-order)
  (proof
   (


    (apply-macete-with-minor-premises tr%maximal-is-maximum)

    )))


(def-theorem finite-sets-have-maximum-elements
  "forall(s:sets[uu], f_indic_q{s} and nonempty_indic_q{s} 
                       implies 
                      forsome(x:uu, maximum(x,s)))"
  (theory linear-order)
  (usages transportable-macete)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises maximal-is-maximum)
    (apply-macete-with-minor-premises finite-sets-have-maximal-elements)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x"))
    )))

(def-theorem finite-sets-have-minimum-elements
  "forall(s:sets[uu], f_indic_q{s} and nonempty_indic_q{s} 
                       implies 
                      forsome(x:uu, minimum(x,s)))"
  (theory linear-order)
  (usages transportable-macete)
  (proof
   (
    
    (apply-macete-with-minor-premises tr%finite-sets-have-maximum-elements)
    )))



