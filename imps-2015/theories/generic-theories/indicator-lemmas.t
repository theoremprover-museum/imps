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


(herald INDICATOR-LEMMAS)

(include-files
 (files (imps theories/generic-theories/indicators)))


;;; Empty indicator lemmas

(def-theorem EMPTY_INDIC-IS-EMPTY
  "empty_indic_q{empty_indic{uu}}"
  (theory indicators)
  (usages transportable transportable-rewrite)
  (proof (simplify-insistently)))

(def-theorem EQUALS-EMPTY-INDIC-IFF-EMPTY
  "forall(a:sets[uu], a=empty_indic{uu} iff empty_indic_q{a})"
  reverse
  (theory indicators)
  (usages transportable transportable-rewrite)
  (proof 
   (
    direct-and-antecedent-inference-strategy
    (backchain "with(a:sets[uu],a=empty_indic{uu})")
    (apply-macete-with-minor-premises empty_indic-is-empty)
    extensionality
    beta-reduce-repeatedly
    )))


;;; Union and intersection lemmas

(def-theorem UNION-COMMUTATIVITY 
  "forall(a,b:sets[uu], (a union b) = (b union a))"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    extensionality
    direct-inference
    simplify-insistently
    (case-split-on-conditionals (0))
    )))

(def-theorem INTERSECTION-COMMUTATIVITY 
  "forall(a,b:sets[uu], (a inters b) = (b inters a))"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    extensionality
    direct-inference
    simplify-insistently
    (case-split-on-conditionals (0))
    simplify
    (contrapose "with(p:prop, p)")
    simplify
    )))    

(def-theorem MEMBERSHIP-IN-UNION
  "forall(x:uu,a,b:sets[uu], x in (a union b) iff (x in a or x in b))"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem MEMBERSHIP-IN-INTERSECTION
  "forall(x:uu,a,b:sets[uu], x in (a inters b) iff (x in a and x in b))"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem DIFF-UNION-EQUAL-WHOLE
  "forall(x:uu,a,b:sets[uu], b subseteq a implies (a diff b) union b = a)"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    extensionality
    direct-inference
    simplify
    (instantiate-universal-antecedent "with(p:prop,p);" ("x_0"))
    (block 
      (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0)")
      direct-and-antecedent-inference-strategy
      simplify)
    (block 
      (script-comment "node added by `instantiate-universal-antecedent' at (0 0 1)")
      direct-and-antecedent-inference-strategy
      simplify)
    )))

(comment
 (proof
   (
    direct-and-antecedent-inference-strategy
    extensionality
    direct-inference
    simplify
    (instantiate-universal-antecedent "with(a,b:sets[uu],b subseteq a)" ("x_0"))
    (case-split-on-conditionals (0))
    (case-split-on-conditionals (0))
    (case-split-on-conditionals (0))
    )))


;;; Lemmas about subseteq

(def-theorem ELEMENT-OF-A-SUBSET-IS-AN-ELEMENT 		; 
  "forall(x:uu,b:sets[uu], 
     forsome(a:sets[uu], (x in a) and (a subseteq b))
       implies 
     (x in b))"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(b,a:sets[uu],a subseteq b)" 
     ("x"))
    )))

(def-theorem SUBSETEQ-REFLEXIVITY
  "forall(a:sets[uu], a subseteq a)"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem SUBSETEQ-ANTISYMMETRY
  "forall(a,b:sets[uu],  a=b iff ((a subseteq b) and (b subseteq a)))"
  (theory indicators)
  (usages transportable-macete)
  (proof				; 38 nodes
   (
    insistent-direct-inference-strategy
    (force-substitution "b" "a" (0))
    (force-substitution "a" "b" (0))
    extensionality
    direct-inference
    (antecedent-inference "with(b,a:sets[uu],a subseteq b and b subseteq a)")
    (instantiate-universal-antecedent "with(a,b:sets[uu],b subseteq a)" ("x_0"))
    (instantiate-universal-antecedent "with(b,a:sets[uu],a subseteq b)" ("x_0"))
    simplify
    (instantiate-universal-antecedent "with(b,a:sets[uu],a subseteq b)" ("x_0"))
    simplify
    )))

(def-theorem SUBSETEQ-TRANSITIVITY 
  "forall(a,b,c:sets[uu], 
     (a subseteq b) and (b subseteq c) implies (a subseteq c))"
  (theory indicators)
  (usages transportable-macete)
  (proof 
   (
    insistent-direct-inference-strategy 
    simplify-insistently
    )))


;;;  The following indicator conversions are all proved by simplify-insistently

(def-theorem UNION-DISJUNCTION-CONVERSION 
  "forall(x:uu, a,b:sets[uu], (x in (a union b)) iff (x in a or x in b))"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))
 
(def-theorem INTERSECTION-CONJUNCTION-CONVERSION 
  "forall(x:uu, a,b:sets[uu], (x in (a inters b)) iff (x in a and x in b))"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem SINGLETON-EQUALITY-CONVERSION 
  "forall(x,a:uu,x in singleton{a} iff x=a)"
  (theory indicators)
  (usages transportable-rewrite transportable-macete)
  (proof (simplify-insistently)))
 
(def-theorem DIFFERENCE-CONJUNCTION-CONVERSION 
  "forall(x:uu, a,b:sets[uu], (x in (a diff b)) iff (x in a and not (x in b)))"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently))) 

(def-compound-macete INDICATOR-CONVERSIONS
  (repeat 
   tr%union-disjunction-conversion
   tr%intersection-conjunction-conversion
   tr%singleton-equality-conversion
   tr%difference-conjunction-conversion))


;;; The following family indicator lemmas are all proved by simplify-insistently

(def-theorem BIG-UNION-MEMBER
  "forall(f:[index,sets[uu]],x:uu, 
     x in big_u{f} iff forsome(i:index,x in f(i)))"
  (theory family-indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem BIG-INTERSECTION-MEMBER
  "forall(f:[index,sets[uu]],
     x:uu, x in big_i{f} iff forall(i:index,x in f(i)))"
  (theory family-indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))
  

;;; Singleton lemmas

(def-theorem IN-SINGLETON-IFF-EQUALS-SINGLE-MEMBER
  "forall(x,y:uu, x in singleton{y} iff x=y)"
  reverse
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem SINGLETONS-HAVE-A-UNIQUE-MEMBER
  "forall(a:sets[uu],y:uu, a=singleton{y} iff y=iota(x:uu, x in a))"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (force-substitution "a" "singleton{y}" (0))
    beta-reduce-insistently
    (contrapose "with(y:uu,a:sets[uu],a=singleton{y})")
    extensionality
    (instantiate-existential ("b_$0"))
    simplify
    (force-substitution "y" "iota(x:uu,x in a)" (0))
    (eliminate-defined-iota-expression 0 u)
    extensionality
    direct-inference
    (instantiate-universal-antecedent "with(p:prop, forall(u_1:uu,p))" ("x_0"))
    simplify
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (simplify-antecedent "with(x_0:uu,a:sets[uu],not(x_0 in a))")
    simplify
    )))


;;; Set difference lemmas

(def-theorem DIFF-WITH-INDIC-IS-DISJ-FROM-INDIC
  "forall(a,b:sets[uu],  (a diff b) disj b)"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))

(def-theorem MEMBERSHIP-IN-DIFF
  "forall(x:uu,a,b:sets[uu], (x in a diff b) iff (x in a and not(x in b)))"
  (theory indicators)
  (usages transportable-macete)
  (proof (simplify-insistently)))


;;; Partition lemmas

(def-theorem DECREMENTED-PARTITION-LEMMA
  "forall(w:sets[sets[uu]],a,b:sets[uu], 
     partition_q{w,a} and b in w implies 
     partition_q{w diff singleton{b},a diff b})"
  (theory indicators)
  (usages transportable-macete)
  (proof				; 74 nodes
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(p:prop, forall(u,v:sets[uu],p))" ("u_$0" "v_$0"))
    (contrapose "with(p:prop, not(p))")
    (weaken (0 1 3 4 5))
    (incorporate-antecedent "with(p:prop, p)")
    simplify-insistently
    (contrapose "with(p:prop, not(p))")
    (weaken (0 2 3 4 5))
    (incorporate-antecedent "with(p:prop, p)")
    simplify-insistently
    (weaken (0))
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(p:prop, forall(x:uu,p))" ("x_$0"))
    (instantiate-existential ("u"))
    extensionality
    (instantiate-existential ("x_$0"))
    simplify
    (backchain "with(p:prop, forall(x:uu,p))")
    (instantiate-existential ("u_$0"))
    (instantiate-universal-antecedent 
     "with(p:prop, forall(u,v:sets[uu],p))" ("u_$0" "b"))
    (weaken (2 3 4 5 6))
    (incorporate-antecedent "with(p:prop, p)")
    simplify-insistently
    )))
  

;; Added Wed Jun  2 16:12:37 EDT 1993 by JT and MEN

(def-theorem UNION-OF-A-DIFFERENCE
  "forall(a,b:sets[uu], a subseteq b implies a union (b diff a) = b)"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises subseteq-antisymmetry)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(b,a:sets[uu],a subseteq b);")

    )))

;; added Thu Dec 16 14:25:51 EST 1993 by guttman 

(def-theorem difference-of-a-disjoint-union
  "forall(a,b:sets[uu], a inters b=empty_indic{uu} implies (a union b) diff a = b)"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
    (prove-by-logic-and-simplification 0)
    (block
      (script-comment
       "node added by `prove-by-logic-and-simplification' at (0 0 0 (1 . 0)
0 0 0 0 (1 . 1) (1 . 0) 1 0)")
      (contrapose "with(f:sets[uu],f=f);")
      simplify-insistently
      extensionality
      (instantiate-existential ("x_0"))
      simplify)
    (contrapose "with(f:sets[uu],f=f);"))))

(def-theorem difference-of-disjoint-sets
  "forall(a,b:sets[uu], a inters b=empty_indic{uu} implies a diff b = a)"
  (theory indicators)
  (usages transportable-macete)
  (proof 
   (
    simplify-insistently
    (prove-by-logic-and-simplification 0)
    (contrapose "with(f:sets[uu],f=f);")
    (prove-by-logic-and-simplification 0)
    auto-instantiate-existential)))


(def-theorem DIFFERENCE-OF-A-UNION
  "forall(a,b:sets[uu], (a union b) diff a = b diff a)"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
    (prove-by-logic-and-simplification 0))))

(def-theorem union-with-empty
  "forall(a:sets[uu], (a union empty_indic{uu}) = a)"
  (theory indicators)
  (usages transportable-macete)
  (proof
   ((prove-by-logic-and-simplification 0))))

;; (def-language indicators-w-subsort-language
;;   (embedded-language indicators)
;;   (sorts (vv uu)))
;; 
;; (def-theory indicators-w-subsort
;;   (language indicators-w-subsort-language)
;;   (component-theories indicators))
;; 
;; (def-theorem union-preserves-subsort
;;   "forall(a,b:sets[vv], #(a union b,sets[vv]))"
;;   (theory indicators-w-subsort)
;;   (usages transportable-macete transportable-rewrite))
