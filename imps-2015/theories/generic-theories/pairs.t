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


(herald PAIRS)

(load-section foundation)



;;; Parse specifications

(def-parse-syntax pair?
  (token pair_q)
  (null-method prefix-operator-method) 
  (binding 160))

(def-parse-syntax i-cross-product
  (token cross)
  (left-method infix-operator-method)
  (binding 101))


;;; Print specifications

(def-print-syntax pair?
  (token pair_q)
  (method present-prefix-operator)
  (binding 160))

(def-print-syntax i-cross-product
  (token " cross ")
  (method present-binary-infix-operator) 
  (binding 101))


;;; TeX print specifications

(def-print-syntax pair
  tex
  (token " \\langle " " \\rangle ")
  (method present-tex-delimited-expression)
  (binding 160))

(def-print-syntax pair?
  tex
  (token pair?)
  (method present-loglike-operator)
  (binding 160))

(def-print-syntax first
  tex
  (token " \\pi_1 ")
  (method present-loglike-operator)
  (binding 160))

(def-print-syntax second
  tex
  (token " \\pi_2 ")
  (method present-loglike-operator)
  (binding 160))


;;; Build quasi-constructors

(def-quasi-constructor PAIR
 "lambda(a:ind_1,b:ind_2,
    lambda(x:ind_1,y:ind_2, if(a=x and b=y, an%individual, ?unit%sort)))"
 (language pure-generic-theory-2)
 (fixed-theories the-kernel-theory))

(set-constructor-logical-transform
 (name->quasi-constructor 'pair)
 equate-to-type-qc-transform)

(def-quasi-constructor PAIR?
 "lambda(p:sets[ind_1,ind_2], forsome(x:ind_1,y:ind_2, p=pair(x,y)))"
 (language pure-generic-theory-2)
 (fixed-theories the-kernel-theory))

(def-quasi-constructor FIRST
 "lambda(p:sets[ind_1,ind_2], iota(x:ind_1,forsome(y:ind_2, p=pair(x,y))))"
 (language pure-generic-theory-2)
 (fixed-theories the-kernel-theory))

(def-quasi-constructor SECOND
 "lambda(p:sets[ind_1,ind_2], iota(y:ind_2,forsome(x:ind_1, p=pair(x,y))))"
 (language pure-generic-theory-2)
 (fixed-theories the-kernel-theory))

(def-quasi-constructor I-CROSS-PRODUCT
  "lambda(a:sets[ind_1],b:sets[ind_2],
     indic(p:sets[ind_1,ind_2], pair_q{p} and (first{p} in a) and (second{p} in b)))"
 (language pure-generic-theory-2)
 (fixed-theories the-kernel-theory))



;;; Theorems

(def-theorem PAIRS-ARE-PAIRS
  "forall(x:ind_1,y:ind_2, pair_q(pair(x,y)))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-inference
    (instantiate-existential ("x" "y"))
    )))

(def-theorem PAIRS-ARE-PAIRS-REWRITE
  "forall(x:ind_1,y:ind_2, pair_q(pair(x,y)) iff truth)"
  (theory pure-generic-theory-2)
  (usages transportable-rewrite)
  (proof
   (
    (apply-macete-with-minor-premises pairs-are-pairs)
    )))

(def-theorem UNIQUENESS-FOR-PAIRS
  "forall(x_1,x_2:ind_1,y_1,y_2:ind_2, 
     pair(x_1,y_1) = pair(x_2,y_2) iff (x_1 = x_2 and y_1 = y_2))" 
  (theory pure-generic-theory-2)
  (usages transportable-macete transportable-rewrite)
  (proof
   (


    direct-inference
    direct-inference
    (block 
      (script-comment "`direct-inference' at (0)")
      (contrapose "with(p:prop,p);")
      extensionality
      (instantiate-existential ("x_1" "y_1"))
      simplify
      (antecedent-inference "with(p:prop,p);")
      simplify
      simplify)
    simplify

    )))

(def-theorem REVERSE-PAIRS
  "forall(x_1,x_2:ind_1,y_1,y_2:ind_2, 
     pair(x_1,y_1) = pair(x_2,y_2) iff pair(y_1,x_1) = pair(y_2,x_2))" 
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises tr%uniqueness-for-pairs)
    direct-and-antecedent-inference-strategy
    )))

(def-theorem FIRST-DEFINED-ENTAILS-PAIR
  "forall(p:sets[ind_1,ind_2], #(first(p)) implies pair_q(p))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, p)")
    (eliminate-iota 0)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("y%iota"))
    (instantiate-existential ("y"))
    (contrapose "with(p:prop, forall(x:ind_1,y:ind_2,p))")
    (backchain "with(a,b:sets[ind_1,ind_2], a=b)")
    (apply-macete-with-minor-premises pairs-are-pairs)
    )))

(def-theorem SECOND-DEFINED-ENTAILS-PAIR
  "forall(p:sets[ind_1,ind_2], #(second(p)) implies pair_q(p))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, p)")
    (eliminate-iota 0)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("y%iota"))
    (instantiate-existential ("x"))
    (contrapose "with(p:prop, forall(x:ind_1,y:ind_2,p))")
    (backchain "with(a,b:sets[ind_1,ind_2], a=b)")
    (apply-macete-with-minor-premises pairs-are-pairs)
    )))

(def-theorem FIRST-PROJECTION
  "forall(x:ind_1,y:ind_2, first(pair(x,y)) = x)"
  (theory pure-generic-theory-2)
  (usages transportable-macete transportable-rewrite simplify-logically-first)
  (proof
   (
    direct-inference
    (eliminate-iota 0)
    (instantiate-existential ("x"))
    (instantiate-existential ("y"))
    (antecedent-inference-strategy (0 1))
    (incorporate-antecedent "with(p:prop, p)")
    (incorporate-antecedent "with(p:prop, p)")
    (apply-macete-with-minor-premises uniqueness-for-pairs)
    simplify
    )))

(def-theorem SECOND-PROJECTION
  "forall(x:ind_1,y:ind_2, second(pair(x,y)) = y)"
  (theory pure-generic-theory-2)
  (usages transportable-macete transportable-rewrite simplify-logically-first)
  (proof				; Uses first-projection
   (
    direct-inference
    (disable-quasi-constructor second)
    (apply-macete-with-minor-premises reverse-pairs)
    (enable-quasi-constructor second)
    (apply-macete-with-minor-premises tr%first-projection)
    )))

(def-theorem PAIR-FIRST-SECOND
  "forall(x:sets[ind_1,ind_2],
     pair_q(x) implies (pair(first(x),second(x)) = x))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (backchain-repeatedly ("with(p:prop, p)"))
    (apply-macete-with-minor-premises first-projection)
    (apply-macete-with-minor-premises second-projection)
    )))

(def-theorem PAIR-FIRST-SECOND-REWRITE
  "forall(x:sets[ind_1,ind_2],
    (pair(first(x),second(x)) 
    = if(pair_q(x),x,lambda(y:ind_1, z:ind_2, ?unit%sort))))"
  (theory pure-generic-theory-2)
  (usages transportable-rewrite simplify-logically-first)
  (proof
   (
    direct-inference
    (case-split ("pair_q{x}"))
    (apply-macete-with-minor-premises pair-first-second)
    simplify
    extensionality
    direct-inference
    simplify
    direct-inference
    (eliminate-iota 0)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("y%iota"))
    auto-instantiate-existential
    (contrapose "with(p:prop,not(p))")
    (weaken (0 1 2 4))
    (backchain "with(p:prop,p)")
    (apply-macete-with-minor-premises pairs-are-pairs)
    )))

(def-theorem FIRST-OF-A-PAIR-IS-DEFINED
  "forall(x:sets[ind_1,ind_2], pair_q(x) implies #(first(x)))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,p)")
    (apply-macete-with-minor-premises first-projection)
    )))

(def-theorem SECOND-OF-A-PAIR-IS-DEFINED
  "forall(x:sets[ind_1,ind_2], pair_q(x) implies #(second(x)))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,p)")
    (apply-macete-with-minor-premises second-projection)
    )))

(def-theorem ALTERNATE-UNIQUENESS-FOR-PAIRS
  "forall(x,y:sets[ind_1,ind_2], 
     (pair_q(x) and pair_q(y))
      implies 
     x=y iff (first(x) = first(y) and second(x) = second(y)))"
  (theory pure-generic-theory-2)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (weaken (1))
    simplify
    (apply-macete-with-minor-premises first-of-a-pair-is-defined)
    (instantiate-existential ("x_$0" "y_$0"))
    (weaken (1 2))
    simplify
    (apply-macete-with-minor-premises second-of-a-pair-is-defined)
    (incorporate-antecedent "with(y,x:sets[ind_1,ind_2],first{x}=first{y})")
    (incorporate-antecedent "with(y,x:sets[ind_1,ind_2],second{x}=second{y})")
    (backchain-repeatedly 
     ("with(y_$0:ind_2,x_$0:ind_1,x:sets[ind_1,ind_2], x=pair{x_$0,y_$0})"))
    (backchain-repeatedly 
     ("with(y_$2:ind_2,x_$2:ind_1,y:sets[ind_1,ind_2], y=pair{x_$2,y_$2})"))
    (apply-macete-with-minor-premises first-projection)
    (apply-macete-with-minor-premises second-projection)
    (apply-macete-with-minor-premises uniqueness-for-pairs)
    direct-and-antecedent-inference-strategy
    )))


;;; Rewrite rules macete

(def-compound-macete REWRITE-RULES-FOR-PAIRS
  (series
   (repeat
    tr%pairs-are-pairs
    tr%first-projection
    tr%second-projection
    tr%pair-first-second)
   simplify))




;;;(make-presentation-format *tex-form* 'pair (list " \\langle " " \\rangle ") present-tex-delimited-expression 160)
;;;(make-presentation-format *tex-form* 'pair? 'pair? present-loglike-operator 160)
;;;(make-presentation-format *tex-form* 'first " \\pi_1 "  present-loglike-operator 160)
;;;(make-presentation-format *tex-form* 'second " \\pi_2 "  present-loglike-operator 160)

