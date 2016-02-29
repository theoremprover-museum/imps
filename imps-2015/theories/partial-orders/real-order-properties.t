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


(herald real-order-properties)

(include-files
 (files (imps theories/partial-orders/partial-order)))


;;;(def-constant majorizes
;;;  "lambda(y:rr,s:sets[rr], forall(x:rr, x in s implies x<=y))"
;;;  (theory h-o-real-arithmetic))

(def-parse-syntax majorizes
  (left-method infix-operator-method)
  (binding 75))

(def-print-syntax majorizes
  (token " majorizes ")
  (method present-binary-infix-operator) 
  (binding 75))

(def-print-syntax majorizes
  tex
  (token " \\sqsupseteq ")
  (method present-tex-binary-infix-operator) 
  (binding 75))

(def-parse-syntax minorizes
  (left-method infix-operator-method)
  (binding 75))

(def-print-syntax minorizes
  (token " minorizes ")
  (method present-binary-infix-operator) 
  (binding 75))

(def-print-syntax minorizes
  tex
  (token " \\sqsubseteq ")
  (method present-tex-binary-infix-operator) 
  (binding 75))

(comment

 (def-theorem sign-reverse-1
   "forall(x,y:rr,x<=y iff -y<=-x)"
   (theory h-o-real-arithmetic)
   (proof (simplify)))
 
 (def-theorem sign-reverse-2
   "forall(x,y:rr,-(-x)=x)"
   (theory h-o-real-arithmetic)
   (proof (simplify)))

 (def-compound-macete sign-reverse
   (sequential
    sign-reverse-1
    sign-reverse-2))

 (def-theorem ()
   "forall(p:[rr,prop],
    nonvacuous_q{p}
     and 
    forsome(alpha:rr,
      forall(theta:rr,p(theta) implies alpha<=theta))
     implies 
    forsome(gamma:rr,
      forall(theta:rr,p(theta) implies gamma<=theta)
       and 
      forall(gamma_1:rr,
        forall(theta:rr,p(theta) implies gamma_1<=theta)
         implies 
        gamma_1<=gamma)))"
   (theory  h-o-real-arithmetic)
   (usages transportable-macete)
   (proof (direct-and-antecedent-inference-strategy
	   (instantiate-theorem completeness ("lambda(x:rr,p(-x))"))
	   (contrapose 0)
	   (instantiate-existential ("-x_0"))
	   simplify
	   (contrapose 0)
	   (instantiate-existential ("-alpha"))
	   (apply-macete-with-minor-premises sign-reverse)
	   (backchain "forall(theta:rr,p(theta) implies alpha<=theta)")
	   (instantiate-existential ("-gamma"))
	   (apply-macete-with-minor-premises sign-reverse)
	   (backchain "forall(theta:rr,lambda(x:rr,p(-x))(theta) implies theta<=gamma)")
	   simplify
	   (apply-macete-with-minor-premises sign-reverse)
	   (backchain "forall(gamma_1:rr,forall(theta:rr,
                        lambda(x:rr,p(-x))(theta) implies theta<=gamma_1)
                           implies 
                          gamma<=gamma_1)")
	   beta-reduce-repeatedly
	   direct-and-antecedent-inference-strategy
	   (apply-macete-with-minor-premises sign-reverse)
	   (backchain "forall(theta_$0:rr,p(theta_$0) implies gamma_$0<=theta_$0)"))))

 )



(def-translation complete-partial-order-to-h-o-real-arithmetic
  (source complete-partial-order)
  (target h-o-real-arithmetic)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs
   (prec <=)
   (rev%prec "lambda(a,b:rr,b<=a)"))
  (sort-pairs (uu rr))
  (theory-interpretation-check using-simplification))
   

(def-renamer partial-order-rr-renamer
  (pairs
   (prec%increasing nondecreasing)
   (rev%prec%increasing nonincreasing)
   (prec%majorizes majorizes)
   (prec%minorizes minorizes)
   (prec%sup sup)
   (prec%inf inf)
   (prec%lim%inf lim%inf)
   (prec%lim%sup lim%sup)))

(def-transported-symbols
  (prec%increasing
   rev%prec%increasing
   prec%majorizes 
   prec%minorizes
   prec%sup 
   prec%inf
   prec%lim%inf
   prec%lim%sup)
  (translation complete-partial-order-to-h-o-real-arithmetic)
  (renamer partial-order-rr-renamer))

(def-translation index-families
  (source mappings-into-a-partial-order)
  (target generic-theory-1)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs (prec <=))
  (sort-pairs (uu rr))
  (theory-interpretation-check using-simplification))


(def-theorem sum-inequality-macete
  "forall(x,y,z,u:rr, x<=z and y<=u implies x+y<=z+u)"
  (proof (simplify))
  (theory h-o-real-arithmetic))

(def-theorem sup-sum
  "forall(f,g:[ind_1,rr], #(sup(ran{f})) and #(sup(ran{g})) and nonempty_indic_q{dom{f} inters dom{g}} implies sup(ran{lambda(x:ind_1,f(x)+g(x))})<=sup(ran{f})+sup(ran{g}))"

  (proof
   
   (direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f(n_$0)<=sup(ran{f}) and g(n_$0)<=sup(ran{g})")
    simplify
    (apply-macete-with-minor-premises tr%prec%sup-dominates-values)
    direct-and-antecedent-inference-strategy
    simplify-insistently
    simplify-insistently
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    (instantiate-existential ("x_$0"))
    (incorporate-antecedent "with(x_$0:ind_1,g,f:[ind_1,rr],x_$0 in dom{f} inters dom{g})")
    simplify
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    (instantiate-existential ("sup(ran{f})+sup(ran{g})"))
    (cut-with-single-formula "f(n_$1)<=sup(ran{f}) and g(n_$1)<=sup(ran{g})")
    simplify
    (apply-macete-with-minor-premises tr%prec%sup-dominates-values)
    direct-and-antecedent-inference-strategy
    simplify
    simplify))


  (theory generic-theory-1))

