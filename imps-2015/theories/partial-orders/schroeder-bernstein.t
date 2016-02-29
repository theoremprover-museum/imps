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


(herald schroeder-bernstein)

; The following def-forms are now in sb-prelim. The file was broken up 
; beacuse the proof of the last theorem uses up too many pages.
;  
; (include-files (files (imps theories/partial-orders/sb-prelim))) 
;
; below. JT 

(comment
 (include-files
  (files (imps theories/partial-orders/knaster-fixed-point-theorem)))

 (def-constant set%prec
   "lambda(a,b:sets[ind_1], a subseteq b)"
   (theory generic-theory-1))
	    	    
 (def-parse-syntax set%prec
   (left-method infix-operator-method)
   (binding 80))

 (def-print-syntax set%prec
   (token " set%prec ")
   (method present-binary-infix-operator) 
   (binding 80))

 (def-theorem ()
   "forall(a,c:sets[ind_1],
     forsome(b:sets[ind_1],a set%prec b and b set%prec c)
      implies 
     a set%prec c)"
   (theory generic-theory-1)
   (proof
    (

    
     unfold-defined-constants
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises tr%subseteq-transitivity)
     auto-instantiate-existential
     )))

 (def-theorem ()
   "forall(a:sets[ind_1],a set%prec a)"
   (theory generic-theory-1)
   (proof
    (


     (unfold-single-defined-constant (0) set%prec)
     )))

 (def-theorem ()
   "forall(a,b:sets[ind_1],
           a set%prec b and b set%prec a implies a=b)"
   (theory generic-theory-1)
   (proof
    (
     unfold-defined-constants
     (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
     )))

 (def-theorem ()
   "forall(p:[sets[ind_1],prop],
     nonvacuous_q{p}
      and 
     forsome(alpha:sets[ind_1],
       forall(theta:sets[ind_1],
         p(theta) implies theta set%prec alpha))
      implies 
     forsome(gamma:sets[ind_1],
       forall(theta:sets[ind_1],
         p(theta) implies theta set%prec gamma)
        and 
       forall(gamma_1:sets[ind_1],
         forall(theta:sets[ind_1],
           p(theta) implies theta set%prec gamma_1)
          implies 
      gamma set%prec gamma_1)))"
   (theory generic-theory-1)
   (proof
    (


     unfold-defined-constants
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("indic{x:ind_1, forsome(b:sets[ind_1], p(b) and x in b)}"))
     simplify-insistently
     direct-and-antecedent-inference-strategy
     auto-instantiate-existential
     simplify-insistently
     )))


 (def-translation complete-partial-order-to-generic-theory-1
   (source complete-partial-order)
   (target generic-theory-1)
   (fixed-theories h-o-real-arithmetic)
   (constant-pairs
    (prec set%prec))
   (sort-pairs (uu "sets[ind_1]"))
   (theory-interpretation-check using-simplification))


 (def-renamer cpo-gt-renamer
   (pairs
    (monotone gt%monotone)))

 (def-transported-symbols monotone
   (translation complete-partial-order-to-generic-theory-1)
   (renamer cpo-gt-renamer)
   )
    
 (def-overloading monotone
   (complete-partial-order monotone)
   (generic-theory-1  gt%monotone))

 (def-theorem monotonicity-of-sb-functional
   "forall(f:[ind_2,ind_1],g:[ind_1,ind_2],
            monotone(lambda(x:sets[ind_1],image(f,image(g,x)^^)^^)))"
   (theory generic-theory-2)
   lemma
   (proof
    (



     (unfold-single-defined-constant-globally gt%monotone)
     (unfold-single-defined-constant-globally set%prec)
     simplify-insistently
     (prove-by-logic-and-simplification 3)
     ))))

(include-files
 (files (imps theories/partial-orders/sb-prelim)))


; This file broken up, see note above. 

(def-theorem schroeder-bernstein-for-types
  "forall(f:[ind_2,ind_1],g:[ind_1,ind_2], 
              total_q{g,[ind_1,ind_2]} and 
              total_q{f,[ind_2,ind_1]} and
              injective_q{f} and 
              injective_q{g}
                implies
              forsome(h:[ind_1,ind_2], bijective_q{h}))"
  (theory generic-theory-2)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forsome(z:sets[ind_1], lambda(x:sets[ind_1],image(f,image(g,x)^^)^^)(z)=z)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%knaster-fixed-point-theorem)
    (apply-macete-with-minor-premises monotonicity-of-sb-functional)
    (block
     (script-comment
      "this proves the lattice of subsets satisfies the conditions of knaster's
 theorem.")
     direct-and-antecedent-inference-strategy
     unfold-defined-constants
     (instantiate-existential ("empty_indic{ind_1}" "indic{x:ind_1,truth}"))
     simplify-insistently
     simplify-insistently)
    (block
     (script-comment "this uses the fixed point property.")
     (antecedent-inference "with(p:prop,forsome(z:sets[ind_1],p));")
     (beta-reduce-antecedent "with(z:sets[ind_1],f:[ind_2,ind_1],g:[ind_1,ind_2],
  lambda(x:sets[ind_1],image{f,image{g,x}^^}^^)(z)=z);")
     (move-to-ancestor 1)
     (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("lambda(x:ind_1,if(x in z, g(x), inverse{f}(x)))"))
     insistent-direct-inference-strategy
     beta-reduce-repeatedly)
    (block
     (script-comment "this proves totality")
     (case-split ("x_$1 in z"))
     simplify
     simplify
     (apply-macete-with-minor-premises eliminate-iota-macete)
     (instantiate-universal-antecedent "with(z:sets[ind_1],p:prop,
  forall(x:ind_1,forall(x_$1:ind_2,p) implies x in z));"
				       ("x_$1"))
     (instantiate-existential ("x_$3"))
     (backchain "with(f:[ind_2,ind_1],injective_q{f});"))
    beta-reduce-repeatedly
    (case-split ("forsome(x:ind_1, x in z and y_$1=g(x))"))
    (instantiate-existential ("x"))
    simplify
    (instantiate-existential ("f(y_$1)"))
    (cut-with-single-formula "not(f(y_$1) in z)")
    simplify
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (backchain "with(f:[ind_2,ind_1],injective_q{f});")
    (contrapose "with(p:prop,not(p));")
    (instantiate-universal-antecedent "with(p:prop,z:sets[ind_1],
  forall(x_$0:ind_1,x_$0 in z implies forall(x_$1:ind_2,p)));"
				      ("f(y_$1)"))
    (backchain "with(p:prop,forall(x_$3:ind_2,p or p));")
    insistent-direct-inference
    beta-reduce-repeatedly
    (case-split ("x_1 in z" "x_2 in z"))
    direct-and-antecedent-inference-strategy
    (backchain "with(g:[ind_1,ind_2],injective_q{g});")
    (simplify-antecedent "with(i:ind_2,i=i);")
    simplify
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy

    (instantiate-universal-antecedent "with(z:sets[ind_1],p:prop,
  forall(x:ind_1,forall(x_$1:ind_2,p) implies x in z));"
				      ("x_2"))
    (instantiate-universal-antecedent "with(p:prop,forall(x_$0:ind_1,p or p));"
				      ("x_1"))
    (simplify-antecedent "with(p:prop,not(p));")
    simplify
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(z:sets[ind_1],p:prop,
  forall(x:ind_1,forall(x_$1:ind_2,p) implies x in z));"
				      ("x_1"))
    (instantiate-universal-antecedent "with(p:prop,forall(x_$0:ind_1,p or p));"
				      ("x_2"))
    (simplify-antecedent "with(p:prop,not(p));")
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "injective_q{inverse{f}}")
    (backchain "with(f:[ind_2,ind_1],injective_q{inverse{f}});")
    simplify-insistently
    (apply-macete-with-minor-premises tr%inverse-is-injective)

    )))






