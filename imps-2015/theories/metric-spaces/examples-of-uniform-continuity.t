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


(herald examples-of-uniform-continuity)

(include-files
 (files (imps theories/metric-spaces/metric-space-pairs)
	(imps theories/metric-spaces/metric-space-supplements)
	(imps theories/metric-spaces/examples-of-continuity)))


(def-constant quadratic%bound
  "lambda(f:[pp_0,pp_1], 
             forsome(a:rr, 0<=a and forall(x,y:pp_0,#(f(x)) and #(f(y)) implies dist_1(f(x),f(y))<=dist_0(x,y)*(a+dist_0(x,y)))))"
  (theory metric-spaces-2-tuples))

;;;(def-theorem monotone-product-lemma
;;;  "forall(x,y,z,u:rr, 0<=x and x<=y and 0<=u and u<=z implies x*u<=y*z)"
;;;
;;;  (proof
;;;
;;;   (
;;;
;;;    direct-and-antecedent-inference-strategy
;;;    (apply-macete-with-minor-premises transitivity-of-<=)
;;;    (instantiate-existential ("x*z"))
;;;    (cut-with-single-formula "0<=x*(z-u)")
;;;    simplify
;;;    (apply-macete-with-minor-premises positivity-for-products)
;;;    simplify
;;;    (cut-with-single-formula "0<=(y-x)*z")
;;;    simplify
;;;    (apply-macete-with-minor-premises positivity-for-products)
;;;    simplify
;;;
;;;
;;;    )
;;;
;;;
;;;   )
;;;  (theory h-o-real-arithmetic))

;; It is very instructive to compare this proof with the corresponding theorem for
;; continuity.

(def-theorem quadratic-is-uniformly-continuous
  "forall(f:[pp_0,pp_1], quadratic%bound(f) implies uniformly%continuous(f))"

  (proof


   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("min(1,eps/(1+a))"))
    (weaken (0))
    (unfold-single-defined-constant (0) min)
    (case-split ("1<=eps/(1+a)"))
    simplify
    simplify
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (antecedent-inference "with(a,eps:rr,y_$0,x_$0:pp_0,f:[pp_0,pp_1],
  #(f(x_$0))
   and 
  #(f(y_$0))
   and 
  dist_0(x_$0,y_$0)<=min(1,eps/(1+a)));")
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("dist_0(x_$0,y_$0)*(a+dist_0(x_$0,y_$0))"))
    (backchain "with(a:rr,f:[pp_0,pp_1],
  forall(x,y:pp_0,
    #(f(x)) and #(f(y))
     implies 
    dist_1(f(x),f(y))<=dist_0(x,y)*(a+dist_0(x,y))));")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("(eps/(1+a))*(a+1)"))
    (apply-macete-with-minor-premises monotone-product-lemma)
    (cut-with-single-formula "min(1,eps/(1+a))<=1 and min(1,eps/(1+a))<=eps/(1+a)")
    simplify
    (apply-macete-with-minor-premises minimum-2nd-arg)
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (instantiate-universal-antecedent "with(a:rr,f:[pp_0,pp_1],
  forall(x,y:pp_0,
    #(f(x)) and #(f(y))
     implies 
    dist_1(f(x),f(y))<=dist_0(x,y)*(a+dist_0(x,y))));" ("x_$0" "y_$0"))


    ))

  
  (usages transportable-macete)
  (theory metric-spaces-2-tuples))

