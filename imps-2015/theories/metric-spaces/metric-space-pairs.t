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


(herald METRIC-SPACE-PAIRS)


(include-files
 (files (imps theories/metric-spaces/metric-spaces)
	(imps theories/metric-spaces/metric-space-supplements)))

(def-theory-ensemble-multiple metric-spaces 2)

(def-theory-ensemble-overloadings metric-spaces (1))

(def-constant continuous%at%point
  "lambda(f:[pp_0,pp_1],x:pp_0,forall(eps:rr,0<eps 
       implies 
       forsome(delta:rr,0<delta 
          and forall(y:pp_0,dist_0(x,y)<=delta implies dist_1(f(x),f(y))<=eps))))"
  (theory metric-spaces-2-tuples))

;;; Try to modify this definition slightly, so the domain does not have to be open:
;;; There are advantages to doing it this way; there are also disadvantages.
;;; For instance, the interchange of limits formula is no longer true.

;;;(def-constant continuous%at%point
;;;  "lambda(f:[pp_0,pp_1],x:pp_0,#(f(x)) and forall(eps:rr,0<eps 
;;;       implies 
;;;       forsome(delta:rr,0<delta 
;;;          and forall(y:pp_0,dist_0(x,y)<=delta and #(f(y)) implies dist_1(f(x),f(y))<=eps))))"
;;;  (theory metric-spaces-2-tuples))



(def-constant continuous
  "lambda(f:[pp_0,pp_1],
     forall(v:sets[pp_1], open(v) implies open(inv_image(f,v))))"
  (theory metric-spaces-2-tuples))

(def-theory-ensemble-overloadings metric-spaces (2))

(def-theorem abstract-intermediate-value
  "forall(f:[pp_0,pp_1],o:sets[pp_0],
continuous(f) and total_q(f,[pp_0,pp_1]) and connected(o) implies connected(image(f,o)))"
  (theory metric-spaces-2-tuples)
  (proof (unfold-defined-constants
	  (apply-macete-with-minor-premises direct-image-to-inverse-image-conversion-macete)
	  (prove-by-logic-and-simplification 3))))
	  

(def-theorem abstract-bolzano-weierstrass
  "forall(f:[pp_0,pp_1],o:sets[pp_0],
continuous(f) and total_q(f,[pp_0,pp_1]) and compact(o) implies compact(image(f,o)))"
  (theory metric-spaces-2-tuples)
  (proof (unfold-defined-constants
	  (apply-macete-with-minor-premises covers-direct-image-to-inverse-image-conversion-macete)
	  (prove-by-logic-and-simplification 3))))

(def-theorem eps-delta-characterization-of-continuity
  "forall(f:[pp_0,pp_1],total_q{f,[pp_0,pp_1]} 
                   implies
                  continuous(f) 
                  iff
                  forall(x:pp_0,continuous%at%point(f,x)))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)

  (proof

   (

    unfold-defined-constants
    direct-inference
    direct-inference
    direct-inference
    (block (script-comment "node added by `direct-inference' at (0)")
	   (instantiate-universal-antecedent "with(p:prop,forall(v:sets[pp_1],p));"
					     (" open%ball(f(x),eps)"))
	   (block (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0 0 0)")
		  (contrapose "with(p:prop,not(p));")
		  (apply-macete-with-minor-premises tr%open-balls-are-open))
	   (block (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0 0 1)")
		  (incorporate-antecedent "with(f:sets[pp_0],open(f));")
		  unfold-defined-constants-repeatedly
		  simplify-insistently
		  direct-and-antecedent-inference-strategy
		  (instantiate-universal-antecedent "with(p:prop,forall(x_$2:pp_0,p implies p));"
						    ("x"))
		  (block (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0)")
			 (contrapose "with(p:prop,not(p));")
			 (apply-macete-with-minor-premises tr%zero-self-distance))
		  (block (script-comment "node added by `instantiate-universal-antecedent' at (0 0 1 0 0)")
			 (instantiate-existential ("delta_$1"))
			 (auto-instantiate-universal-antecedent "with(eps:rr,f:[pp_0,pp_1],delta_$1:rr,x:pp_0,
  forall(x_$0:pp_0,
    dist_0(x,x_$0)<=delta_$1
     implies 
    dist_1(f(x),f(x_$0))<eps))")
			 simplify))
	   (unfold-single-defined-constant (0) open%ball_1))

    (block (script-comment "node added by `direct-inference' at (1)")
	   unfold-defined-constants-repeatedly
	   simplify-insistently
	   direct-and-antecedent-inference-strategy
	   (auto-instantiate-universal-antecedent "with(v:sets[pp_1],p:prop,forall(x:pp_1, x in v implies p))")
	   (instantiate-universal-antecedent "with(p:prop,forall(x:pp_0,forall(eps:rr,p)));"
					     ("x_$2"))
	   (auto-instantiate-universal-antecedent "with(p:prop, forall(eps:rr,0<eps implies p))")
	   (instantiate-existential ("delta_$0"))
	   (backchain-repeatedly ("with(v:sets[pp_1],delta:rr,x_$2:pp_0,f:[pp_0,pp_1],
  forall(x_$0:pp_1,
    dist_1(f(x_$2),x_$0)<=delta implies x_$0 in v))"))
	   (backchain "with(p:prop,forall(y_$0:pp_0,p implies p));"))

    )

   )


  )

(def-constant lipschitz%bound%on
  "lambda(phi:[pp_0,pp_1],r:rr,s:sets[pp_0], 
     0<r and forall(x,y:pp_0, 
               x in s and y in s 
                implies  
               dist_1(phi(x),phi(y)) <= r * dist_0(x,y)))"
  (theory metric-spaces-2-tuples))

;;;(def-theorem lipschitz%bound%on%subsets
;;;  "forall(phi:[pp_0,pp_1],s,s_1:sets[pp_0],r:rr,s subseteq s_1 and 
;;; lipschitz%bound%on(phi,r,s_1) implies lipschitz%bound%on(phi,r,s))"
;;;  (theory metric-spaces-2-tuples)
;;;  (usages transportable-macete)
;;;  (proof "$METRIC_SPACES/proofs/lip-bnd-subsets.t"))

(def-constant lipschitz%bound
  "lambda(phi:[pp_0,pp_1],r:rr,
     lipschitz%bound%on(phi,r,sort_to_indic{pp_0}))"
  (theory  metric-spaces-2-tuples))

(def-theorem lipschitz-bound-is-total
  "forall(f:[pp_0,pp_1],r:rr,
     lipschitz%bound(f,r) implies total_q{f,[pp_0,pp_1]})"
  (theory  metric-spaces-2-tuples)
  (usages transportable-macete)
  (proof 
   (

    unfold-defined-constants
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    simplify

    )))

(def-constant uniformly%continuous
  "lambda(f:[pp_0,pp_1],
     forall(eps:rr, 
       0<eps 
        implies 
       forsome(delta:rr, 0<delta and
         forall(x,y:pp_0, 
           #(f(x)) and #(f(y)) and dist_0(x,y)<=delta 
            implies 
           dist_1(f(x),f(y))<=eps))))"
  (theory metric-spaces-2-tuples))

(def-theorem lipschitz-bound-is-uniformly-continuous
  "forall(f:[pp_0,pp_1],r:rr, 
     lipschitz%bound(f,r) implies uniformly%continuous(f))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)
  (proof
   (

    unfold-defined-constants
    (unfold-single-defined-constant (0) lipschitz%bound%on)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("eps/r"))
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("r*dist_0(x_$0,y_$0)"))
    (backchain 
      "with(r:rr,f:[pp_0,pp_1],forall(x_$0,y_$0:pp_0,
         x_$0 in sort_to_indic{pp_0} and y_$0 in sort_to_indic{pp_0}
          implies 
         dist_1(f(x_$0),f(y_$0))<=r*dist_0(x_$0,y_$0)));")
    simplify
    (incorporate-antecedent 
     "with(r,eps:rr,y_$0,x_$0:pp_0,f:[pp_0,pp_1],
        #(f(x_$0)) and #(f(y_$0)) and dist_0(x_$0,y_$0)<=eps/r);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    simplify


    )))


;;;the following formula is FALSE:

;;; forall(f:[pp_0,pp_1], r:rr, x:pp_0, uniformly%continuous(f) and #(f(x)) 
;;;                 implies continuous%at%point(f,x))

;; The reason is that according to our definition,  continuity at a point of a function
;; implies that its domain is an open set. Uniform continuity says nothing about the
;; domain.

(def-theorem total-uniformly-continuous-is-continuous
  "forall(f:[pp_0,pp_1], 
     uniformly%continuous(f) and total_q{f,[pp_0,pp_1]}
      implies 
     forall(x:pp_0, continuous%at%point(f,x)))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)
  (proof
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent 
     "with(p:prop, forall(eps:rr, 0<eps implies p))")
    (instantiate-existential ("delta"))
    (backchain "with(p,q:prop, forall(x,y:pp_0, p implies q))")
    simplify

    )))


(def-theorem lipschitz-bound-is-continuous
  "forall(f:[pp_0,pp_1],r:rr,x:pp_0, 
     lipschitz%bound(f,r) implies continuous%at%point(f,x))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)
  (proof 
   (

    (apply-macete-with-minor-premises total-uniformly-continuous-is-continuous)
    (apply-macete-with-minor-premises lipschitz-bound-is-uniformly-continuous)
    (apply-macete-with-minor-premises lipschitz-bound-is-total)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("r"))

    )))

