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

(herald ULTRAMETRIC-SPACES)

(load-section metric-space-pairs)


(def-theory ULTRAMETRIC-SPACES
  (component-theories h-o-real-arithmetic)
  (language metric-spaces-language)
  (axioms
   (positivity-of-distance
    "forall(x,y:pp, 0<=dist(x,y))" transportable-macete)
   (point-separation-for-distance
    "forall(x,y:pp, x=y iff dist(x,y)=0)" transportable-macete)
   (ultrametric-symmetry-of-distance
    "forall(x,y:pp, dist(x,y) = dist(y,x))" transportable-macete)
   (ultrametric-inequality-for-distance
    "forall(x,y,z:pp, dist(x,z)<=max(dist(x,y),dist(y,z)))" transportable-macete)))

(def-theorem ultrametic-spaces-are-metric
  "forall(x,y,z:pp,dist(x,z)<=dist(x,y)+dist(y,z))"
  (theory ULTRAMETRIC-SPACES)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "dist(x,z)<=max(dist(x,y),dist(y,z))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises ultrametric-inequality-for-distance)
    (cut-with-single-formula
     "forall(a,b:rr, 0<=a and 0<=b implies max(a,b)<=a+b)")
    (instantiate-universal-antecedent
     "with(p:prop,forall(a,b:rr,p));" ("dist(x,y)" "dist(y,z)"))
    (simplify-antecedent "with(p:prop,not(p));")
    (simplify-antecedent "with(p:prop,not(p));")
    simplify
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) max)
    (case-split ("a<=b"))
    simplify
    simplify
    )))

(def-theorem ultrametric-distance-bound-lemma
  "forall(x,y,z:pp, eps:rr, 
      dist(x,y)<=eps and dist(y,z)<=eps implies dist(x,z)<=eps)"
  (theory ultrametric-spaces)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "dist(x,z)<=max(dist(x,y),dist(y,z))")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(r:rr,z,x:pp,dist(x,z)<=max(r,r));")
      (unfold-single-defined-constant (0) max)
      (case-split ("dist(x,y)<=dist(y,z)"))
      simplify
      simplify)
    (apply-macete-with-minor-premises ultrametric-inequality-for-distance)

    )))


(def-theory-ensemble-instances metric-spaces 
  force-under-quick-load
  (target-theories ultrametric-spaces ultrametric-spaces)
  (permutations  (0) (0 1))
  (theory-interpretation-check using-simplification)
  (sorts (pp pp pp))
  (constants (dist dist dist)))


(def-theory-ensemble-overloadings metric-spaces 
  (1 2))


(def-theorem intersecting-balls-are-comparable
  "forall(x,y:pp, r,s:rr, 0<=r and r<=s and
               nonempty_indic_q{ball(x,r) inters ball(y,s)}
               implies
               ball(x,r) subseteq ball(y,s))"
  (theory ultrametric-spaces)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(x_$0:pp,f:sets[pp],x_$0 in f);")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%ball-membership-condition)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (apply-macete-with-minor-premises tr%ball-membership-condition)
    direct-inference
    (apply-macete-with-minor-premises ultrametric-distance-bound-lemma)
    auto-instantiate-existential
    (apply-macete-with-minor-premises ultrametric-distance-bound-lemma)
    (instantiate-existential ("x"))
    (block 
     (script-comment "`instantiate-existential' at (0 0)")
     (apply-macete-with-minor-premises tr%ultrametric-symmetry-of-distance)
     simplify)
    simplify

    )))

(def-theorem cauchy-ultrametric-condition
  "forall(x:[zz,pp], 
           cauchy(x) iff 
           forall(eps:rr, 
              0<eps implies 
              forsome(n:zz, forall(m:zz, n<=m implies dist(x(m),x(m+1))<=eps))))"
  (theory ultrametric-spaces)
  (usages transportable-macete)
  (proof
   (


    (apply-macete-with-minor-premises tr%cauchy-double-index-characterization)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
      (auto-instantiate-universal-antecedent "with(x:[zz,pp],
  forall(eps:rr,
    0<eps
     implies 
    forsome(n:zz,
      forall(p,q:zz,
        n<=p and n<=q implies dist(x(p),x(q))<=eps))));")
      (instantiate-existential ("n"))
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
      (auto-instantiate-universal-antecedent "with(x:[zz,pp],
  forall(eps:rr,
    0<eps
     implies 
    forsome(n:zz,
      forall(m:zz,n<=m implies dist(x(m),x(m+1))<=eps))));")
      (instantiate-existential ("n"))
      (apply-macete-with-minor-premises ultrametric-distance-bound-lemma)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	(instantiate-existential ("x(n)"))
	(move-to-ancestor 1)
	(cut-with-single-formula "forall(q:zz, n<=q implies dist(x(q),x(n))<=eps)")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  direct-and-antecedent-inference-strategy
	  simplify
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (2)")
	    (apply-macete-with-minor-premises tr%ultrametric-symmetry-of-distance)
	    simplify))
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (induction integer-inductor ("q"))
	  (block 
	    (script-comment "`induction' at (0 0 0)")
	    (apply-macete-with-minor-premises tr%zero-self-distance)
	    simplify
	    (block 
	      (script-comment "`instantiate-existential' at (0 1 0 0 0 1)")
	      (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
                                                                 
						("n"))
	      (simplify-antecedent "with(p:prop,not(p));")))
	  (block 
	    (script-comment "`induction' at (0 1 0 0 0 0 0)")
	    (apply-macete-with-minor-premises ultrametric-distance-bound-lemma)
	    (block 
	      (script-comment "`apply-macete-with-minor-premises' at (0)")
	      (instantiate-existential ("x(t)"))
	      (apply-macete-with-minor-premises tr%ultrametric-symmetry-of-distance)
	      (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
                                                                 
						("t"))
	      simplify)
	    (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
					      ("t")))))
      (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));" ("p"))
      (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));" ("q")))

    )))
