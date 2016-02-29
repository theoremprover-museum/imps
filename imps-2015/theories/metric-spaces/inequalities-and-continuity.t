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


(herald inequalities-and-continuity)

(include-files
 (files ;; (imps theories/metric-spaces/metric-space-triples)
	(imps theories/metric-spaces/examples-of-continuity)
	(imps theories/metric-spaces/metric-space-pairs-supplements)
	(imps theories/metric-spaces/mappings-from-an-interval)))


(def-theory-ensemble-instances
  metric-spaces 
  (target-theories fixed-interval-theory h-o-real-arithmetic)
  force-under-quick-load
  (permutations (0) (0 1))
  (theory-interpretation-check using-simplification)
  (sorts (pp ii rr))
  (constants (dist "lambda(x,y:ii, abs(x-y))" "lambda(x,y:rr, abs(x-y))"))
  (special-renamings
   (continuous%at%point ii%continuous%at%point)
   (continuous ii%continuous)))

;;This is added to enrich translations:

(def-theory-ensemble-instances
  metric-spaces 
  (target-theories fixed-interval-theory)
  force-under-quick-load
  (permutations (0))
  (theory-interpretation-check using-simplification)
  (sorts (pp ii))
  (constants (dist "lambda(x,y:ii, abs(x-y))")))

(def-theory-ensemble-overloadings metric-spaces (1 2))

(include-files
 
 (files 

  (imps theories/partial-orders/convergence-and-order)
  (imps theories/partial-orders/induction-in-cpos)))


(def-theorem sup-property-of-continuity
  "forall(f:[ii,rr],x,a:rr,s:sets[ii],
     total_q{f,[ii,rr]}
      and
     ii%continuous(f)
      and
     #(sup(s),ii)
      and
     forall(x:rr,x in s implies f(x)<=a)
      implies 
     f(sup(s))<=a)"
  (theory fixed-interval-theory)
  (proof
   (


    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    (unfold-single-defined-constant (0) ii%continuous%at%point)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(x:ii,forall(eps:rr,p)));"
				      ("sup(s)"))
    (contrapose "with(p:prop,
  forall(eps:rr,0<eps implies forsome(delta:rr,p)));")
    (instantiate-existential ("(f(sup(s))-a)/2"))
    simplify
    (cut-with-single-formula "forsome(x:ii, x in s and sup(s)-delta_$0<x)")
    (antecedent-inference "with(p:prop,forsome(x:ii,p));")
    (instantiate-existential ("x"))
    (apply-macete-with-minor-premises absolute-value-non-negative)
    simplify
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-inference
    (instantiate-existential ("x"))
    simplify
    (cut-with-single-formula "f(x)<=a")
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises absolute-value-non-negative)
    simplify
    (cut-with-single-formula "forsome(x:rr,x in s and sup(s)-delta_$0<x)")
    (antecedent-inference "with(p:prop,forsome(x:rr,p));")
    (instantiate-existential ("with(x:rr, x)"))
    (apply-macete-with-minor-premises sup-minus-epsilon-corollary)
    direct-and-antecedent-inference-strategy
    )))



(def-theorem subset-of-interval-characterization
  "forall(s:sets[rr],a,b:ii,
     forall(x:rr,x in s implies a<=x and x<=b)
      implies 
     #(s,sets[ii]))"
  (theory fixed-interval-theory)
  (proof
   (

    direct-and-antecedent-inference-strategy
    sort-definedness
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("b" "a"))
    simplify
    simplify
    )))


(def-theorem inf-lemma
  "forall(x,y,z:rr, forall(y_0:rr, y<y_0 implies x<=y_0*z) implies x<=y*z)"
  lemma
  (theory h-o-real-arithmetic)
  (proof

   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "z<=0 or 0<z")
    (block
     (script-comment "node added by `cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,p or p);")
     (block
      (script-comment "node added by `antecedent-inference' at (0)")
      (cut-with-single-formula "x<=(y+1)*z and (y+1)*z<=y*z")
      simplify
      (block
       (script-comment "node added by `cut-with-single-formula' at (1)")
       direct-and-antecedent-inference-strategy
       (block
	(script-comment "node added by `direct-and-antecedent-inference-strategy' at (0)")
	(backchain "with(p:prop,forall(y_0:rr,p));")
	simplify)
       simplify))
     (block
      (script-comment "node added by `antecedent-inference' at (1)")
      (cut-with-single-formula "y<x/z or x/z<=y")
      (block
       (script-comment "node added by `cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,p or p);")
       (block
	(script-comment "node added by `antecedent-inference' at (0)")
	(instantiate-universal-antecedent "with(p:prop,forall(y_0:rr,p));"
					  ("[1/2]*(y+x/z)"))
	(block
	 (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0)")
	 (contrapose "with(p:prop,not(p));")
	 simplify)
	(block
	 (script-comment "node added by `instantiate-universal-antecedent' at (0 0 1)")
	 (incorporate-antecedent "with(r,x:rr,x<=r);")
	 (apply-macete-with-minor-premises fractional-expression-manipulation)
	 simplify))
       (block
	(script-comment "node added by `antecedent-inference' at (1)")
	(incorporate-antecedent "with(y,r:rr,r<=y);")
	(apply-macete-with-minor-premises fractional-expression-manipulation)))
      simplify))
    simplify
    )))

(def-constant ii%locally%lipschitz%bound
  "lambda(phi:[ii,pp], r:rr, 0<r and
         forall(x,z:ii, x<z implies forsome(y:ii, x<y and y<=z and dist(phi(y),phi(x))<=r*(y-x))))"
  (theory mappings-from-an-interval))


(def-theorem lipschitz-on-interval-characterization
  "forall(phi:[ii,pp], r:rr, 0<r and forall(x,y:ii, y<=x 
                               implies 
                             dist(phi(x),phi(y))<=r*(x-y)) 
                              implies
                             lipschitz%bound(phi,r))"
  lemma
  (proof

   (

    (while (progresses? unfold-directly-defined-constants) (skip))
    direct-and-antecedent-inference-strategy
    (case-split ("0<=x_$0-y_$0"))
    (let-script instantiate-antecedents 2
		(
		 (instantiate-universal-antecedent
		  "with(p:prop,forall(x,y:ii,p));"
		  ($1 $2))
		 (simplify-antecedent "with(p:prop,not(p));")
		 simplify))
    ($instantiate-antecedents "x_$0" "y_$0")
    ($instantiate-antecedents "y_$0" "x_$0")
    ))
  (theory mappings-from-an-interval))

(def-theorem continuity-of-dist-expression
  "forall(phi:[ii,pp],y:ii,a,b:rr,
        total_q{phi,[ii,pp]} 
         and  
        continuous(phi) 
         implies 
        continuous(lambda(z:ii,a+b*z+dist(phi(z),phi(y)))))"
  (theory mappings-from-an-interval)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(phi:[ii,pp],continuous(phi));")
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    (move-to-sibling 1)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises polynomial-continuity-macete)
    (incorporate-antecedent "with(phi:[ii,pp],forall(x:ii,continuous%at%point(phi,x)));")
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("eps"))
    (instantiate-universal-antecedent "with(p:prop,forall(x:ii,forall(eps:rr,p)));"
				      ("x"))
    (instantiate-universal-antecedent "with(p:pp,r:rr,
  forall(eps:rr,
    0<eps
     implies 
    forsome(delta:rr,
      0<delta
       and 
      forall(y:ii,abs(r)<=delta implies dist(p,p)<=eps))));"
				      ("eps_$0"))
    (instantiate-existential ("delta"))
    (cut-with-single-formula
     "abs(dist(phi(x),phi(y))-dist(phi(y_$0),phi(y)))<=dist(phi(x),phi(y_$0))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises dist-continuity-lemma)
    (instantiate-universal-antecedent "with(eps_$0,delta,r:rr,
  forall(y:ii,r<=delta implies r<=eps_$0));"
				      ("y_$0"))
    simplify

    )))


(def-theorem locally-lipschitz-implies-lipschitz
  "forall(phi:[ii,pp],r:rr,
     total_q{phi,[ii,pp]}
      and 
     continuous(phi)
      and 
     ii%locally%lipschitz%bound(phi,r)
      implies 
     lipschitz%bound(phi,r))"
  lemma
  (proof

   (



    (apply-macete-with-minor-premises lipschitz-on-interval-characterization)
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    (unfold-single-defined-constant (0) ii%locally%lipschitz%bound)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(z:rr, y<=z and z<=x implies lambda(x:rr,dist(phi(x),phi(y))-r*(x-y)<=0)(z))")
    (block
     (script-comment "node added by `cut-with-single-formula' at (0)")
     (instantiate-universal-antecedent "with(p:prop,forall(z:rr,p implies p));"
				       ("x"))
     (simplify-antecedent "with(p:prop,not(p));")
     simplify)
    (block
     (script-comment "node added by `cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises tr%induction-principle-for-cpos)
     beta-reduce-repeatedly
     direct-and-antecedent-inference-strategy
     simplify
     (move-to-ancestor 2)
     (block
      (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1 0 0)")
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula "#(sup(t_$0)) and y<=sup(t_$0) and sup(t_$0)<=x ")
      (move-to-sibling 1)
      (block
       (script-comment "node added by `cut-with-single-formula' at (1)")
       direct-and-antecedent-inference-strategy
       (block
	(script-comment "node added by `direct-and-antecedent-inference-strategy' at (0)")
	(apply-macete-with-minor-premises tr%prec%sup-defined)
	direct-and-antecedent-inference-strategy
	auto-instantiate-existential
	(block
	 (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1 0)")
	 (unfold-single-defined-constant (0)
                                                                 
					 majorizes)
	 (instantiate-existential ("x"))
	 simplify))
       (block
	(script-comment "node added by `direct-and-antecedent-inference-strategy' at (1)")
	(apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
	direct-and-antecedent-inference-strategy
	(instantiate-existential ("y"))
	simplify)
       (block
	(script-comment "node added by `direct-and-antecedent-inference-strategy' at (2)")
	(apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
	direct-and-antecedent-inference-strategy
	(unfold-single-defined-constant (0) majorizes)
	direct-and-antecedent-inference-strategy
	simplify))
      (block
       (script-comment "node added by `cut-with-single-formula' at (0)")
       (cut-with-single-formula "lambda(z:ii,r*y+([-1]*r)*z+dist(phi(z),phi(y)))(sup(t_$0))<=0")
       simplify
       (block
	(script-comment "node added by `cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises sup-property-of-continuity)
	(block
	 (script-comment "node added by `apply-macete-with-minor-premises' at (0)")
	 direct-and-antecedent-inference-strategy
	 simplify-insistently
	 (block
	  (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1)")
	  (apply-macete-with-minor-premises continuity-of-dist-expression)
	  direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity))
	 (block
	  (script-comment "node added by `direct-and-antecedent-inference-strategy' at (2)")
	  (apply-macete-with-minor-premises interval-characterization)
	  (instantiate-existential ("x" "y")))
	 (block
	  (script-comment "node added by `direct-and-antecedent-inference-strategy' at (3 0 0)")
	  beta-reduce-with-minor-premises
	  (move-to-sibling 1)
	  (block
	   (script-comment "node added by `beta-reduce-with-minor-premises' at (1)")
	   (apply-macete-with-minor-premises interval-characterization)
	   (instantiate-existential ("x" "y"))
	   simplify
	   simplify)
	  simplify))
	(block
	 (script-comment "node added by `apply-macete-with-minor-premises' at (1)")
	 (apply-macete-with-minor-premises subset-of-interval-characterization)
	 (instantiate-existential ("x" "y"))
	 simplify
	 simplify))))
     (block
      (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1 1 0
0 0)")
      (instantiate-universal-antecedent "with(p:prop,forall(x,z:ii,p));"
					("y_$1" "z_$0"))
      (simplify-antecedent "with(z_$0,y_$1:rr,not(y_$1<z_$0));")
      (block
       (script-comment "node added by `instantiate-universal-antecedent' at (0 0 1 0 0)")
       (instantiate-existential ("y_$0"))
       (block
	(script-comment "node added by `instantiate-existential' at (0 0)")
	(cut-with-single-formula "dist(phi(y_$0),phi(y))<=dist(phi(y_$0),phi(y_$1))+dist(phi(y_$1),phi(y))")
	(move-to-sibling 1)
	(apply-macete-with-minor-premises triangle-inequality-for-distance)
	simplify)
       simplify
       simplify)
      (block
       (script-comment "node added by `instantiate-universal-antecedent' at (1 2)")
       (apply-macete-with-minor-premises interval-characterization)
       (instantiate-existential ("x" "y"))
       simplify)))

    ))

  (theory mappings-from-an-interval))


(def-theorem locally-lipschitz-implies-lipschitz-plus
  "forall(phi:[ii,pp], r_0:rr, 0<r_0 and total_q{phi,[ii,pp]} and continuous(phi) and 
           forall(r:rr,r_0<r implies ii%locally%lipschitz%bound(phi,r))
             implies 
          lipschitz%bound(phi,r_0))"


  (theory mappings-from-an-interval)
  (usages transportable-macete)
  (proof
   
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(r:rr,r_0<r implies lipschitz%bound(phi,r))")
    (incorporate-antecedent "with(phi:[ii,pp],r_0:rr,
  forall(r:rr,r_0<r implies lipschitz%bound(phi,r)));")
    unfold-defined-constants
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises inf-lemma)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, forall(r:rr, r_0<r implies 0<r and p))")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises locally-lipschitz-implies-lipschitz)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,  forall(r:rr, r_0<r implies p))")

    )))



