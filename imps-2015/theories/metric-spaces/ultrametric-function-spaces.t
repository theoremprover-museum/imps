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

(herald ultrametric-function-spaces)

(def-language functions-on-a-graded-set
  (embedded-languages h-o-real-arithmetic)
  (base-types  uu values)
  (constants (degree "[uu, nn]")))

(def-theory functions-on-a-graded-set
  (component-theories h-o-real-arithmetic)
  (language functions-on-a-graded-set)
  (axioms
   (totality-of-degree
    "total_q{degree, [uu->nn]}" d-r-convergence)))

(def-theorem ()
  "forsome(x:[uu,values],total_q{x,[uu,values]})"
  (theory functions-on-a-graded-set)
  (proof
   (
    
    (cut-with-single-formula "forsome(x:values, #(x,values))")
    (antecedent-inference "with(p:prop,p);")
    (instantiate-existential ("lambda(v:uu, x)"))
    simplify-insistently
    )))

(def-atomic-sort total%fns
  "lambda(f:[uu->values], total_q{f,[uu->values]})"
  (theory functions-on-a-graded-set))

(def-constant fn%approx
  "lambda(f,g:total%fns, n:zz, forall(k:uu, degree(k)<=n implies f(k)=g(k)))"
  (theory functions-on-a-graded-set))

(def-theorem fn%approx-separation
  "forall(x,y:total%fns,
      not(x=y) implies forsome(n:zz,not(fn%approx(x,y,n))))"
  (theory functions-on-a-graded-set)
  lemma
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally fn%approx)
    (contrapose "with(p:prop,p);")
    extensionality
    direct-inference
    (contrapose "with(p:prop,p);")
    (instantiate-existential ("degree(x_0)"))
    (instantiate-existential ("x_0"))
    simplify

    )))

(def-theorem fn%approx-monotonicity
  "forall(m:zz,x,y:total%fns,
     forsome(n:zz,fn%approx(x,y,n) and m<=n)
       implies 
     fn%approx(x,y,m))"
  (theory functions-on-a-graded-set)
  lemma
  (proof
   (
    
    (unfold-single-defined-constant-globally fn%approx)
    direct-and-antecedent-inference-strategy
    simplify

    )))


(def-theorem fn%approx-existence
  "forall(x,y:total%fns,forsome(m:zz,fn%approx(x,y,m)))"
  (theory functions-on-a-graded-set)
  lemma
  (proof
   (


    (unfold-single-defined-constant-globally fn%approx)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("-1"))
    (contrapose "with(p:prop,p);")
    simplify

    )))


(def-theorem fn%approx-reflexivity 
  "forall(m:zz,x:total%fns,fn%approx(x,x,m))"
  (theory functions-on-a-graded-set)
  lemma
  (proof
   (
    
    (unfold-single-defined-constant-globally fn%approx)
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(x,total%fns)")
    (incorporate-antecedent "with(x:total%fns,#(x,total%fns));")
    (apply-macete-with-minor-premises total%fns-defining-axiom_functions-on-a-graded-set)
    simplify
    )))
  
(def-theorem fn%approx-symmetry
  "forall(m:zz,x,y:total%fns,
    fn%approx(x,y,m) implies fn%approx(y,x,m))"
  (theory functions-on-a-graded-set)                                     
  lemma
  (proof   
   (     

    (unfold-single-defined-constant-globally fn%approx)
    (force-substitution "y(k)=x(k)" "x(k)=y(k)" (0))
    simplify
    )))


(def-theorem fn%approx-transitivity
  "forall(m:zz,x,z:total%fns,
  forsome(y:total%fns,
    fn%approx(x,y,m) and fn%approx(y,z,m))
   implies 
  fn%approx(x,z,m))"
  (theory functions-on-a-graded-set) 
  (proof
   (

    (unfold-single-defined-constant-globally fn%approx)
    direct-and-antecedent-inference-strategy
    simplify
    )))

(include-files
 (files (imps theories/metric-spaces/tree-like-spaces)))

(def-translation degree-equivalence-to-functions-on-a-graded-set
  force-under-quick-load
  (source degree-equivalence)
  (target functions-on-a-graded-set)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (pp "total%fns"))
  (constant-pairs (approx fn%approx))
  (theory-interpretation-check using-simplification))

;Under this translation, some constants such as the predicate "cauchy"
;get translated into long-winded expressions, simply because  the 
;theory functions-on-a-graded-set has not yet been viewed as a metric space.
;We now do this:

(def-renamer de-to-fgs-renamer
  (pairs
   (sep%deg fn%deg)
   (sep%dist fn%dist)))


(def-transported-symbols (sep%deg sep%dist) 
  (translation degree-equivalence-to-functions-on-a-graded-set)
  (renamer de-to-fgs-renamer)
  )
  
(def-theorem fn%dist-triangle-inequality
  sep%dist-is-a-metric
  (theory functions-on-a-graded-set)
  (translation degree-equivalence-to-functions-on-a-graded-set)
  (proof existing-theorem))

(def-theorem fn%dist-symmetric
  sep%dist-symmetric
  (theory functions-on-a-graded-set)
  (translation degree-equivalence-to-functions-on-a-graded-set)
  (proof existing-theorem))

(def-theorem fn%dist-non-negative
  sep%dist-non-negative
  (theory functions-on-a-graded-set)
  (translation degree-equivalence-to-functions-on-a-graded-set)
  (proof existing-theorem))  
  
(def-theorem  fn%dist-reflexive
  rev%sep%dist-reflexive
  (theory functions-on-a-graded-set)
  (translation degree-equivalence-to-functions-on-a-graded-set)
  (proof existing-theorem))

(def-theory-ensemble-instances metric-spaces 
  force-under-quick-load
  (target-theories functions-on-a-graded-set functions-on-a-graded-set)
  (permutations  (0) (0 1))
  (theory-interpretation-check using-simplification)
  (sorts (pp total%fns total%fns))
  (constants (dist fn%dist fn%dist)))

(def-theory-ensemble-overloadings metric-spaces (1 2))

;;We have to evaluate this again to update translation constant a-list, in particular
;;to have the constants "cauchy" and "lim" translated to something useful:

(def-translation degree-equivalence-to-functions-on-a-graded-set
  force-under-quick-load
  (source degree-equivalence)
  (target functions-on-a-graded-set)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (pp "total%fns"))
  (constant-pairs (approx fn%approx))
  (theory-interpretation-check using-simplification))

(def-constant discrete%lim
  "lambda(s:[zz,total%fns], 
    lambda(u:uu,
     s(set%min(indic{n:zz,0<=n and forall(p,q:zz, n<=p and n<=q implies fn%approx(s(p),s(q),degree(u)))}))(u)))"
  (theory functions-on-a-graded-set))

(def-theorem definedness-of-discrete%lim
  "forall(s:[zz,total%fns],  cauchy(s) implies #(discrete%lim(s), total%fns))"
  (theory functions-on-a-graded-set)
  (proof
   (

    (apply-macete-with-minor-premises tr%strong-cauchy-characterization-for-sep%dist)
    (apply-macete-with-minor-premises total%fns-defining-axiom_functions-on-a-graded-set)
    insistent-direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally discrete%lim)
    (cut-with-single-formula "forsome(k:zz, set%min(indic{n:zz,  0<=n and forall(p,q:zz,
                             n<=p and n<=q 
                              implies 
                             fn%approx(s(p),
                                       s(q),
                                       degree(x_0)))})=k)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(k:zz,p));")
      (backchain "with(k,z:zz,z=k);")
      (incorporate-antecedent "with(k,z:zz,z=k);")
      (apply-macete-with-minor-premises iota-free-characterization-of-set%min)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula "#(s(k),total%fns)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(incorporate-antecedent "with(f:total%fns,#(f,total%fns));")
	(apply-macete-with-minor-premises total%fns-defining-axiom_functions-on-a-graded-set)
	simplify
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  (instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
					    ("k" "k"))
	  (simplify-antecedent "with(p:prop,not(p));")))
      simplify)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (instantiate-existential ("set%min(indic{n:zz,  0<=n and forall(p,q:zz, 
                           n<=p and n<=q
                            implies 
                           fn%approx(s(p),
                                     s(q),
                                     degree(x_0)))})"))
      simplify
      (apply-macete-with-minor-premises definedness-of-set%min)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(instantiate-universal-antecedent "with(p:prop,p);"
					  ("degree(x_0)"))
	(instantiate-existential ("max(n,0)"))
	simplify
	(block 
	  (script-comment "`instantiate-existential' at (0 1 0 0)")
	  (instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
					    ("p" "q"))
	  (block 
	    (script-comment "`instantiate-universal-antecedent' at (0 0 0 0)")
	    (cut-with-single-formula "n<=max(n,0)")
	    (simplify-antecedent "with(p:prop,not(p));")
	    (block 
	      (script-comment "`cut-with-single-formula' at (1 (2 . 1))")
	      (cut-with-single-formula "n<=max(n,0)")
	      simplify))
	  (block 
	    (script-comment "`instantiate-universal-antecedent' at (0 0 0 1)")
	    (cut-with-single-formula "n<=max(n,0)")
	    (simplify-antecedent "with(p:prop,not(p));")
	    simplify)))
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0)")
	(instantiate-existential ("[-1]"))
	(simplify-antecedent "with(j:zz,j<=[-1]);")))
    (unfold-single-defined-constant (0) discrete%lim)


    )))

(def-theorem discrete%lim-eventually-constant-property
  "forall(s:[zz,total%fns], #(discrete%lim(s), total%fns) implies
	    forall(u:uu, 
		     forsome(m:zz, forall(p:zz, m<=p implies s(p)(u)=discrete%lim(s)(u)))))"
  (theory functions-on-a-graded-set)
  (usages transportable-macete)
  (proof
   (


    (apply-macete-with-minor-premises
     total%fns-defining-axiom_functions-on-a-graded-set)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      direct-and-antecedent-inference-strategy
      (instantiate-existential ("set%min(indic{n:zz,0<=n and forall(p,q:zz, n<=p and n<=q implies fn%approx(s(p),s(q),degree(u)))})"))
      (move-to-ancestor 3)
      (move-to-descendent (1 0))
      (block 
	(script-comment "`instantiate-existential' at (1 0)")
	(incorporate-antecedent "with(p:prop,p);")
	(unfold-single-defined-constant (0) discrete%lim)
	simplify-insistently)
      (block 
	(script-comment "`instantiate-existential' at (0 0 0)")
	(cut-with-single-formula "forsome(k:zz, set%min(indic{n:zz,  0<=n
								and 
								forall(p,q:zz,
									 n<=p and n<=q
									 implies 
									 fn%approx(s(p),
										    s(q),
										    degree(u)))})=k)")
	(move-to-sibling 1)
	(instantiate-existential ("set%min(indic{n:zz,  0<=n
						   and 
						   forall(p,q:zz,
							    n<=p and n<=q
							    implies 
							    fn%approx(s(p),
								       s(q),
								       degree(u)))})"))
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (incorporate-antecedent "with(p_$0,z:zz,z<=p_$0);")
	  (unfold-single-defined-constant (0) discrete%lim)
	  (antecedent-inference "with(p:prop,forsome(k:zz,p));")
	  (backchain "with(k,z:zz,z=k);")
	  (backchain "with(k,z:zz,z=k);")
	  (incorporate-antecedent "with(k,z:zz,z=k);")
	  (apply-macete-with-minor-premises iota-free-characterization-of-set%min)
	  simplify-insistently
	  direct-and-antecedent-inference-strategy
	  (instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
					     ("p_$0" "k"))
	  (simplify-antecedent "with(p:prop,not(p));")
	  (block 
	    (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	    (cut-with-single-formula "#(s(p_$0),total%fns) and #(s(k),total%fns)")
	    (move-to-sibling 1)
	    simplify
	    (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	      (incorporate-antecedent "with(p:prop,p and p);")
	      (apply-macete-with-minor-premises total%fns-defining-axiom_functions-on-a-graded-set)
	      direct-inference
	      (incorporate-antecedent "with(n:nn,f:total%fns,fn%approx(f,f,n));")
	      (unfold-single-defined-constant (0)
                                                                 
					      fn%approx)
	      direct-and-antecedent-inference-strategy
	      (instantiate-universal-antecedent "with(p:prop,forall(k_$0:uu,p implies p));"
                                                                 
						 ("u"))
	      (simplify-antecedent "with(p:prop,not(p));"))))))
    (unfold-single-defined-constant (0) discrete%lim))))


(def-theorem cauchy-implies-discrete%lim-is-lim
  "forall(s:[zz,total%fns],  
        cauchy(s) 
           implies
        lim(s)=discrete%lim(s))"
  lemma
  (theory functions-on-a-graded-set)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(discrete%lim(s),total%fns)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises definedness-of-discrete%lim)
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (cut-with-single-formula "forsome(x:total%fns, discrete%lim(s)=x)")
     (move-to-sibling 1)
     (instantiate-existential ("discrete%lim(s)"))
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(x:total%fns,p));")
      (cut-with-single-formula "forall(u:uu, 
forsome(m:zz, forall(p:zz, m<=p implies s(p)(u)=discrete%lim(s)(u))))")
      (move-to-sibling 1)
      (apply-macete-with-minor-premises discrete%lim-eventually-constant-property)
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (backchain "with(x:total%fns,f:[uu,values],f=x);")
       (apply-macete-with-minor-premises tr%lim-characterization-for-sep%dist)
       (incorporate-antecedent "with(p:prop,forall(u:uu,p));")
       (backchain "with(x:total%fns,f:[uu,values],f=x);")
       direct-and-antecedent-inference-strategy
       (incorporate-antecedent "with(s:[zz,total%fns],cauchy(s));")
       (apply-macete-with-minor-premises tr%strong-cauchy-characterization-for-sep%dist)
       direct-and-antecedent-inference-strategy
       (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
					 ("m_$0"))
       (instantiate-existential ("n"))
       (cut-with-single-formula "#(s(p_$0), total%fns)")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(unfold-single-defined-constant (0) fn%approx)
	direct-and-antecedent-inference-strategy
	(instantiate-universal-antecedent "with(p:prop,forall(u:uu,p));"
					  ("k"))
	(instantiate-universal-antecedent "with(p:prop,forall(p:zz,with(p:prop,p)));"
					  ("max(m,n)"))
	(simplify-antecedent "with(p:prop,not(p));")
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	 (instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
                                                                 
					   ("p_$0" "max(m,n)"))
	 (simplify-antecedent "with(p:prop,not(p));")
	 (block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	  (backchain-backwards "with(v:values,v=v);")
	  (cut-with-single-formula "#(s(p_$0), total%fns) and #(s(max(m,n)), total%fns)")
	  (move-to-sibling 1)
	  simplify
	  (block 
	   (script-comment "`cut-with-single-formula' at (0)")
	   (incorporate-antecedent "with(m_$0:zz,f:total%fns,fn%approx(f,f,m_$0));")
	   (unfold-single-defined-constant (0)
                                                                 
					   fn%approx)
	   simplify))))
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	simplify
	(instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
					  ("p_$0" "p_$0"))))))

    )))

(def-theorem completeness-of-total%fns
  "complete"
  (theory  functions-on-a-graded-set)
  (usages transportable-macete)
  (proof
   (

    (unfold-single-defined-constant (0) complete)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lim(s)=discrete%lim(s)")
    (apply-macete-with-minor-premises cauchy-implies-discrete%lim-is-lim)
    simplify
    (cut-with-single-formula "#(discrete%lim(s),total%fns)")
    (apply-macete-with-minor-premises definedness-of-discrete%lim)

    )))



(def-theorem fn%dist-is-bounded
  "forall(x,y:total%fns,  fn%dist(x,y)<=1)"
  (theory functions-on-a-graded-set)
  (usages transportable-macete)
  (proof
   (



    (force-substitution "1" "2^(- 0)" (0))
    (block 
     (script-comment "`force-substitution' at (0)")
     (apply-macete-with-minor-premises tr%small-distance-characterization)
     (unfold-single-defined-constant-globally fn%approx)
     simplify)
    simplify

    )))

(def-theorem fn%dist-small-distance-chracterization
  "forall(x,y:total%fns, n:zz, 
     fn%dist(x,y)<=2^(-n) iff forall(u:uu, degree(u)<=n-1 implies x(u)=y(u)))"
  (theory functions-on-a-graded-set)
  (usages transportable-macete)
  (proof
   (


    (apply-macete-with-minor-premises tr%small-distance-characterization)
    (unfold-single-defined-constant-globally fn%approx)


    )))