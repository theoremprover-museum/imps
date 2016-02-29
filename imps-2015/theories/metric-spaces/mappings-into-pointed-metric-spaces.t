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


(herald mappings-into-pointed-metric-spaces)

(include-files
 (files (imps theories/metric-spaces/pointed-metric-spaces)))


(def-theory-ensemble-instances
  metric-spaces
  force-under-quick-load
  (permutations (0 1))
  (sorts (pp pp pp))
  (constants (dist dist dist))
  (target-theories metric-spaces metric-spaces))

(def-theory-ensemble-instances
  metric-spaces
  force-under-quick-load
  (permutations (0))
  (sorts (pp bfun))
  (constants (dist bfun%dist))
  (target-theories mappings-into-a-pointed-metric-space)
  (special-renamings
   (ball bfun%ball)
   (complete bfun%complete)
   (lipschitz%bound%on bfun%lipschitz%bound%on)
   (lipschitz%bound bfun%lipschitz%bound)))

(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-theorem bfun-values-defined-lemma
  "forall(x:ind_1,g:bfun, #(g(x)))"
  (usages rewrite transportable-macete)

  (proof

   (

   (instantiate-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space ("g"))
   simplify
   simplify
    )

   )


  (theory mappings-into-a-pointed-metric-space))

(def-theorem bfun-ball-membership-lemma
  "forall(f:[ind_1,pp],g:bfun, r:rr, f in ball(g,r) iff forall(x:ind_1, f(x) in ball(g(x),r)))"
    
  (proof

   (

    direct-inference
    (force-substitution "f in ball(g,r) " "forsome(h:bfun, h=f and h in ball(g,r))" (0))
    (apply-macete-with-minor-premises ball-membership-condition)
    (apply-macete-with-minor-premises tr%ball-membership-condition)
    (force-substitution "bfun%dist(g,h)<=r" "forall(x:ind_1,dist(g(x),h(x))<=r)" (0))
    direct-and-antecedent-inference-strategy
    (backchain-backwards "with(f:[ind_1,pp],h:bfun,h=f);")
    simplify
    (instantiate-existential ("f"))
    (apply-macete-with-minor-premises bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    insistent-direct-inference
    insistent-direct-inference
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (weaken (1))
    (apply-macete-with-minor-premises tr%non-empty-range)
    (instantiate-existential ("x"))
    (unfold-single-defined-constant (0) rad%dist)
    simplify
    (weaken (0 1))
    (unfold-single-defined-constant (0) rad%dist)
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    (instantiate-existential ("r+sup(ran{rad%dist oo g})"))
    (apply-macete-with-minor-premises triangle-inequality-alternate-form)
    (instantiate-existential ("g(n_$0)"))
    (cut-with-single-formula "dist(a_0,g(n_$0))<=sup(ran{rad%dist oo g})")
    simplify
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("dist(g(n_$0),a_0)"))
    (unfold-single-defined-constant (0) rad%dist)
    simplify
    (instantiate-existential ("n_$0"))
    simplify
    simplify
    (weaken (0 1 2 3))
    (cut-with-single-formula "#(g,bfun)")
    (incorporate-antecedent "with(g:bfun,#(g,bfun));")
    (apply-macete-with-minor-premises bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    direct-and-antecedent-inference-strategy
    (weaken (0 1))
    (weaken (0))
    (weaken (0))
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "dist(g(x),h(x))<=bfun%dist(g,h)")
    simplify
    (apply-macete-with-minor-premises bounded-bfun%dist)
    (unfold-single-defined-constant (0) bfun%dist)
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    (instantiate-existential ("x"))
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    (instantiate-existential ("r"))
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("f"))
    (backchain-backwards "with(f:[ind_1,pp],h:bfun,h=f);")


    )


   )




  (theory mappings-into-a-pointed-metric-space))

(def-theorem bfun-ball-closure
  "forall(f:bfun,r:rr, s:[zz,bfun],0<r and 
    forall(n:zz, #(s(n)) implies s(n) in ball(f,r)) and 
    forall(x:ind_1, #(lim(lambda(n:zz, s(n)(x))))) 
         implies
     lambda(x:ind_1, lim(lambda(n:zz, s(n)(x)))) in ball(f,r))"


  (proof

   (

    (apply-macete-with-minor-premises bfun-ball-membership-lemma)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises closed-balls-are-closed)
    direct-and-antecedent-inference-strategy
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(x:ind_1,x_$1:zz,s:[zz,bfun],x_$0:pp,x_$0=s(x_$1)(x));")
    (backchain "with(r:rr,f:bfun,s:[zz,bfun],
  forall(n:zz,
    #(s(n)) implies 
    forall(x:ind_1,s(n)(x) in ball(f(x),r))));")
    (instantiate-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space ("f"))
    simplify
    simplify


    )
   )


  (theory mappings-into-a-pointed-metric-space))

(def-theorem bfun-ball-closure-corollary
  "forall(f:bfun,r:rr, s:[zz,bfun],0<r and 
            forsome(m:zz, forall(n:zz, m<=n implies s(n) in ball(f,r))) and 
            forall(x:ind_1, #(lim(lambda(n:zz, s(n)(x)))))
               implies
             lambda(x:ind_1, lim(lambda(n:zz, s(n)(x)))) in ball(f,r))"

  (proof

   (
    direct-and-antecedent-inference-strategy
    (force-substitution "lim(lambda(n:zz,s(n)(x)))" "lim(lambda(n:zz,lambda(k:zz, if(m<=k,s(k),?bfun))(n)(x)))" (0))
    (apply-macete-with-minor-premises bfun-ball-closure)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify
    (cut-with-single-formula "lim(lambda(n:zz,if(m<=n, s(n), ?bfun)(x)))=lim(lambda(n:zz,s(n)(x)))")
    (weaken (0))
    (apply-macete-with-minor-premises limit-depends-on-tail)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("m"))
    simplify
    (weaken (3))
    (cut-with-single-formula "total_q{s(P_$1),[ind_1,pp]}")
    (instantiate-universal-antecedent "with(s:[zz,bfun],r:rr,f:bfun,m:zz,forall(n:zz,m<=n implies s(n) in ball(f,r)));" ("p_$1"))
    (weaken ( 1 2))
    (instantiate-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space ("s(p_$1)"))
    beta-reduce-repeatedly
    )

   )
  
  (theory mappings-into-a-pointed-metric-space))



(def-theorem uniform-cauchy-implies-ptwise-cauchy
  "forall(s:[zz,bfun], cauchy(s) implies forall(x:ind_1, cauchy(lambda(n:zz, s(n)(x)))))"

  (proof

   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent "with(s:[zz,bfun],
  forall(eps:rr,
    0<eps
     implies 
    forsome(p:zz,
      forall(q:zz,p<q implies bfun%dist(s(p),s(q))<=eps))));")
    (instantiate-existential ("p"))
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("bfun%dist(s(p),s(q_$0))"))
    (apply-macete-with-minor-premises bounded-bfun%dist)
    (instantiate-universal-antecedent "with(eps_$0:rr,s:[zz,bfun],p:zz,
  forall(q:zz,p<q implies bfun%dist(s(p),s(q))<=eps_$0));" ("q_$0"))
    (instantiate-universal-antecedent "with(eps_$0:rr,s:[zz,bfun],p:zz,
  forall(q:zz,p<q implies bfun%dist(s(p),s(q))<=eps_$0));" ("q_$0"))
    (backchain "with(eps_$0:rr,s:[zz,bfun],p:zz,
  forall(q:zz,p<q implies bfun%dist(s(p),s(q))<=eps_$0));")
    direct-inference
    direct-inference
    )
   )
  (theory mappings-into-a-pointed-metric-space))

(def-theorem cauchy-ptwise-converge-implies-uniform-convergence
  "forall(s:[zz,bfun],cauchy(s) and forall(x:ind_1, #(lim(lambda(n:zz, s(n)(x)))))
            implies
            lim(s)=lambda(x:ind_1,(lim(lambda(n:zz, s(n)(x))))))"

  (proof

   (


    (apply-macete-with-minor-premises tr%cauchy-double-index-characterization)
    (force-substitution "bfun%dist(s(p),s(q))<=eps" "s(q) in ball(s(p),eps)" (0))
    (block 
     (script-comment "node added by `force-substitution' at (0)")
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "forsome(h:bfun, h = lambda(x:ind_1,lim(lambda(n:zz,s(n)(x)))))")
     (block 
      (script-comment "node added by `cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(h:bfun,p));")
      (backchain-backwards "with(f:[ind_1,pp],h:bfun,h=f);")
      (apply-macete-with-minor-premises tr%characterization-of-limit)
      (force-substitution
       "bfun%dist(h,s(p))<=eps"
       "h in ball(s(p),eps)"
			  (0))
      (block 
       (script-comment "node added by `force-substitution' at (0)")
       direct-and-antecedent-inference-strategy
       (auto-instantiate-universal-antecedent "with(p:prop,  forall(eps:rr, 0<eps implies p))")
       (instantiate-existential ("n"))
       (backchain "with(f:[ind_1,pp],h:bfun,h=f);")
       (apply-macete-with-minor-premises bfun-ball-closure-corollary)
       (block 
	(script-comment "node added by `apply-macete-with-minor-premises' at (0)")
	direct-and-antecedent-inference-strategy
	(instantiate-existential ("n"))
	(backchain "with(p:prop,forall(p,q:zz,with(p:prop,p)));")
	simplify)
       (instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
					 ("p" "p")))
      (block 
       (script-comment "node added by `force-substitution' at (1)")
       (apply-macete-with-minor-premises tr%ball-membership-condition)
       direct-inference
       (apply-macete-with-minor-premises tr%symmetry-of-distance)))
     (block 
      (script-comment "node added by `cut-with-single-formula' at (1)")
      (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,p));"
					("1"))
      (simplify-antecedent "with(p:prop,not(p));")
      (block 
       (script-comment "node added by `instantiate-universal-antecedent' at (0 0 1 0)")
       (cut-with-single-formula "lambda(x:ind_1,lim(lambda(n:zz,s(n)(x)))) in ball(s(n),1)")
       (block 
	(script-comment "node added by `cut-with-single-formula' at (0)")
	(cut-with-single-formula "#(lambda(x:ind_1,lim(lambda(n:zz,s(n)(x)))),bfun)")
	(instantiate-existential ("lambda(x:ind_1,lim(lambda(n:zz,s(n)(x))))")))
       (block 
	(script-comment "node added by `cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises bfun-ball-membership-lemma)
	direct-and-antecedent-inference-strategy
	beta-reduce-repeatedly
	(force-substitution "lim(lambda(n:zz,s(n)(x)))"
			    "lim(lambda(k:zz,if(n<=k,s(k)(x),?pp)))"
			    (0))
	(block 
	 (script-comment "node added by `force-substitution' at (0)")
	 (apply-macete-with-minor-premises closed-balls-are-closed)
	 (block 
	  (script-comment "node added by `apply-macete-with-minor-premises' at (0)")
	  direct-and-antecedent-inference-strategy
	  (block 
	   (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0)")
	   simplify-insistently
	   direct-and-antecedent-inference-strategy
	   (cut-with-single-formula "forall(p,q:zz,n<=p and n<=q implies s(q)(x) in ball(s(p)(x),1))")
	   (block 
	    (script-comment "node added by `cut-with-single-formula' at (0)")
	    (force-substitution "x_$0"
                                                                 
				"s(x_$1)(x)"
                                                                 
				(0))
	    (backchain "with(f:sets[pp],
  forall(p,q:zz,
    with(p:pp,p:prop,
      with(p:prop,p and p) implies with(p:pp,p in f))));")
	    simplify)
	   (block 
	    (script-comment "node added by `cut-with-single-formula' at (1)")
	    (weaken (3 1 0))
	    (incorporate-antecedent "with(p:prop,p);")
	    (apply-macete-with-minor-premises tr%ball-membership-condition)
	    direct-and-antecedent-inference-strategy
	    (apply-macete-with-minor-premises transitivity-of-<=)
	    (block 
	     (script-comment "node added by `apply-macete-with-minor-premises' at (0)")
	     (instantiate-existential ("bfun%dist(s(p),s(q))"))
	     (block 
	      (script-comment "node added by `instantiate-existential' at (0 0)")
                                                                 
	      (apply-macete-with-minor-premises bounded-bfun%dist)
                                                                 
	      (instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
						("p" "q"))
                                                                 
	      (instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
						("p" "q")))
	     simplify
	     direct-and-antecedent-inference-strategy)
	    (apply-macete-with-minor-premises bfun-values-defined-lemma)))
	  (block 
	   (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1)")
	   (force-substitution "#(lim(lambda(k:zz,if(n<=k, s(k)(x), ?pp))))"
                                                                 
			       "lim(lambda(k:zz,if(n<=k, s(k)(x), ?pp)))=lim(lambda(n:zz,s(n)(x)))"
                                                                 
			       (0))
	   (block 
	    (script-comment "node added by `force-substitution' at (0)")
	    (weaken ("with(a,b:sets[pp], a subseteq b)"))
	    (apply-macete-with-minor-premises limit-depends-on-tail)
	    beta-reduce-repeatedly
	    direct-and-antecedent-inference-strategy
	    (instantiate-existential ("n"))
	    simplify
	    (apply-macete-with-minor-premises bfun-values-defined-lemma)
	    (instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
                                                                 
					      ("n" "p_$0"))
	    (simplify-antecedent "with(p:prop,not(p));"))
	   direct-and-antecedent-inference-strategy))
	 (block 
	  (script-comment "node added by `apply-macete-with-minor-premises' at (1)")
	  direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises bfun-values-defined-lemma)
	  (instantiate-universal-antecedent "with(p:prop,forall(p,q:zz,with(p:prop,p)));"
                                                                 
					    ("n" "n"))
	  (simplify-antecedent "with(p:prop,not(p));")))
	simplify))))
    (apply-macete-with-minor-premises tr%ball-membership-condition)


    )


   )


  
  (theory mappings-into-a-pointed-metric-space))

(def-theorem bfun-completeness
  "complete implies bfun%complete"

  (proof

   (
    
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (force-substitution "#(lim(s))" "lim(s)=lambda(x:ind_1,lim(lambda(n:zz, s(n)(x))))" (0))
    (apply-macete-with-minor-premises cauchy-ptwise-converge-implies-uniform-convergence)
    direct-and-antecedent-inference-strategy
    (backchain "forall(s:[zz,pp],cauchy(s) implies #(lim(s)));")
    (apply-macete-with-minor-premises uniform-cauchy-implies-ptwise-cauchy)
    direct-and-antecedent-inference-strategy

    )

   )

  (usages transportable-macete)

  (theory mappings-into-a-pointed-metric-space))


