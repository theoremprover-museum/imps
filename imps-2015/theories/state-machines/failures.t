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

(herald failures)

;;(set (proof-log-port) (standard-output))

(include-files
   (files (imps theories/state-machines/monoid-transition-system)))

(include-files
   (files (imps theories/metric-spaces/ultrametric-function-spaces)))

(def-theorem ()
  "#(lambda(u:uu,floor(lngth(u))),[uu,nn])"
  (theory  graded-monoid)
  (proof
   (


    sort-definedness
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "0<=floor(lngth(xx_0))")
    simplify
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises floor-not-much-below-arg)
     (apply-macete-with-minor-premises length-non-negative))
    )))

(def-translation functions-on-a-graded-set-to-graded-monoid
  (source functions-on-a-graded-set)
  (target graded-monoid)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (values "sets[sets[action]]"))
  (constant-pairs (degree "lambda(u:uu, floor(lngth(u)))"))
  (theory-interpretation-check using-simplification))

(def-theorem ()
  "forsome(x:[uu,sets[sets[action]]], total_q{x,[uu,sets[sets[action]]]})"
  (theory  graded-monoid)
  (proof
   (
    (instantiate-existential ("lambda(x:uu, empty_indic{sets[action]})"))
    simplify-insistently
    )))


(def-renamer fog-to-gms
  (pairs
   (total%fns total%fns)
   (discrete%lim discrete%lim)
   (fn%approx fn%approx)
   (fn%deg fn%deg)
   (fn%dist fn%dist)))

   
(def-transported-symbols (total%fns fn%approx fn%deg fn%dist discrete%lim)
  (translation functions-on-a-graded-set-to-graded-monoid))


(def-theorem graded-monoid-fn%dist-triangle-inequality
  fn%dist-triangle-inequality
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))

(def-theorem graded-monoid-fn%dist-symmetric
  fn%dist-symmetric
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))

(def-theorem graded-monoid-fn%dist-non-negative
  fn%dist-non-negative
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))  
  
(def-theorem  graded-monoid-fn%dist-reflexive
  fn%dist-reflexive
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))

(def-theory-ensemble-instances metric-spaces 
  force-under-quick-load
  (target-theories graded-monoid graded-monoid)
  (permutations  (0) (0 1))
  (theory-interpretation-check using-simplification)
  (sorts (pp total%fns total%fns))
  (constants (dist fn%dist fn%dist)))

(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-theorem all-failures-are-total
  "forall(x:ff,#(x,total%fns))"
  (theory graded-monoid)
  (usages d-r-convergence)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(x,ff)")
    (apply-macete-with-minor-premises
     total%fns-defining-axiom_graded-monoid)
    beta-reduce-repeatedly
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
    (unfold-single-defined-constant (0) failure_q)
    direct-and-antecedent-inference-strategy

    )))

(def-theorem ()
  "forall(x,y,z:ff,fn%dist(x,z)<=fn%dist(y,z)+fn%dist(x,y))"
  lemma
  (theory graded-monoid)
  (proof
   (

    (apply-macete-with-minor-premises commutative-law-for-addition)
    (apply-macete-with-minor-premises graded-monoid-fn%dist-triangle-inequality)
    )))
  

(def-translation ms-subspace-to-graded-monoid
  (source ms-subspace)
  (target graded-monoid)
  (sort-pairs (aa ff))
  (core-translation metric-spaces-to-graded-monoid)
  (theory-interpretation-check using-simplification))


(def-theory-ensemble-instances
  metric-spaces
  force-under-quick-load
  (target-theories graded-monoid graded-monoid)
  (multiples 1 2)
  (theory-interpretation-check using-simplification)
  (sorts (pp ff ff))
  (constants (dist "lambda(x,y:ff, fn%dist(x,y))" "lambda(x,y:ff, fn%dist(x,y))"))
  (special-renamings 
   (complete sub%complete)
   (cauchy sub%cauchy)
   (lim sub%lim)))

(def-theorem graded-monoid-fn%approx-separation
  fn%approx-separation
  lemma
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))

(def-theorem graded-monoid-fn%approx-monotonicity
  fn%approx-monotonicity
  lemma
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))
  
(def-theorem graded-monoid-fn%approx-existence
  fn%approx-existence
  lemma
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))

(def-theorem graded-monoid-fn%approx-reflexivity
  fn%approx-reflexivity
  lemma
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))

(def-theorem graded-monoid-fn%approx-symmetry
  fn%approx-symmetry
  lemma
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))

(def-theorem graded-monoid-fn%approx-transitivity
  fn%approx-transitivity
  lemma
  (theory graded-monoid)
  (translation functions-on-a-graded-set-to-graded-monoid)
  (proof existing-theorem))

(def-translation degree-equivalence-to-graded-monoid
  force-under-quick-load
  (source degree-equivalence)
  (target graded-monoid)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (pp "total%fns"))
  (constant-pairs (approx fn%approx))
  (theory-interpretation-check using-simplification))


(def-theorem characterization-ultrametric-limit-of-fns
  "forall(f:[zz->total%fns],s:total%fns,
      lim(f)=s
        iff 
      forall(m:zz, 0<=m implies
         forsome(n:zz, 
            forall(p:zz, u:uu, n<=p and lngth(u)<m+1 implies f(p)(u)=s(u)))))"
  (theory graded-monoid)
  (proof

   (



    (apply-macete-with-minor-premises tr%lim-characterization-for-sep%dist)
    direct-inference
    (unfold-single-defined-constant (0) fn%approx)
    (force-substitution "floor(lngth(k))<=n" "lngth(k)<n+1" (0))
    (move-to-sibling 1)
    (block 
      (script-comment "`force-substitution' at (1)")
      (cut-with-single-formula "forsome(m:zz, floor(lngth(k))=m)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,p);")
	(backchain "with(p:prop,p);")
	(incorporate-antecedent "with(p:prop,p);")
	(apply-macete-with-minor-premises floor-characterization)
	direct-and-antecedent-inference-strategy
	simplify
	simplify)
      (instantiate-existential ("floor(lngth(k))")))
    (block 
      (script-comment "`force-substitution' at (0)")
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
	(instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
					  ("m"))
	(instantiate-existential ("n"))
	(instantiate-universal-antecedent "with(p:prop,forall(p:zz,with(p:prop,p)));"
					  ("p"))
	(cut-with-single-formula " #(f(p),total%fns) and  #(s,total%fns)")
	(incorporate-antecedent "with(s,f:total%fns,#(f,total%fns) and #(s,total%fns));")
	(apply-macete-with-minor-premises total%fns-defining-axiom_graded-monoid)
	beta-reduce-repeatedly
	direct-and-antecedent-inference-strategy
	(incorporate-antecedent "with(m:zz,s:total%fns,
  with(f:[total%fns,total%fns,zz,prop],f)
   (with(f:total%fns,f),s,m));")
	simplify
	direct-and-antecedent-inference-strategy
	simplify)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1 0)")
	(incorporate-antecedent "with(p:prop,p);")
	(force-substitution "0<=m
     implies 
    forsome(n:zz,
      forall(p:zz,u:uu,
        n<=p and lngth(u)<m+1 implies f(p)(u)=s(u)))"
			    "0<=m
     implies 
0<=m and    forsome(n:zz,
      forall(p:zz,u:uu,
        n<=p and lngth(u)<m+1 implies f(p)(u)=s(u)))"
			    (0))
	(move-to-sibling 1)
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment "`force-substitution' at (0)")
	  direct-and-antecedent-inference-strategy
	  (cut-with-single-formula "forsome(n:zz, forall(p:zz, n<=p implies #(f(p))))")
	  (move-to-sibling 1)
	  (block 
	    (script-comment "`cut-with-single-formula' at (1)")
	    (instantiate-universal-antecedent "with(p:prop,p);"
					      ("0"))
	    (simplify-antecedent "with(p:prop,p);")
	    (block 
	      (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0)")
	      (instantiate-existential ("n"))
	      (instantiate-universal-antecedent "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));"
                                                                 
						("p" "e"))
	      (contrapose "with(p:prop,not(p));")
	      (apply-macete-with-minor-premises lngth-of-e)
	      simplify))
	  (block 
	    (script-comment "`cut-with-single-formula' at (0)")
	    (antecedent-inference "with(p:prop,forsome(n:zz,p));")
	    (instantiate-universal-antecedent "with(p:prop,forall(m:zz,0<=m implies p and p));"
					      ("m"))
	    (block 
	      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	      (instantiate-existential ("n"))
	      (instantiate-universal-antecedent "with(p:prop,forall(p:zz,with(p:prop,p)));"
                                                                 
						("p"))
	      beta-reduce-repeatedly
	      direct-and-antecedent-inference-strategy
	      (cut-with-single-formula "0<=lngth(k_$0)")
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		(contrapose "with(p:prop,not(p));")
		simplify)
	      (apply-macete-with-minor-premises length-non-negative))
	    (block 
	      (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0)")
	      (instantiate-existential ("n_$0"))
	      (cut-with-single-formula "#(f(p))")
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		beta-reduce-repeatedly
		direct-and-antecedent-inference-strategy
		simplify)
	      (block 
		(script-comment "`cut-with-single-formula' at (1)")
		(instantiate-universal-antecedent "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));"
                                                                 
						  ("p" "e"))
		(contrapose "with(p:prop,not(p));")
		(apply-macete-with-minor-premises lngth-of-e)
		simplify))))))


    )))

(def-theorem prefix-has-smaller-length-lemma
  "forall(a,b:uu, a prefix b implies lngth(a)<=lngth(b))"
  (theory  graded-monoid)
  lemma
  (proof
   (

    (unfold-single-defined-constant (0) prefix)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,p);")
    (apply-macete-with-minor-premises length-of-product)
    (cut-with-single-formula "0<=lngth(p)")
    simplify
    (apply-macete-with-minor-premises length-non-negative)
    )))

(def-theorem failure_q-is-closed-under-lim
  "forall(s:[zz,total%fns], 
     #(lim(s)) and 
      forall(n:zz, #(s(n)) implies failure_q(s(n)))
        implies 
      failure_q(lim(s)))"
  (theory graded-monoid)
  (proof 

   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x:total%fns, lim(s)=x)")
    (move-to-sibling 1)
    (instantiate-existential ("lim(s)"))
    (antecedent-inference "with(p:prop,forsome(x:total%fns,p));")
    (backchain "with(x,f:total%fns,f=x);")
    (incorporate-antecedent "with(x,f:total%fns,f=x);")
    (apply-macete-with-minor-premises characterization-ultrametric-limit-of-fns)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f:total%fns,forall(n:zz,#(f) implies failure_q(f)));")
    (unfold-single-defined-constant-globally failure_q)
    (force-substitution "forsome(m_$0:uu, germ(m_$0)=a_$0 and u_$0**m_$0 in support(s(n)))"
			"forsome(m_$0:uu, 
          germ(m_$0)=a_$0 and lngth(m_$0)<=1 and u_$0**m_$0 in support(s(n)))"
			(0))
    (move-to-sibling 1)
    (block 
     (script-comment "`force-substitution' at (1)")
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "forsome(u:uu, germ(u)=a_$0 and 0<=lngth(u) and lngth(u)<=1)")
     (move-to-sibling 1)
     (apply-macete-with-minor-premises action-representatives-can-have-norm-le-1)
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(u:uu,p));")
      (incorporate-antecedent "with(a_$0:action,f:sets[uu],f=a_$0);")
      (backchain-backwards "with(p:prop,p and p and p);")
      (apply-macete-with-minor-premises germ-equality-condition)
      direct-and-antecedent-inference-strategy
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
       (instantiate-existential ("e"))
       (backchain-backwards "with(u:uu,u=e);")
       (block 
	(script-comment "`instantiate-existential' at (0 1)")
	(apply-macete-with-minor-premises lngth-of-e)
	simplify)
       (block 
	(script-comment "`instantiate-existential' at (0 2)")
	(incorporate-antecedent "with(m_$0,u_$0:uu,f:total%fns,u_$0**m_$0 in support(f));")
	simplify))
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
       (instantiate-existential ("u_$1"))
       (block 
	(script-comment "`instantiate-existential' at (0 0)")
	(backchain-backwards "with(p:prop,p and p and p);")
	(apply-macete-with-minor-premises germ-equality-condition)
	direct-and-antecedent-inference-strategy
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
	 (instantiate-existential ("u_$1"))
	 (apply-macete-with-minor-premises prefix-is-reflexive))
	(instantiate-existential ("u_$1")))
       (block 
	(script-comment "`instantiate-existential' at (0 1)")
	(cut-with-single-formula "lngth(u_$1)<=lngth(u)")
	simplify
	(apply-macete-with-minor-premises prefix-has-smaller-length-lemma))
       (block 
	(script-comment "`instantiate-existential' at (0 2)")
	(cut-with-single-formula "(u_$0**u_$1) prefix (u_$0**m_$0)")
	(block 
	 (script-comment "`cut-with-single-formula' at (0)")
	 (backchain "with(p:prop,forall(u_$0,v_$0:uu,p));")
	 auto-instantiate-existential)
	(block 
	 (script-comment "`cut-with-single-formula' at (1)")
	 (unfold-single-defined-constant (0) prefix)
	 (incorporate-antecedent "with(m_$0,u_$1:uu,u_$1 prefix m_$0);")
	 (unfold-single-defined-constant (0) prefix)
	 direct-and-antecedent-inference-strategy
	 (backchain "with(u,m_$0:uu,m_$0=u);")
	 (apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)
	 (instantiate-existential ("p")))))))
    (unfold-single-defined-constant-globally support)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0)")
     (instantiate-universal-antecedent "with(p:prop,forall(m:zz,0<=m implies forsome(n:zz,p)));"
				       ("floor(lngth(u_$0))+1"))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
      (cut-with-single-formula "0<=floor(lngth(u_$0))")
      (simplify-antecedent "with(p:prop,not(p));")
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises floor-not-much-below-arg)
       (apply-macete-with-minor-premises length-non-negative)))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
      (instantiate-universal-antecedent "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));"
					("n" "u_$0"))
      (simplify-antecedent "with(p:prop,not(p));")
      (simplify-antecedent "with(p:prop,not(p));")
      (block 
       (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
       (instantiate-universal-antecedent "with(p:prop,forall(n:zz,p));"
					 ("n"))
       (backchain-backwards "with(f:sets[sets[action]],f=f);")
       (backchain "with(p:prop,forall(u_$0:uu,x_$8,y_$0:sets[action],p));")
       (instantiate-existential ("y_$0"))
       simplify)))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
     (instantiate-universal-antecedent "with(p:prop,forall(m:zz,0<=m implies forsome(n:zz,p)));"
				       ("1"))
     (simplify-antecedent "with(p:prop,not(p));")
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
      (backchain-backwards "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
      (instantiate-existential ("n"))
      simplify
      (block 
       (script-comment "`instantiate-existential' at (0 0 1)")
       (apply-macete-with-minor-premises lngth-of-e)
       simplify)
      (block 
       (script-comment "`instantiate-existential' at (0 1)")
       (backchain "with(p:prop,forall(n:zz,p));")
       (instantiate-universal-antecedent "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));"
					 ("n" "e")))))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 2 0 0 0 0 0)")
     (instantiate-universal-antecedent "with(p:prop,forall(m:zz,0<=m implies forsome(n:zz,p)));"
				       ("floor(lngth(u_$0))+1"))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
      (cut-with-single-formula "0<=floor(lngth(u_$0))")
      (simplify-antecedent "with(p:prop,not(p));")
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises floor-not-much-below-arg)
       (apply-macete-with-minor-premises length-non-negative)))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
      (backchain-backwards "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
      (instantiate-existential ("n"))
      simplify
      (block 
       (script-comment "`instantiate-existential' at (0 0 1)")
       (cut-with-single-formula "lngth(v_$0)<=lngth(u_$0)")
       simplify
       (apply-macete-with-minor-premises prefix-has-smaller-length-lemma))
      (block 
       (script-comment "`instantiate-existential' at (0 1)")
       (backchain "with(p:prop,forall(n:zz,p));")
       direct-and-antecedent-inference-strategy
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(instantiate-universal-antecedent "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));"
					  ("n" "u_$0"))
	(simplify-antecedent "with(p:prop,not(p));"))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(instantiate-existential ("u_$0"))
	(backchain "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
	simplify
	(instantiate-existential ("x_$1"))))))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 3 0 0 0 0 0 0 0)")
     (instantiate-universal-antecedent "with(p:prop,forall(m:zz,0<=m implies forsome(n:zz,p)));"
				       ("floor(lngth(u_$0))+1"))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
      (cut-with-single-formula "0<=floor(lngth(u_$0))")
      (simplify-antecedent "with(p:prop,not(p));")
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises floor-not-much-below-arg)
       (apply-macete-with-minor-premises length-non-negative)))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
      (backchain-backwards "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
      (instantiate-existential ("n"))
      simplify
      simplify
      (block 
       (script-comment "`instantiate-existential' at (0 1)")
       (instantiate-universal-antecedent "with(p:prop,forall(n:zz,p));"
					 ("n"))
       (instantiate-universal-antecedent "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));"
					 ("n" "u_$0"))
       (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0)")
	(instantiate-universal-antecedent "with(p:prop,forall(u_$0:uu,a_$0:action,p));"
					  ("u_$0" "a_$0"))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	 (contrapose "with(f:sets[sets[action]],empty_indic_q{f});")
	 (backchain "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
	 simplify
	 (instantiate-existential ("x_$1")))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0 0 0)")
	 (instantiate-universal-antecedent "with(p:prop,forall(m_$0:uu,p or p));"
                                                                 
					   ("m_$0"))
	 (contrapose "with(f:sets[sets[action]],empty_indic_q{f});")
	 (backchain-backwards "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
	 (instantiate-existential ("n"))
	 (block 
	  (script-comment "`instantiate-existential' at (0 0 1)")
	  (apply-macete-with-minor-premises length-of-product)
	  simplify)
	 (instantiate-existential ("x_$3")))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 1 1)")
	 (backchain "with(p:prop,forall(x_$8:sets[action],p));")
	 (backchain "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
	 simplify)))))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 4 0)")
     insistent-direct-inference
     (instantiate-universal-antecedent "with(p:prop,forall(m:zz,0<=m implies forsome(n:zz,p)));"
				       ("floor(lngth(x_$3))+1"))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
      (cut-with-single-formula "0<=lngth(x_$3)")
      (simplify-antecedent "with(p:prop,not(p));")
      (apply-macete-with-minor-premises length-non-negative))
     (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
      (backchain-backwards "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
      (instantiate-existential ("n"))
      simplify
      simplify
      (block 
       (script-comment "`instantiate-existential' at (0 1)")
       (backchain "with(p:prop,forall(n:zz,p));")
       (instantiate-universal-antecedent "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));"
					 ("n" "x_$3")))))
    (backchain "with(p:prop,f:total%fns,
  forall(n:zz,#(f) implies p and p and p and p and p and p));")
    (instantiate-universal-antecedent "with(p:prop,forall(m:zz,0<=m implies forsome(n:zz,p)));"
				      ("floor(lngth(u_$0))+1"))
    (block 
     (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
     (cut-with-single-formula "0<=lngth(u_$0)")
     (simplify-antecedent "with(p:prop,not(p));")
     (apply-macete-with-minor-premises length-non-negative))
    (instantiate-existential ("n"))
    (block 
     (script-comment "`instantiate-existential' at (0 0)")
     (instantiate-universal-antecedent "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));"
				       ("n" "u_$0"))
     (simplify-antecedent "with(p:prop,not(p));")
     (simplify-antecedent "with(p:prop,not(p));"))
    (backchain "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
    simplify
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 3)
    (block 
     (script-comment "`instantiate-existential' at (0 1)")
     (instantiate-existential ("u_$0"))
     (backchain "with(p:prop,forall(p:zz,u:uu,with(p:prop,p)));")
     simplify)
    )))
       

(def-theorem completeness-of-ff
  "sub%complete"
  (theory graded-monoid)
  (proof
   (

    (apply-macete-with-minor-premises tr%rev%completeness-extends)
    (block 
     (script-comment "`apply-macete-with-minor-premises' at (0)")
     (apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory)
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises failure_q-is-closed-under-lim)
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "#(s(n),ff)")
     (incorporate-antecedent "with(f:ff,#(f,ff));")
     (apply-macete-with-minor-premises ff-defining-axiom_directed-monoid-theory))
    (apply-macete-with-minor-premises tr%completeness-of-total%fns)

    )))