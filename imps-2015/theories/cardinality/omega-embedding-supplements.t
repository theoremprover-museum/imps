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

(herald OMEGA-EMBEDDING-SUPPLEMENTS)


;;(set (proof-log-port) (standard-output))

(def-theorem complete-induction-schema
  "forall(p:[zz,prop],n:zz,
          forall(k:zz,n<=k implies p(k))
           iff
          (truth
            and
          forall(m:zz,
           n<=m and forall(k:zz,n<=k and k<m implies p(k))
            implies 
            p(m))))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (backchain "with(p:[zz,prop],n:zz,forall(k:zz,n<=k implies p(k)));")
    (apply-macete-with-minor-premises complete-induction)
    (instantiate-existential ("n"))

    )))

(def-inductor complete-inductor
  complete-induction-schema
  (theory h-o-real-arithmetic))


(def-theorem omega-n-as-domain-lemma
  "forall(f:[nn->nn],n:nn, dom{f}=omega(n) iff forall(x:nn, #(f(x)) iff x<n))"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (

    (unfold-single-defined-constant (0) omega)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 0
0 0)")
      (instantiate-universal-antecedent "with(f:[nn,nn],dom{f})
 subseteq with(f:[nn,prop],pred_to_indic(f));"
					("x"))
      (simplify-antecedent "with(p:prop,not(p));")
      (simplify-antecedent "with(x:nn,f:sets[nn],x in f);"))
    (block 
      (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 0
1 0)")
      (instantiate-universal-antecedent "with(f:[nn,prop],pred_to_indic(f))
 subseteq with(f:[nn,nn],dom{f});"
					("x"))
      (simplify-antecedent "with(p:prop,not(p));")
      (simplify-antecedent "with(x:nn,f:sets[nn],x in f);"))
    (block 
      (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 1 0)")
      insistent-direct-inference
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(x:nn,p));"
					("x_$2"))
      simplify
      (simplify-antecedent "with(x_$2:nn,f:sets[nn],x_$2 in f);"))
    (block 
      (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 1 1)")
      insistent-direct-inference
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(x:nn,p iff p));"
					("x_$1"))
      simplify
      (block 
	(script-comment "node added by `instantiate-universal-antecedent' at (0 0 1)")
	simplify))

    )))

(def-theorem not-in-range-condition
  "forall(f,g:[nn,nn], m:nn, dom{f}=dom{g} and 
                       forall(k,l:nn, #(f(k)) and #(f(l)) and #(g(k)) and #(g(l)) and k<l 
                                       implies 
                                      f(k) < f(l) and g(k)<g(l))
                       and 
                       forall(x:nn, x<m implies f(x)==g(x))
                       and
                       f(m)<g(m)
                       implies not(f(m) in ran{g}))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (contrapose "with(f:sets[nn],f=f);")
    (antecedent-inference "with(p:prop,forsome(x:nn,p));")
    (contrapose "with(n:nn,n=n);")
    (cut-with-single-formula "x<m or x=m or m<x")
    (move-to-sibling 1)
    simplify
    (block 
      (script-comment "node added by `cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,p or p or p);")
      (block 
	(script-comment "node added by `antecedent-inference' at (0)")
	(case-split ("#(f(x)) and #(f(m))"))
	(block 
	  (script-comment "node added by `case-split' at (1)")
	  (cut-with-single-formula "f(x)=g(x) and f(x)<f(m)")
	  (move-to-sibling 1)
	  (block 
	    (script-comment "node added by `cut-with-single-formula' at (1)")
	    (backchain-backwards "with(p:prop,forall(x:nn,p));")
	    direct-and-antecedent-inference-strategy
	    (backchain "with(p:prop,forall(k,l:nn,p));")
	    direct-and-antecedent-inference-strategy
	    (backchain-backwards "with(p:prop,forall(x:nn,p));")
	    direct-and-antecedent-inference-strategy)
	  simplify)
	(block 
	  (script-comment "node added by `case-split' at (2)")
	  (contrapose "with(p:prop,not(p));")
	  direct-inference
	  simplify))
      simplify
      (block 
	(script-comment "node added by `antecedent-inference' at (2)")
	(case-split ("#(g(x))"))
	(block 
	  (script-comment "node added by `case-split' at (1)")
	  (cut-with-single-formula "g(m)<g(x)")
	  simplify
	  (block 
	    (script-comment "node added by `cut-with-single-formula' at (1)")
	    simplify
	    simplify
	    (backchain "with(p:prop,forall(k,l:nn,p));")
	    direct-and-antecedent-inference-strategy
	    (apply-macete-with-minor-premises tr%rev%domain-membership-iff-defined)
	    (backchain "with(f:sets[nn],f=f);")
	    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)))
	simplify))

    )))



(def-theorem characterization-of-omega-embedding-lemma
  "forall(f,g:[nn -> nn], n:nn, dom{f}= dom{g}
                                and ran{f}=ran{g} and
            forall(k,l:nn, k<l and l in dom{g} implies f(k) < f(l) and g(k)<g(l))
               implies
            g=f)"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(k:zz, 0<=k implies g(k)==f(k))")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      extensionality
      direct-inference
      simplify)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (induction complete-inductor ())
      (case-split ("m in dom{g}"))
      (block 
	(script-comment "`case-split' at (1)")
	(cut-with-single-formula "#(f(m)) and #(g(m))")
	(move-to-sibling 1)
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  direct-and-antecedent-inference-strategy
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	    (incorporate-antecedent "with(m:zz,f:sets[nn],m in f);")
	    (backchain-backwards "with(g,f:[nn,nn],dom{f}=dom{g});")
	    simplify)
	  (simplify-antecedent "with(m:zz,f:sets[nn],m in f);"))
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (cut-with-single-formula "g(m)<f(m) or g(m)=f(m) or f(m)<g(m)")
	  (move-to-sibling 1)
	  simplify
	  (block 
	    (script-comment "`cut-with-single-formula' at (0)")
	    (antecedent-inference "with(p:prop,p or p or p);")
	    (block 
	      (script-comment "`antecedent-inference' at (0)")
	      (cut-with-single-formula "not(g(m) in ran{f})")
	      (move-to-sibling 1)
	      (block 
		(script-comment "`cut-with-single-formula' at (1)")
		(apply-macete-with-minor-premises not-in-range-condition)
		direct-and-antecedent-inference-strategy
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0
0 0)")
		  (backchain "with(p:prop,forall(k,l:nn,p));")
		  simplify)
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0
1 0)")
		  (backchain "with(p:prop,forall(k,l:nn,p));")
		  simplify)
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0)")
		  (backchain "with(p:prop,forall(k:zz,p));")
		  simplify))
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		(contrapose "with(p:prop,not(p));")
		(backchain "with(g,f:[nn,nn],ran{f}=ran{g});")
		(apply-macete-with-minor-premises indicator-facts-macete)
		beta-reduce-repeatedly
		(instantiate-existential ("m"))))
	    (block 
	      (script-comment "`antecedent-inference' at (2)")
	      (cut-with-single-formula "not(f(m) in ran{g})")
	      (move-to-sibling 1)
	      (block 
		(script-comment "`cut-with-single-formula' at (1)")
		(apply-macete-with-minor-premises not-in-range-condition)
		direct-and-antecedent-inference-strategy
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0
0 0)")
		  (backchain "with(p:prop,forall(k,l:nn,p));")
		  simplify)
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0
1 0)")
		  (backchain "with(p:prop,forall(k,l:nn,p));")
		  simplify)
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0)")
		  (backchain "with(p:prop,forall(k:zz,p));")
		  simplify))
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		(contrapose "with(p:prop,not(p));")
		(backchain-backwards "with(g,f:[nn,nn],ran{f}=ran{g});")
		(apply-macete-with-minor-premises indicator-facts-macete)
		beta-reduce-repeatedly
		(instantiate-existential ("m")))))))
      (block 
	(script-comment "`case-split' at (2)")
	(cut-with-single-formula "not(#(g(m))) and not(#(f(m)))")
	simplify
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  direct-inference
	  (simplify-antecedent "with(p:prop,not(p));")
	  (block 
	    (script-comment "`direct-inference' at (1)")
	    (contrapose "with(m:zz,f:sets[nn],not(m in f));")
	    (backchain-backwards "with(g,f:[nn,nn],dom{f}=dom{g});")
	    simplify))))

    )))


(def-theorem characterization-of-omega-embedding
  "forall(f:[nn -> nn], s:sets[nn], 
                        (omega%embedding(s)=f 
                           iff
                        (dom{f}=dom(omega%embedding(s))
                          and ran{f}=s and
                         forall(k,l:nn, k<l and l in dom{f} implies f(k) < f(l)))))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    simplify
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
      (backchain-backwards "with(f:[nn,nn],f=f);")
      (apply-macete-with-minor-premises ran-of-omega%embedding))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2
0 0 0)")
      (backchain-backwards "with(f:[nn,nn],f=f);")
      (backchain-backwards "with(f:[nn,nn],f=f);")
      (apply-macete-with-minor-premises strong-monotonicity-of-omega%embedding)
      (backchain "with(f:[nn,nn],f=f);")
      direct-inference
      (simplify-antecedent "with(l:nn,f:sets[nn],l in f);"))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
      (apply-macete-with-minor-premises characterization-of-omega-embedding-lemma)
      direct-and-antecedent-inference-strategy
      (apply-macete-with-minor-premises ran-of-omega%embedding)
      simplify
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0
1 0)")
	(apply-macete-with-minor-premises strong-monotonicity-of-omega%embedding)
	direct-and-antecedent-inference-strategy
	(simplify-antecedent "with(l:nn,f:sets[nn],l in f);")))
    )))

(def-theorem upper-bound-of-finite-sequences
  "forall(f:[nn->rr],n:nn, 
         forsome(r:rr, forall(k:nn, k<=n and #(f(k))implies f(k)<=r)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forall(n:zz,0<=n implies   
        forsome(r:rr,forall(k:nn,k<=n and #(f(k)) implies f(k)<=r)))")
    simplify
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (induction integer-inductor ())
      (block 
	(script-comment "`induction' at (0 0 0)")
	(case-split ("#(f(0))"))
	(block 
	  (script-comment "`case-split' at (1)")
	  (instantiate-existential ("f(0)"))
	  (cut-with-single-formula "k_$0=0")
	  simplify
	  simplify)
	(block 
	  (script-comment "`case-split' at (2)")
	  (instantiate-existential ("0"))
	  (contrapose "with(p:prop,not(p));")
	  (cut-with-single-formula "k=0")
	  simplify
	  simplify))
      (block 
	(script-comment "`induction' at (0 1 0 0 0 0 0)")
	(case-split ("#(f(1+t))"))
	(block 
	  (script-comment "`case-split' at (1)")
	  (instantiate-existential ("max(r,f(1+t))"))
	  (case-split ("k_$0<=t"))
	  (block 
	    (script-comment "`case-split' at (1)")
	    (cut-with-single-formula "f(k_$0)<=r and r<=max(r,f(1+t))")
	    simplify
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (apply-macete-with-minor-premises maximum-1st-arg)
	      simplify))
	  (block 
	    (script-comment "`case-split' at (2)")
	    (cut-with-single-formula "f(1+t)<=max(r,f(1+t)) and f(k_$0)=f(1+t)")
	    simplify
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (apply-macete-with-minor-premises maximum-2nd-arg)
	      (cut-with-single-formula "k_$0=1+t")
	      simplify)))
	(block 
	  (script-comment "`case-split' at (2)")
	  (instantiate-existential ("r"))
	  (backchain "with(p:prop,forall(k:nn,p));")
	  direct-and-antecedent-inference-strategy
	  (cut-with-single-formula "not(k=1+t)")
	  simplify
	  (block 
	    (script-comment "`cut-with-single-formula' at (1)")
	    (contrapose "with(p:prop,not(p));")
	    simplify))))
    )))

(def-theorem upper-bound-of-finite-sequences-of-nn
  "forall(f:[nn->nn],n:nn, 
         forsome(m:nn, forall(k:nn, k<=n and #(f(k))implies f(k)<=m)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(r:rr, forall(k:nn, k<=n and #(f(k))implies f(k)<=r))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises upper-bound-of-finite-sequences)
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,p);")
      (cut-with-single-formula "forsome(n:zz, max(0,r)<n)")
      (move-to-sibling 1)
      (apply-macete-with-minor-premises archimedean)
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(n:zz,p));")
	(instantiate-existential ("n_$0"))
	(block 
	  (script-comment "`instantiate-existential' at (0 0 0)")
	  (cut-with-single-formula "r<=max(0,r) and f(k)<=r")
	  simplify
	  (block 
	    (script-comment "`cut-with-single-formula' at (1)")
	    (apply-macete-with-minor-premises maximum-2nd-arg)
	    simplify))
	(block 
	  (script-comment "`instantiate-existential' at (1)")
	  (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
	  beta-reduce-repeatedly
	  (cut-with-single-formula "0<=max(0,r)")
	  simplify
	  (apply-macete-with-minor-premises maximum-1st-arg))))
    )))


(def-theorem finite-sets-in-nn-are-bounded
  "forall(s:sets[nn], f_indic_q{s} implies forsome(n:nn, s subseteq omega(n)))"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(n:nn, omega(n) equinumerous s)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(n:nn,p));")
      (antecedent-inference "with(s,f:sets[nn],f equinumerous s);")
      (antecedent-inference "with(s:sets[nn],
  bijective_on_q{with(f:[nn,nn],f),with(f:sets[nn],f),s});")
      (cut-with-single-formula
       "forsome(r:nn, forall(k:nn, k<=n and #(f(k)) implies f(k)<=r))")
      (move-to-sibling 1)
      (apply-macete-with-minor-premises upper-bound-of-finite-sequences-of-nn)
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(weaken (1))
	(antecedent-inference "with(s:sets[nn],
  surjective_on_q{with(f:[nn,nn],f),with(f:sets[nn],f),s});")
	(incorporate-antecedent "with(s:sets[nn],f:[nn,nn],ran{f}=s);")
	(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	direct-inference
	(antecedent-inference "with(p:prop,p and p);")
	(instantiate-existential ("r+1"))
	insistent-direct-inference
	(instantiate-universal-antecedent
	 "with(f:[nn,nn],s:sets[nn],s subseteq ran{f});"
	 ("x"))
	(move-to-ancestor 3)
	direct-inference
	(instantiate-universal-antecedent "with(f:[nn,nn],s:sets[nn],s subseteq ran{f});"
					  ("x"))
	(contrapose "with(x:nn,f:[nn,nn],x in ran{f});")
	(apply-macete-with-minor-premises indicator-facts-macete)
	beta-reduce-repeatedly
	(contrapose "with(p:prop,not(p));")
	(unfold-single-defined-constant (0) omega)
	(apply-macete-with-minor-premises indicator-facts-macete)
	beta-reduce-repeatedly
	(antecedent-inference "with(p:prop,forsome(x_$1:nn,p));")
	(backchain "with(n,x:nn,x=n);")
	(instantiate-universal-antecedent "with(r,n:nn,p:prop,forall(k:nn,p and p implies n<=r));"
					  ("x_$1"))
	(block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 0 0)")
	  (contrapose "with(f:sets[nn],f=f);")
	  (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	  (contrapose "with(n,x_$1:nn,not(x_$1<=n));")
	  (antecedent-inference "with(p:prop,p and p);")
	  (instantiate-universal-antecedent "with(n:nn,f:[nn,nn],dom{f} subseteq omega(n));"
					    ("x_$1"))
	  (simplify-antecedent "with(x_$1:nn,f:sets[nn],not(x_$1 in f));")
	  (block 
	    (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	    (incorporate-antecedent "with(x_$1,n:nn,x_$1 in omega(n));")
	    (unfold-single-defined-constant (0) omega)
	    (apply-macete-with-minor-premises indicator-facts-macete)
	    simplify))
	simplify))
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (incorporate-antecedent "with(p:prop,p);")
      (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
      (apply-macete-with-minor-premises tr%iota-free-definition-of-f-card)
      direct-and-antecedent-inference-strategy
      (move-to-ancestor 3)
      (instantiate-existential ("n"))
      (apply-macete-with-minor-premises tr%equinumerous-is-symmetric))

    )))

(def-theorem subset-of-nn-finite-iff-bounded
  "forall(s:sets[nn], f_indic_q{s} iff forsome(n:nn, s subseteq omega(n)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises finite-sets-in-nn-are-bounded)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
      (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
      (cut-with-single-formula "forsome(m:nn, m<=n and f_card{s}=m)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(m:nn,p));")
	(instantiate-existential ("m")))
      (apply-macete-with-minor-premises subset-of-finite-cardinal-has-f-card))

    )))

(def-theorem domain-of-omega-embedding-for-finite-sets
  "forall(s:sets[nn], f_indic_q{s} implies dom{omega%embedding(s)}=omega(f_card{s}))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (apply-macete-with-minor-premises subset-of-nn-finite-iff-bounded)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forsome(m:nn, m<=n and dom{omega%embedding(s)}=omega(m))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises dom-of-omega%embedding-at-finite-set)
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(m:nn,p));")
      (backchain "with(p:prop,p and p);")
      (cut-with-single-formula "f_card{s}=m")
      simplify
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises tr%iota-free-definition-of-f-card)
	(antecedent-inference "with(p:prop,p and p);")
	(apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
	(instantiate-existential ("omega%embedding(s)"))
	insistent-direct-inference
	(block 
	  (script-comment "`insistent-direct-inference' at (0)")
	  insistent-direct-inference
	  (apply-macete-with-minor-premises ran-of-omega%embedding))
	(block 
	  (script-comment "`insistent-direct-inference' at (1)")
	  (apply-macete-with-minor-premises tr%injective-implies-injective-on)
	  (apply-macete-with-minor-premises injectiveness-of-omega%embedding))))

    )))


(def-theorem characterization-of-omega-embedding-for-finite-sets
  "forall(f:[nn -> nn], s:sets[nn],
                         f_indic_q{s}
                           implies 
                        (omega%embedding(s)=f 
                           iff
                        (dom{f}=omega(f_card{s})
                          and ran{f}=s and
                         forall(k,l:nn, k<l and l in dom{f} implies f(k) < f(l)))))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (force-substitution "omega(f_card{s})" "dom(omega%embedding(s))" (0))
    (move-to-sibling 1)
    (apply-macete-with-minor-premises domain-of-omega-embedding-for-finite-sets)
    (apply-macete-with-minor-premises characterization-of-omega-embedding)
    )))

(def-theorem domain-of-omega-embedding-for-infinite-sets
  "forall(s:sets[nn], 
           not(f_indic_q{s})
               implies 
           dom{omega%embedding(s)}=sort_to_indic{nn})"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-inference
    simplify-insistently
    (block 
      (script-comment "`direct-inference' at (1)")
      insistent-direct-inference
      (apply-macete-with-minor-premises indicator-facts-macete)
      beta-reduce-repeatedly
      direct-and-antecedent-inference-strategy
      (contrapose "with(p:prop,not(p));")
      (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
      (apply-macete-with-minor-premises tr%iota-free-definition-of-f-card)
      (cut-with-single-formula "forsome(n:nn, dom{omega%embedding(s)}=omega(n))")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(n:nn,p));")
	(instantiate-existential ("n"))
	(backchain-backwards "with(f:sets[nn],f=f);")
	(apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
	(instantiate-existential ("omega%embedding(s)"))
	insistent-direct-inference
	(block 
	  (script-comment "`insistent-direct-inference' at (0)")
	  insistent-direct-inference
	  (apply-macete-with-minor-premises ran-of-omega%embedding))
	(block 
	  (script-comment "`insistent-direct-inference' at (1)")
	  (apply-macete-with-minor-premises tr%injective-implies-injective-on)
	  (apply-macete-with-minor-premises injectiveness-of-omega%embedding)))
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(weaken (2 1))
	(contrapose "with(p:prop,p);")
	(cut-with-single-formula "forall(k:zz, 0<=k implies #(omega%embedding(s)(k)))")
	simplify
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (induction complete-inductor ("k"))
	  (move-to-ancestor 3)
	  (antecedent-inference "with(p:prop,p and p);")
	  (incorporate-antecedent "with(p:prop,forall(n:nn,not(p)));")
	  (apply-macete-with-minor-premises omega-n-as-domain-lemma)
	  direct-and-antecedent-inference-strategy
	  (contrapose "with(p:prop,forall(n:nn,not(p)));")
	  (instantiate-existential ("m"))
	  (block 
	    (script-comment "`instantiate-existential' at (0 0 0)")
	    (contrapose "with(n:nn,#(n));")
	    (case-split ("m=x or m<x"))
	    (antecedent-inference "with(p:prop,p or p);")
	    simplify
	    (instantiate-theorem strong-monotonicity-of-omega%embedding
				 ("s" "m" "x")))
	  simplify)))

    )))

(def-theorem characterization-of-omega-embedding-for-infinite-sets
  "forall(f:[nn -> nn], s:sets[nn],
                         not(f_indic_q{s})
                           implies 
                        (omega%embedding(s)=f 
                           iff
                        (dom{f}=sort_to_indic{nn}
                          and ran{f}=s and
                         forall(k,l:nn, k<l and l in dom{f} implies f(k) < f(l)))))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (force-substitution "sort_to_indic{nn}" "dom(omega%embedding(s))" (0))
    (move-to-sibling 1)
    (apply-macete-with-minor-premises domain-of-omega-embedding-for-infinite-sets)
    (apply-macete-with-minor-premises characterization-of-omega-embedding)
    )))

;;(set (proof-log-port) (standard-output))


(def-theorem compositionality-of-omega-embedding
  "forall(s:sets[nn], f:[nn -> nn], 
         s subseteq dom{f} and 
         forall(a,b:nn, a<b and a in s and b in s implies f(a)<f(b))
           implies
         omega%embedding(image{f,s})=f oo (omega%embedding(s)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("f_indic_q{s}"))
    (block 
      (script-comment "`case-split' at (1)")
      (apply-macete-with-minor-premises characterization-of-omega-embedding-for-finite-sets)
      (move-to-sibling 1)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (1)")
	(cut-with-single-formula "f_card{image{f,s}}<=f_card{s}")
	(apply-macete-with-minor-premises tr%image-of-a-finite-set-is-finite))
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	  (apply-macete-with-minor-premises tr%domain-composition)
	  (move-to-sibling 1)
	  (apply-macete-with-minor-premises ran-of-omega%embedding)
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (0)")
	    (apply-macete-with-minor-premises domain-of-omega-embedding-for-finite-sets)
	    (cut-with-single-formula "f_card{s}=f_card{image{f,s}}")
	    simplify
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (apply-macete-with-minor-premises tr%f-card-equal-iff-finite-and-equinumerous)
	      direct-and-antecedent-inference-strategy
	      (block 
		(script-comment "`direct-and-antecedent-inference-strategy' at (1 1 0)")
		(instantiate-existential ("restrict{f,s}"))
		insistent-direct-inference
		(block 
		  (script-comment "`insistent-direct-inference' at (0)")
		  insistent-direct-inference
		  (apply-macete-with-minor-premises tr%domain-of-a-restriction)
		  (block 
		    (script-comment "`insistent-direct-inference' at (1)")
		    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
		    direct-inference
		    (block 
		      (script-comment "`direct-inference' at (0)")
		      insistent-direct-inference
		      (apply-macete-with-minor-premises indicator-facts-macete)
		      beta-reduce-repeatedly)
		    (block 
		      (script-comment "`direct-inference' at (1)")
		      insistent-direct-inference
		      (apply-macete-with-minor-premises indicator-facts-macete)
		      beta-reduce-repeatedly)))
		(block 
		  (script-comment "`insistent-direct-inference' at (1)")
		  insistent-direct-inference
		  direct-and-antecedent-inference-strategy
		  (contrapose "with(p:prop,forall(a,b:nn,p));")
		  (cut-with-single-formula "x_$1<x_$2 or x_$2<x_$1")
		  (move-to-sibling 1)
		  simplify
		  (block 
		    (script-comment "`cut-with-single-formula' at (0)")
		    (antecedent-inference "with(p:prop,p or p);")
		    (block 
		      (script-comment "`antecedent-inference' at (0)")
		      (instantiate-existential ("x_$1" "x_$2"))
		      (contrapose "with(n:nn,n=n);")
		      simplify-insistently)
		    (block 
		      (script-comment "`antecedent-inference' at (1)")
		      (instantiate-existential ("x_$2" "x_$1"))
		      (contrapose "with(n:nn,n=n);")
		      simplify-insistently))))
	      (weaken (0)))))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	  (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	  direct-inference
	  (block 
	    (script-comment "`direct-inference' at (0)")
	    insistent-direct-inference
	    (apply-macete-with-minor-premises indicator-facts-macete)
	    beta-reduce-repeatedly
	    direct-and-antecedent-inference-strategy
	    (cut-with-single-formula "omega%embedding(s)(x_$9) in s")
	    auto-instantiate-existential
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (apply-macete-with-minor-premises tr%membership-in-a-range)
	      (instantiate-existential ("x_$9" "omega%embedding(s)"))
	      (apply-macete-with-minor-premises ran-of-omega%embedding)))
	  (block 
	    (script-comment "`direct-inference' at (1)")
	    insistent-direct-inference
	    (apply-macete-with-minor-premises indicator-facts-macete)
	    beta-reduce-repeatedly
	    direct-and-antecedent-inference-strategy
	    (cut-with-single-formula "s=ran{omega%embedding(s)}")
	    (move-to-sibling 1)
	    (apply-macete-with-minor-premises ran-of-omega%embedding)
	    (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	      (incorporate-antecedent "with(x:nn,s:sets[nn],x in s);")
	      (backchain "with(f:[nn,nn],s:sets[nn],s=ran{f});")
	      (apply-macete-with-minor-premises indicator-facts-macete)
	      beta-reduce-repeatedly
	      direct-and-antecedent-inference-strategy
	      (instantiate-existential ("x_$0"))
	      simplify)))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0 0)")
	  simplify-insistently
	  (backchain "with(p:prop,forall(a,b:nn,p));")
	  (block 
	    (script-comment "`backchain' at (0)")
	    (apply-macete-with-minor-premises strong-monotonicity-of-omega%embedding)
	    simplify
	    (cut-with-single-formula "s=ran{omega%embedding(s)}")
	    (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	      (force-substitution "s"
				  "ran{omega%embedding(s)}"
				  (2 4))
	      (apply-macete-with-minor-premises tr%membership-in-a-range)
	      (block 
		(script-comment "`apply-macete-with-minor-premises' at (0)")
		direct-and-antecedent-inference-strategy
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
		  (incorporate-antecedent "with(l_$0:nn,f:sets[nn],l_$0 in f);")
		  simplify-insistently)
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
		  (instantiate-existential ("k_$0" "omega%embedding(s)"))
		  simplify
		  (apply-macete-with-minor-premises omega%embedding-strong-definedness)
		  (instantiate-existential ("l_$0"))
		  simplify)
		(instantiate-existential ("l_$0" "omega%embedding(s)")))
	      (block 
		(script-comment "`apply-macete-with-minor-premises' at (1)")
		(apply-macete-with-minor-premises omega%embedding-strong-definedness)
		(instantiate-existential ("l_$0"))
		simplify))
	    (apply-macete-with-minor-premises ran-of-omega%embedding))
	  direct-inference)))
    (block 
      (script-comment "`case-split' at (2)")
      (apply-macete-with-minor-premises characterization-of-omega-embedding-for-infinite-sets)
      (move-to-sibling 1)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (1)")
	(contrapose "with(p:prop,not(p));")
	(cut-with-single-formula "f_card{s}<=f_card{image{f,s}}")
	(apply-macete-with-minor-premises tr%f-card-leq-iff-finite-and-embeds)
	direct-inference
	(instantiate-existential ("restrict{f,s}"))
	(apply-macete-with-minor-premises tr%domain-of-a-restriction)
	(block 
	  (script-comment "`instantiate-existential' at (0 1)")
	  insistent-direct-inference
	  (apply-macete-with-minor-premises indicator-facts-macete)
	  beta-reduce-repeatedly)
	(block 
	  (script-comment "`instantiate-existential' at (0 2)")
	  (apply-macete-with-minor-premises tr%injective-implies-injective-on)
	  insistent-direct-inference
	  direct-and-antecedent-inference-strategy
	  (contrapose "with(n:nn,n=n);")
	  (cut-with-single-formula "x_$0<x_$1 or x_$1<x_$0")
	  (move-to-sibling 1)
	  simplify
	  (block 
	    (script-comment "`cut-with-single-formula' at (0)")
	    (antecedent-inference "with(p:prop,p or p);")
	    (block 
	      (script-comment "`antecedent-inference' at (0)")
	      (contrapose "with(p:prop,forall(a,b:nn,p));")
	      auto-instantiate-existential
	      (block 
		(script-comment "`auto-instantiate-existential' at (0 1)")
		(contrapose "with(n:nn,n=n);")
		simplify-insistently)
	      (block 
		(script-comment "`auto-instantiate-existential' at (0 2)")
		(contrapose "with(n:nn,n=n);")
		simplify-insistently)
	      (block 
		(script-comment "`auto-instantiate-existential' at (0 3)")
		(contrapose "with(n:nn,n=n);")
		simplify-insistently))
	    (block 
	      (script-comment "`antecedent-inference' at (1)")
	      (contrapose "with(p:prop,forall(a,b:nn,p));")
	      auto-instantiate-existential
	      (block 
		(script-comment "`auto-instantiate-existential' at (0 1)")
		(contrapose "with(n:nn,n=n);")
		simplify-insistently)
	      (block 
		(script-comment "`auto-instantiate-existential' at (0 2)")
		(contrapose "with(n:nn,n=n);")
		simplify-insistently)
	      (block 
		(script-comment "`auto-instantiate-existential' at (0 3)")
		(contrapose "with(n:nn,n=n);")
		simplify-insistently)))))
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	  (apply-macete-with-minor-premises tr%domain-composition)
	  (move-to-sibling 1)
	  (apply-macete-with-minor-premises ran-of-omega%embedding)
	  (apply-macete-with-minor-premises domain-of-omega-embedding-for-infinite-sets))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	  (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	  direct-inference
	  (block 
	    (script-comment "`direct-inference' at (0)")
	    insistent-direct-inference
	    (apply-macete-with-minor-premises indicator-facts-macete)
	    beta-reduce-repeatedly
	    direct-and-antecedent-inference-strategy
	    (cut-with-single-formula "omega%embedding(s)(x) in s")
	    (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	      auto-instantiate-existential
	      (instantiate-existential ("omega%embedding(s)(x)")))
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (apply-macete-with-minor-premises tr%membership-in-a-range)
	      (instantiate-existential ("x_$2" "omega%embedding(s)"))
	      (apply-macete-with-minor-premises ran-of-omega%embedding)
	      (move-to-ancestor 2)
	      (instantiate-existential ("x" "omega%embedding(s)"))))
	  (block 
	    (script-comment "`direct-inference' at (1)")
	    insistent-direct-inference
	    (apply-macete-with-minor-premises indicator-facts-macete)
	    beta-reduce-repeatedly
	    direct-and-antecedent-inference-strategy
	    (cut-with-single-formula "s=ran{omega%embedding(s)}")
	    (move-to-sibling 1)
	    (apply-macete-with-minor-premises ran-of-omega%embedding)
	    (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	      (incorporate-antecedent "with(x:nn,s:sets[nn],x in s);")
	      (backchain "with(f:[nn,nn],s:sets[nn],s=ran{f});")
	      (apply-macete-with-minor-premises indicator-facts-macete)
	      beta-reduce-repeatedly
	      direct-and-antecedent-inference-strategy
	      (instantiate-existential ("x_$0"))
	      simplify)))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (2 0 0
0)")
	  simplify-insistently
	  (backchain "with(p:prop,forall(a,b:nn,p));")
	  (block 
	    (script-comment "`backchain' at (0)")
	    (apply-macete-with-minor-premises strong-monotonicity-of-omega%embedding)
	    simplify
	    (cut-with-single-formula "s=ran{omega%embedding(s)}")
	    (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	      (force-substitution "s"
				  "ran{omega%embedding(s)}"
				  (2 4))
	      (apply-macete-with-minor-premises tr%membership-in-a-range)
	      (block 
		(script-comment "`apply-macete-with-minor-premises' at (0)")
		direct-and-antecedent-inference-strategy
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
		  (incorporate-antecedent "with(l:nn,f:sets[nn],l in f);")
		  simplify-insistently)
		(block 
		  (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
		  (instantiate-existential ("k" "omega%embedding(s)"))
		  simplify
		  (apply-macete-with-minor-premises omega%embedding-strong-definedness)
		  (instantiate-existential ("l"))
		  simplify)
		(instantiate-existential ("l" "omega%embedding(s)")))
	      (block 
		(script-comment "`apply-macete-with-minor-premises' at (1)")
		(apply-macete-with-minor-premises omega%embedding-strong-definedness)
		(instantiate-existential ("l"))
		simplify))
	    (apply-macete-with-minor-premises ran-of-omega%embedding))
	  direct-inference)))
    )))




(comment unblocked proof
	 
	 direct-and-antecedent-inference-strategy
	 (case-split ("f_indic_q{s}"))
	 (apply-macete-with-minor-premises characterization-of-omega-embedding-for-finite-sets)
	 (move-to-sibling 1)
	 (block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  (cut-with-single-formula "f_card{image{f,s}}<=f_card{s}")
	  (apply-macete-with-minor-premises tr%image-of-a-finite-set-is-finite))
	 direct-and-antecedent-inference-strategy
	 (apply-macete-with-minor-premises tr%domain-composition)
	 (move-to-sibling 1)
	 (apply-macete-with-minor-premises ran-of-omega%embedding)
	 (apply-macete-with-minor-premises domain-of-omega-embedding-for-finite-sets)
	 (cut-with-single-formula "f_card{s}=f_card{image{f,s}}")
	 simplify
	 (apply-macete-with-minor-premises tr%f-card-equal-iff-finite-and-equinumerous)
	 direct-and-antecedent-inference-strategy
	 (instantiate-existential ("restrict{f,s}"))
	 insistent-direct-inference
	 insistent-direct-inference
	 (apply-macete-with-minor-premises tr%domain-of-a-restriction)
	 (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	 direct-inference
	 insistent-direct-inference
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce-repeatedly
	 insistent-direct-inference
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce-repeatedly
	 insistent-direct-inference
	 direct-and-antecedent-inference-strategy
	 (contrapose "with(p:prop,forall(a,b:nn,p));")
	 (cut-with-single-formula "x_$1<x_$2 or x_$2<x_$1")
	 (move-to-sibling 1)
	 simplify
	 (antecedent-inference "with(p:prop,p or p);")
	 (instantiate-existential ("x_$1" "x_$2"))
	 (contrapose "with(n:nn,n=n);")
	 simplify-insistently
	 (instantiate-existential ("x_$2" "x_$1"))
	 (contrapose "with(n:nn,n=n);")
	 simplify-insistently
	 (weaken (0))
	 (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	 direct-inference
	 insistent-direct-inference
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce-repeatedly
	 direct-and-antecedent-inference-strategy
	 (cut-with-single-formula "omega%embedding(s)(x_$9) in s")
	 auto-instantiate-existential
	 (apply-macete-with-minor-premises tr%membership-in-a-range)
	 (instantiate-existential ("x_$9" "omega%embedding(s)"))
	 (apply-macete-with-minor-premises ran-of-omega%embedding)
	 insistent-direct-inference
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce-repeatedly
	 direct-and-antecedent-inference-strategy
	 (cut-with-single-formula "s=ran{omega%embedding(s)}")
	 (move-to-sibling 1)
	 (apply-macete-with-minor-premises ran-of-omega%embedding)
	 (incorporate-antecedent "with(x:nn,s:sets[nn],x in s);")
	 (backchain "with(f:[nn,nn],s:sets[nn],s=ran{f});")
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce-repeatedly
	 direct-and-antecedent-inference-strategy
	 (instantiate-existential ("x_$0"))
	 simplify
	 simplify-insistently
	 (backchain "with(p:prop,forall(a,b:nn,p));")
	 (apply-macete-with-minor-premises strong-monotonicity-of-omega%embedding)
	 simplify
	 (cut-with-single-formula "s=ran{omega%embedding(s)}")
	 (force-substitution "s" "ran{omega%embedding(s)}" (2 4))
	 (apply-macete-with-minor-premises tr%membership-in-a-range)
	 direct-and-antecedent-inference-strategy
	 (incorporate-antecedent "with(l_$0:nn,f:sets[nn],l_$0 in f);")
	 simplify-insistently
	 (instantiate-existential ("k_$0" "omega%embedding(s)"))
	 simplify
	 (apply-macete-with-minor-premises omega%embedding-strong-definedness)
	 (instantiate-existential ("l_$0"))
	 simplify
	 (instantiate-existential ("l_$0" "omega%embedding(s)"))
	 (apply-macete-with-minor-premises omega%embedding-strong-definedness)
	 (instantiate-existential ("l_$0"))
	 simplify
	 (apply-macete-with-minor-premises ran-of-omega%embedding)
	 direct-inference
	 (apply-macete-with-minor-premises characterization-of-omega-embedding-for-infinite-sets)
	 (move-to-sibling 1)
	 (contrapose "with(p:prop,not(p));")
	 (cut-with-single-formula "f_card{s}<=f_card{image{f,s}}")
	 (apply-macete-with-minor-premises tr%f-card-leq-iff-finite-and-embeds)
	 direct-inference
	 (instantiate-existential ("restrict{f,s}"))
	 (apply-macete-with-minor-premises tr%domain-of-a-restriction)
	 insistent-direct-inference
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce-repeatedly
	 (apply-macete-with-minor-premises tr%injective-implies-injective-on)
	 insistent-direct-inference
	 direct-and-antecedent-inference-strategy
	 (contrapose "with(n:nn,n=n);")
	 (cut-with-single-formula "x_$0<x_$1 or x_$1<x_$0")
	 (move-to-sibling 1)
	 simplify
	 (antecedent-inference "with(p:prop,p or p);")
	 (contrapose "with(p:prop,forall(a,b:nn,p));")
	 auto-instantiate-existential
	 (contrapose "with(n:nn,n=n);")
	 simplify-insistently
	 (contrapose "with(n:nn,n=n);")
	 simplify-insistently
	 (contrapose "with(n:nn,n=n);")
	 simplify-insistently
	 (contrapose "with(p:prop,forall(a,b:nn,p));")
	 auto-instantiate-existential
	 (contrapose "with(n:nn,n=n);")
	 simplify-insistently
	 (contrapose "with(n:nn,n=n);")
	 simplify-insistently
	 (contrapose "with(n:nn,n=n);")
	 simplify-insistently
	 direct-and-antecedent-inference-strategy
	 (apply-macete-with-minor-premises tr%domain-composition)
	 (move-to-sibling 1)
	 (apply-macete-with-minor-premises ran-of-omega%embedding)
	 (apply-macete-with-minor-premises domain-of-omega-embedding-for-infinite-sets)
	 (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	 direct-inference
	 insistent-direct-inference
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce-repeatedly
	 direct-and-antecedent-inference-strategy
	 (cut-with-single-formula "omega%embedding(s)(x) in s")
	 auto-instantiate-existential
	 (instantiate-existential ("omega%embedding(s)(x)"))
	 (apply-macete-with-minor-premises tr%membership-in-a-range)
	 (instantiate-existential ("x_$2" "omega%embedding(s)"))
	 (apply-macete-with-minor-premises ran-of-omega%embedding)
	 (move-to-ancestor 2)
	 (instantiate-existential ("x" "omega%embedding(s)"))
	 insistent-direct-inference
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce-repeatedly
	 direct-and-antecedent-inference-strategy
	 (cut-with-single-formula "s=ran{omega%embedding(s)}")
	 (move-to-sibling 1)
	 (apply-macete-with-minor-premises ran-of-omega%embedding)
	 (incorporate-antecedent "with(x:nn,s:sets[nn],x in s);")
	 (backchain "with(f:[nn,nn],s:sets[nn],s=ran{f});")
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce-repeatedly
	 direct-and-antecedent-inference-strategy
	 (instantiate-existential ("x_$0"))
	 simplify
	 simplify-insistently
	 (backchain "with(p:prop,forall(a,b:nn,p));")
	 (apply-macete-with-minor-premises strong-monotonicity-of-omega%embedding)
	 simplify
	 (cut-with-single-formula "s=ran{omega%embedding(s)}")
	 (force-substitution "s" "ran{omega%embedding(s)}" (2 4))
	 (apply-macete-with-minor-premises tr%membership-in-a-range)
	 direct-and-antecedent-inference-strategy
	 (incorporate-antecedent "with(l:nn,f:sets[nn],l in f);")
	 simplify-insistently
	 (instantiate-existential ("k" "omega%embedding(s)"))
	 simplify
	 (apply-macete-with-minor-premises omega%embedding-strong-definedness)
	 (instantiate-existential ("l"))
	 simplify
	 (instantiate-existential ("l" "omega%embedding(s)"))
	 (apply-macete-with-minor-premises omega%embedding-strong-definedness)
	 (instantiate-existential ("l"))
	 simplify
	 (apply-macete-with-minor-premises ran-of-omega%embedding)
	 direct-inference





	 )
