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

(herald tree-like-spaces)

(load-section metric-spaces)

;;(set (proof-log-port) (standard-output))

(def-language degree-equivalence-language
  (embedded-languages h-o-real-arithmetic)
  (base-types pp)
  (constants
   (approx "[pp,pp,zz->prop]")))

(def-theory degree-equivalence
  (language degree-equivalence-language)
  (component-theories  h-o-real-arithmetic)
  (axioms
   (approx-separation
    "forall(x,y:pp, not(x=y) implies forsome(n:zz, not(approx(x,y,n))))")
   (approx-monotonicity
    "forall(m,n:zz,x,y:pp, approx(x,y,n) and m<=n implies approx(x,y,m))")
   (approx-existence
    "forall(x,y:pp, forsome(m:zz, approx(x,y,m)))")
   (approx-reflexivity
    "forall(m:zz,x:pp, approx(x,x,m))")
   (approx-symmetry
    "forall(m:zz,x,y:pp, approx(x,y,m) implies  approx(y,x,m))")
   (approx-transitivity
    "forall(m:zz,x,y,z:pp, approx(x,y,m) and approx(y,z,m) implies approx(x,z,m))")))

(def-constant sep%deg
  "lambda(x,y:pp,
      iota(n:zz, not(approx(x,y,n)) 
                  and 
                 forall(m:zz, m<n implies approx(x,y,m))))"
  (theory degree-equivalence))

(def-theorem iota-free-characterization-of-sep%deg
  "forall(x,y:pp, n:zz, 
            sep%deg(x,y)=n iff 
            (not(approx(x,y,n)) 
                  and 
             forall(m:zz, m<n implies approx(x,y,m))))"
  (theory degree-equivalence)
  (proof
   (


    (unfold-single-defined-constant (0) sep%deg)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (contrapose "with(p:prop,p);")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      (contrapose "with(p:prop,p);"))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0)")
      (contrapose "with(n:zz,n=n);")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      (contrapose "with(m:zz,y,x:pp,not(approx(x,y,m)));")
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula "b<=n and n<=b")
      simplify
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	direct-inference
	(block 
	  (script-comment "`direct-inference' at (0)")
	  (contrapose "with(n:zz,y,x:pp,not(approx(x,y,n)));")
	  simplify)
	(block 
	  (script-comment "`direct-inference' at (1)")
	  (contrapose "with(b:zz,y,x:pp,not(approx(x,y,b)));")
	  simplify)))
    )))


(def-theorem alternate-iota-free-characterization-of-sep%deg
  "forall(x,y:pp, n:zz, 
            sep%deg(x,y)=n iff 
            (not(approx(x,y,n)) and approx(x,y,n-1)))"
  (theory degree-equivalence)
  (proof
   (


    (apply-macete-with-minor-premises iota-free-characterization-of-sep%deg)
    direct-and-antecedent-inference-strategy
    simplify
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 1 0 0 0)")
      (apply-macete-with-minor-premises approx-monotonicity)
      (instantiate-existential ("n-1"))
      simplify)

    )))

(def-theorem definedness-of-sep%deg
  "forall(x,y:pp,  not(x=y) implies #(sep%deg(x,y)))"
  (theory degree-equivalence)
  (usages d-r-convergence)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:zz, sep%deg(x,y)=s)")
    (antecedent-inference "with(p:prop,forsome(s:zz,p));")
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises iota-free-characterization-of-sep%deg)
      (instantiate-theorem well-ordering-for-integers
			   ("lambda(n:zz, not(approx(x,y,n)))"))
      (block 
	(script-comment "`instantiate-theorem' at (0 0 0)")
	(contrapose "with(p:prop,forall(y:zz,p));")
	simplify
	(apply-macete-with-minor-premises approx-separation))
      (block 
	(script-comment "`instantiate-theorem' at (0 0 1)")
	(beta-reduce-antecedent "with(y,x:pp,
  forall(n:zz,
    forsome(m:zz,
      m<=n and lambda(n:zz,not(approx(x,y,n)))(m))));")
	(contrapose "with(p:prop,forall(n:zz,p));")
	(cut-with-single-formula "forsome(n:zz, approx(x,y,n))")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (instantiate-existential ("n"))
	  (apply-macete-with-minor-premises approx-monotonicity)
	  auto-instantiate-existential)
	(apply-macete-with-minor-premises approx-existence))
      (block 
	(script-comment "`instantiate-theorem' at (0 1 0 0)")
	(beta-reduce-antecedent "with(u:zz,y,x:pp,lambda(n:zz,not(approx(x,y,n)))(u));")
	(beta-reduce-antecedent "with(y,x:pp,u:zz,
  forall(v:zz,
    v<u implies not(lambda(n:zz,not(approx(x,y,n)))(v))));")
	auto-instantiate-existential
	(instantiate-universal-antecedent "with(p:prop,forall(v:zz,p));"
					  ("m"))))

    )))


(def-theorem undefinedness-case-of-sep%deg
  "forall(x:pp, not(#(sep%deg(x,x))))"
  (theory degree-equivalence)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(n:zz, approx(x,x,n))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises approx-reflexivity)
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (contrapose "with(p:prop,p);")
      (cut-with-single-formula "forsome(s:zz, sep%deg(x,x)=s)")
      (move-to-sibling 1)
      (instantiate-existential ("sep%deg(x,x)"))
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(s:zz,p));")
	(incorporate-antecedent "with(s,n:zz,n=s);")
	(apply-macete-with-minor-premises iota-free-characterization-of-sep%deg)
	direct-and-antecedent-inference-strategy
	auto-instantiate-existential))
    )))


(def-theorem sep%deg-upper-bound
  "forall(x,y:pp, n:zz, not(x=y) 
	    implies
	    (sep%deg(x,y)<=n iff not(approx(x,y,n))))"
  (theory  degree-equivalence)
  (proof
   (

    
    direct-inference
    direct-inference
    (cut-with-single-formula "forsome(s:zz, sep%deg(x,y)=s)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,forsome(s:zz,p));")
     (backchain "with(s,n:zz,n=s);")
     (incorporate-antecedent "with(s,n:zz,n=s);")
     (apply-macete-with-minor-premises iota-free-characterization-of-sep%deg)
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (contrapose "with(s:zz,y,x:pp,not(approx(x,y,s)));")
      (apply-macete-with-minor-premises approx-monotonicity)
      auto-instantiate-existential)
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
      (contrapose "with(n:zz,y,x:pp,not(approx(x,y,n)));")
      simplify))
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (instantiate-existential ("sep%deg(x,y)"))
     simplify)

    ))
  )

(def-theorem symmetry-of-sep%deg
  "forall(x,y:pp, not(x=y) 
	    implies
	    sep%deg(x,y)=sep%deg(y,x))"
  (theory  degree-equivalence)
  lemma
  (proof
   (

    (apply-macete-with-minor-premises iota-free-characterization-of-sep%deg)
    direct-inference
    direct-inference
    (cut-with-single-formula "forsome(s:zz, sep%deg(y,x)=s)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(s:zz,p));")
      (backchain-repeatedly ("with(s:zz,x,y:pp,sep%deg(y,x)=s);"))
      (incorporate-antecedent "with(s,n:zz,n=s);")
      (apply-macete-with-minor-premises iota-free-characterization-of-sep%deg)
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
	(contrapose "with(s:zz,x,y:pp,not(approx(y,x,s)));")
	(apply-macete-with-minor-premises approx-symmetry))
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0 0)")
	(apply-macete-with-minor-premises approx-symmetry)
	simplify))
    (instantiate-existential ("sep%deg(y,x)"))

    )))


(comment
 (def-theorem sep%deg-lower-bound
  "forall(x,y:pp, n:zz, not(x=y) 
	    implies
	    (n<sep%deg(x,y)iff approx(x,y,n)))"
  (theory  degree-equivalence)
  (proof
   (


    direct-inference
    direct-inference
    (cut-with-single-formula "forsome(s:zz, sep%deg(x,y)=s)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(s:zz,p));")
      (backchain "with(s,n:zz,n=s);")
      (incorporate-antecedent "with(s,n:zz,n=s);")
      (apply-macete-with-minor-premises iota-free-characterization-of-sep%deg)
      direct-and-antecedent-inference-strategy
      simplify
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
	(contrapose "with(s:zz,y,x:pp,not(approx(x,y,s)));")
	(apply-macete-with-minor-premises approx-monotonicity)
	auto-instantiate-existential
	simplify))
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (instantiate-existential ("sep%deg(x,y)"))
      simplify)
    ))))


(def-theorem reverse-ultrametric-lemma
  "forall(x,y,z:pp, 
      not x=y and not y=z and not x=z and sep%deg(x,y)<=sep%deg(y,z)
       implies
      sep%deg(x,y)<=sep%deg(x,z))"
  lemma
  (theory degree-equivalence)
  (proof
   (
    

    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(n:zz,n<=n);")
    (apply-macete-with-minor-premises sep%deg-upper-bound)
    (cut-with-single-formula "forsome(s,t:zz, sep%deg(y,z)=s and sep%deg(x,z)=t)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(s,t:zz,p));")
      (backchain-repeatedly
       ("with(t:zz,x:pp,s:zz,z,y:pp,
            sep%deg(y,z)=s and sep%deg(x,z)=t);"))
      (incorporate-antecedent "with(p:prop,p and p);")
      (apply-macete-with-minor-premises iota-free-characterization-of-sep%deg)
      direct-and-antecedent-inference-strategy
      (contrapose "with(t:zz,z,x:pp,not(approx(x,z,t)));")
      (case-split ("t<s"))
      (block 
	(script-comment "`case-split' at (1)")
	(apply-macete-with-minor-premises approx-transitivity)
	auto-instantiate-existential
	(backchain "with(z,y:pp,s:zz,forall(m:zz,m<s implies approx(y,z,m)));"))
      (block 
	(script-comment "`case-split' at (2)")
	(contrapose "with(s:zz,y,x:pp,not(approx(x,y,s)));")
	(apply-macete-with-minor-premises approx-monotonicity)
	auto-instantiate-existential
	simplify))
    (instantiate-existential ("sep%deg(y,z)" "sep%deg(x,z)"))
    )))



(def-theorem reverse-ultrametric-inequality
  "forall(x,y,z:pp, 
      not x=y and not y=z and not x=z 
       implies
      min(sep%deg(x,y),sep%deg(y,z))<=sep%deg(x,z))"
  (theory degree-equivalence)
  lemma
  (proof
   (
    

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) min)
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      (apply-macete-with-minor-premises reverse-ultrametric-lemma)
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      (apply-macete-with-minor-premises symmetry-of-sep%deg)
      (apply-macete-with-minor-premises reverse-ultrametric-lemma)
      (apply-macete-with-minor-premises symmetry-of-sep%deg)
      simplify)
    )))

(def-constant sep%dist
  "lambda(x,y:pp, if(x=y,0,2^(- sep%deg(x,y))))"
  (theory degree-equivalence))

(def-theorem sep%dist-reflexive
  "forall(x,y:pp, sep%dist(x,y)=0 iff x=y)"
  reverse
  (theory degree-equivalence)
  (proof
   (

    (unfold-single-defined-constant (0) sep%dist)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    (case-split ("x=y"))
    simplify
    (block 
      (script-comment "`case-split' at (2)")
      simplify
      (cut-with-single-formula "0<[1/2]^sep%deg(x,y)")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises positivity-for-r^n)
	simplify)
      simplify)
    )))

(def-theorem sep%dist-non-negative
  "forall(x,y:pp, 0<=sep%dist(x,y))"
  (theory degree-equivalence)
  (proof
   (

    direct-inference
    (case-split ("x=y"))
    (block 
      (script-comment "`case-split' at (1)")
      (cut-with-single-formula "sep%dist(x,y)=0")
      simplify
      (apply-macete-with-minor-premises sep%dist-reflexive))
    (block 
      (script-comment "`case-split' at (2)")
      (unfold-single-defined-constant-globally sep%dist)
      simplify
      (cut-with-single-formula "0<[1/2]^sep%deg(x,y)")
      simplify
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises positivity-for-r^n)
	simplify))
    )))

(def-theorem sep%dist-symmetric
  "forall(x,y:pp, sep%dist(x,y)=sep%dist(y,x))"
  (theory degree-equivalence)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (case-split ("x=y"))
    (block 
      (script-comment "`case-split' at (1)")
      (cut-with-single-formula "sep%dist(x,y)=0 and sep%dist(x,y)=0")
      (apply-macete-with-minor-premises sep%dist-reflexive))
    (block 
      (script-comment "`case-split' at (2)")
      unfold-defined-constants
      simplify
      (cut-with-single-formula "sep%deg(x,y)=sep%deg(y,x)")
      simplify
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-locally symmetry-of-sep%deg
			      (0)
			      "sep%deg(x,y)")
	simplify))
    )))

(comment
 (def-theorem monotonicity-of-exponentiation
   "forall(a:rr, x,y:zz, x<=y and 0<a and a<=1 implies a^y<=a^x)"
   (theory h-o-real-arithmetic)
   lemma
   (proof
    (

     (induction integer-inductor ("y"))
     (force-substitution "a^(1+t)<=a^x" "a*a^t<=1*a^x" (0))
     (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises monotone-product-lemma)
      (cut-with-single-formula "0<a^t")
      simplify
      (apply-macete-with-minor-premises positivity-for-r^n))
     (block 
      (script-comment "`force-substitution' at ()")
      direct-inference
      simplify)
     )))

 (def-theorem strict-monotonicity-of-exponentiation
   "forall(a:rr, x,y:zz, x<y and 0<a and a<1 implies a^y<a^x)"
   (theory h-o-real-arithmetic)
   lemma
   (proof
    (


     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "a^y<=a^(x+1)")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises monotonicity-of-exponentiation)
      simplify)
     (cut-with-single-formula "a^(x+1)<a^x")
     simplify
     (force-substitution "a^(x+1)<a^x" "0<(1-a)*a^x" (0))
     (move-to-sibling 1)
     (block 
      (script-comment "`force-substitution' at (1)")
      (weaken ("a<1"))
      simplify)
     (block 
      (script-comment "`force-substitution' at (0)")
      simplify
      (apply-macete-with-minor-premises positivity-for-r^n))

     ))))

(def-theorem min-under-nondecreasing-fn-lemma
  "forall(x,y:zz,f:[zz,rr], 
          forall(x,y:zz, x<=y implies f(y)<=f(x))
                  implies
          f(min(x,y))=max(f(x),f(y)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    (case-split ("x<=y"))
    (block 
      (script-comment "`case-split' at (1)")
      simplify
      (cut-with-single-formula "f(y)<f(x) or f(y)=f(x)")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	simplify
	(instantiate-universal-antecedent "with(p:prop,forall(x,y:zz,p));"
					  ("x" "y"))
	simplify)
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,p or p);")
	simplify
	simplify))
    (block 
      (script-comment "`case-split' at (2)")
      simplify
      (cut-with-single-formula "f(x)<f(y) or f(x)=f(y)")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(instantiate-universal-antecedent "with(p:prop,forall(x,y:zz,p));"
					  ("y" "x"))
	simplify
	simplify)
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,p or p);")
	simplify
	simplify))
    )))


(def-theorem sep%dist-ultrametric
  "forall(x,y,z:pp, sep%dist(x,z)<=max(sep%dist(x,y),sep%dist(y,z)))"
  (theory degree-equivalence)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("x=z"))
    (block 
      (script-comment "`case-split' at (1)")
      (cut-with-single-formula "sep%dist(x,z)=0")
      (block 
	(script-comment "`cut-with-single-formula' at (0)") simplify
	(unfold-single-defined-constant (0) max)
	(cut-with-single-formula "0<=sep%dist(x,y) and 0<= sep%dist(y,x)")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)") simplify
	  (case-split-on-conditionals (0))
	  )
	(apply-macete-with-minor-premises sep%dist-non-negative)
	)
      (apply-macete-with-minor-premises sep%dist-reflexive)
      )
    (block 
      (script-comment "`case-split' at (2)") (case-split ("x=y"))
      (block 
	(script-comment "`case-split' at (1)") simplify
	(cut-with-single-formula "sep%dist(x,x)=0")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (unfold-single-defined-constant (0) max) simplify
	  )
	(apply-macete-with-minor-premises sep%dist-reflexive)
	)
      (block 
	(script-comment "`case-split' at (2)") (case-split ("y=z"))
	(block 
	  (script-comment "`case-split' at (1)") simplify
	  (cut-with-single-formula "sep%dist(z,z)=0")
	  (block 
	    (script-comment "`cut-with-single-formula' at (0)")
	    (unfold-single-defined-constant (0) max) simplify
	    (cut-with-single-formula "0<sep%dist(x,z)") simplify
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (cut-with-single-formula "0<=sep%dist(x,y) and not sep%dist(x,y)=0")
	      simplify
	      (block 
		(script-comment "`cut-with-single-formula' at (1)")
		(apply-macete-with-minor-premises sep%dist-non-negative)
		(apply-macete-with-minor-premises sep%dist-reflexive)
		) ) )
	  (apply-macete-with-minor-premises sep%dist-reflexive)
	  )
	(block 
	  (script-comment "`case-split' at (2)")
	  (unfold-single-defined-constant-globally sep%dist) simplify
	  (instantiate-theorem min-under-nondecreasing-fn-lemma
			       ("sep%deg(x,y)" "sep%deg(y,z)" "lambda(n:zz, [1/2]^n)")
			       )
	  (block 
	    (script-comment "`instantiate-theorem' at (0 0 0 0)")
	    (contrapose "with(r:rr,not(r<=r));") beta-reduce-repeatedly
	    (apply-macete-with-minor-premises monotonicity-of-exponentiation)
	    simplify
	    )
	  (block 
	    (script-comment "`instantiate-theorem' at (0 1)")
	    (beta-reduce-antecedent
	     "with(z,y,x:pp,
  lambda(n:zz,[1/2]^n)(min(sep%deg(x,y),sep%deg(y,z)))
  =max(lambda(n:zz,[1/2]^n)(sep%deg(x,y)),
       lambda(n:zz,[1/2]^n)(sep%deg(y,z))));"
	     )
	    (backchain-backwards "with(r:rr,r=r);")
	    (apply-macete-with-minor-premises monotonicity-of-exponentiation)
	    (apply-macete-with-minor-premises reverse-ultrametric-inequality)
	    simplify
	    ) ) ) )

    )))


(include-files
 (files (imps theories/metric-spaces/ultrametric-spaces)))
 

(def-translation ultrametric-to-degree-equivalence
  force-under-quick-load
  (source ultrametric-spaces)
  (target degree-equivalence)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs (dist sep%dist))
  (theory-interpretation-check using-simplification))

(def-theorem sep%dist-is-a-metric
  ultrametic-spaces-are-metric
  (theory degree-equivalence)
  (translation ultrametric-to-degree-equivalence)
  (proof existing-theorem))
    
(def-theory-ensemble-instances metric-spaces 
  force-under-quick-load
  (target-theories degree-equivalence degree-equivalence)
  (permutations  (0) (0 1))
  (theory-interpretation-check using-simplification)
  (sorts (pp pp pp))
  (constants (dist sep%dist sep%dist)))

;; This is put in here to cause the translation to be enriched.

(def-translation ultrametric-to-degree-equivalence
  force-under-quick-load
  (source ultrametric-spaces)
  (target degree-equivalence)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs (dist sep%dist))
  (theory-interpretation-check using-simplification))

(def-theory-ensemble-overloadings metric-spaces 
  (1 2))

(def-theorem small-distance-characterization-lemma
  "forall(x,y:pp, n:zz, sep%dist(x,y)<=2^(-n) iff (x=y or n<=sep%deg(x,y)))"
  lemma
  (theory degree-equivalence)
  (proof
   (

    direct-inference
    (case-split ("x=y"))
    (block 
     (script-comment "`case-split' at (1)")
     (cut-with-single-formula "sep%dist(x,y)=0 ")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      simplify
      (cut-with-single-formula "0<[1/2]^n")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises positivity-for-r^n)
       simplify))
     (apply-macete-with-minor-premises sep%dist-reflexive))
    (block 
     (script-comment "`case-split' at (2)")
     (unfold-single-defined-constant (0) sep%dist)
     simplify
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      (contrapose "with(r:rr,r<=r);")
      (cut-with-single-formula "[1/2]^n < [1/2]^sep%deg(x,y)")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises strict-monotonicity-of-exponentiation)
       simplify))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      (apply-macete-with-minor-premises monotonicity-of-exponentiation)
      simplify)))))


(def-theorem small-distance-characterization
  "forall(x,y:pp, n:zz, sep%dist(x,y)<=2^(-n) iff approx(x,y,n-1))"
  (theory degree-equivalence)
  lemma
  (usages transportable-macete)
  (proof
   (


    (apply-macete-with-minor-premises small-distance-characterization-lemma)
    (force-substitution "n<=sep%deg(x,y)" "not(sep%deg(x,y)<=n-1)" (0))
    (move-to-sibling 1)
    (block 
      (script-comment "`force-substitution' at (1)")
      (cut-with-single-formula "#(sep%deg(x,y))")
      (move-to-sibling 1)
      (apply-macete-with-minor-premises definedness-of-sep%deg)
      (prove-by-logic-and-simplification 0))
    (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises sep%deg-upper-bound)
      direct-and-antecedent-inference-strategy
      simplify
      (apply-macete-with-minor-premises approx-reflexivity))
    )))

(def-theorem powers-arbitrarily-small
  "forall(r,eps:rr,
      0<r and r<1 and 0<eps
       implies 
      forsome(n:zz,1<=n and r^n<=eps))"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "convergent%to%infinity(lambda(n:zz,(r^[-1])^n))")
    (move-to-sibling 1)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises r^n-convergent-to-infinity)
      (apply-macete-with-minor-premises fractional-expression-manipulation)
      simplify)
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(f:[zz,rr],convergent%to%infinity(f));")
      (unfold-single-defined-constant (0) convergent%to%infinity)
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(m:rr,p));"
					("eps^[-1]"))
      (instantiate-universal-antecedent "with(p:prop,forall(j:zz,p));"
					("max(1,x)"))
      (simplify-antecedent "with(p:prop,not(p));")
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	(incorporate-antecedent "with(r:rr,r<=r);")
	(apply-macete-with-minor-premises fractional-expression-manipulation)
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  simplify
	  direct-and-antecedent-inference-strategy
	  auto-instantiate-existential
	  simplify)
	(apply-macete-with-minor-premises positivity-for-r^n))))))


(def-theorem cauchy-characterization-for-sep%dist
  "forall(f:[zz->pp],
      cauchy(f) 
        iff 
      forall(m:zz, forsome(n:zz, forall(p:zz, n<=p implies approx(f(p),f(p+1),m)))))"
  (theory degree-equivalence)
  (usages transportable-macete)
  (proof
   (

    (apply-macete-with-minor-premises tr%cauchy-ultrametric-condition)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (instantiate-universal-antecedent "with(p:prop,p);" ("2^(-(m+1))"))
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	(contrapose "with(p:prop,p);")
	(apply-macete-with-minor-premises positivity-for-r^n)
	simplify)
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
	(instantiate-existential ("n_$0"))
	(incorporate-antecedent "with(p:prop,forall(m_$0:zz,p));")
	(apply-macete-with-minor-premises small-distance-characterization)
	simplify))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
      (cut-with-single-formula "forsome(n:zz,1<=n and 2^(-n)<=eps)")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	simplify
	(apply-macete-with-minor-premises powers-arbitrarily-small)
	simplify)
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
					  ("n-1"))
	(instantiate-existential ("max(n_$0,n)"))
	(cut-with-single-formula "sep%dist(f(m_$0),f(m_$0+1))<=2^(-n)")
	simplify
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises small-distance-characterization)
	  (backchain "with(p:prop,forall(p_$0:zz,p));")
	  (cut-with-single-formula "n_$0<=max(n_$0,n)")
	  simplify
	  simplify)))

    )))

(def-theorem strong-cauchy-characterization-for-sep%dist
  "forall(f:[zz->pp],
      cauchy(f) 
        iff 
      forall(m:zz, forsome(n:zz, forall(p,q:zz, n<=p and n<=q implies approx(f(p),f(q),m)))))"
  (theory degree-equivalence)
  (usages transportable-macete)
  (proof
   (


    (apply-macete-with-minor-premises tr%cauchy-double-index-characterization)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (instantiate-universal-antecedent "with(p:prop,p);" ("2^(-(m+1))"))
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	(contrapose "with(p:prop,p);")
	(apply-macete-with-minor-premises positivity-for-r^n)
	simplify)
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
	(incorporate-antecedent "with(p:prop,p);")
	(apply-macete-with-minor-premises small-distance-characterization)
	simplify
	direct-and-antecedent-inference-strategy
	(instantiate-existential ("n"))))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
      (cut-with-single-formula "forsome(n:zz,1<=n and 2^(-n)<=eps)")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	simplify
	(apply-macete-with-minor-premises powers-arbitrarily-small)
	simplify)
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
					  ("n-1"))
	(instantiate-existential ("max(n_$0,n)"))
	(cut-with-single-formula "sep%dist(f(p_$0),f(q_$0))<=2^(-n)")
	simplify
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises small-distance-characterization)
	  (backchain "with(p:prop,forall(p_$0,q_$0:zz,p));")
	  (cut-with-single-formula "n_$0<=max(n_$0,n)")
	  simplify
	  simplify)))

    )))

(def-theorem lim-characterization-for-sep%dist
  "forall(f:[zz->pp],s:pp,
      lim(f)=s
        iff 
      forall(m:zz, forsome(n:zz, forall(p:zz, n<=p implies approx(f(p),s,m)))))"
  (theory degree-equivalence)
  (usages transportable-macete)
  (proof
   (


    (apply-macete-with-minor-premises tr%characterization-of-limit)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (instantiate-universal-antecedent "with(p:prop,p);" ("2^(-(m+1))"))
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 0)")
	(contrapose "with(p:prop,p);")
	(apply-macete-with-minor-premises positivity-for-r^n)
	simplify)
      (block 
	(script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
	(instantiate-existential ("n_$0"))
	(incorporate-antecedent "with(p:prop,forall(p_$0:zz,p));")
	(apply-macete-with-minor-premises small-distance-characterization)
	simplify
	direct-and-antecedent-inference-strategy
	(apply-macete-with-minor-premises approx-symmetry)
	simplify))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
      (cut-with-single-formula "forsome(n:zz,1<=n and 2^(-n)<=eps_$0)")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	simplify
	(apply-macete-with-minor-premises powers-arbitrarily-small)
	simplify)
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
					  ("n-1"))
	(instantiate-existential ("max(n_$0,n)"))
	(cut-with-single-formula "sep%dist(s,f(p_$1))<=2^(-n)")
	simplify
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises small-distance-characterization)
	  (apply-macete-with-minor-premises approx-symmetry)
	  (backchain "with(p:prop,forall(p_$0:zz,p));")
	  (cut-with-single-formula "n_$0<=max(n_$0,n)")
	  simplify
	  simplify)))

    )))


(include-files
 (files (imps theories/metric-spaces/mu-operator)))

;; Update everything:

(def-theory-ensemble-instances metric-spaces 
  force-under-quick-load
  (target-theories degree-equivalence degree-equivalence)
  (permutations  (0) (0 1))
  (theory-interpretation-check using-simplification)
  (sorts (pp pp pp))
  (constants (dist sep%dist sep%dist)))

(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-theorem characterization-of-contractiveness
  "forall(x,y,u,v:pp,
       forall(m:zz,approx(x,y,m) implies approx(u,v,m+1))
        implies 
       sep%dist(u,v)<=[1/2]*sep%dist(x,y))"
  (theory degree-equivalence)
  (proof
   (



    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally sep%dist)
    (case-split ("x=y"))
    (block 
     (script-comment "`case-split' at (1)")
     simplify
     (case-split ("u=v"))
     simplify
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      (contrapose "with(p:prop,forall(m:zz,p));")
      (backchain "with(y,x:pp,x=y);")
      (cut-with-single-formula "forsome(m:zz, not(approx(u,v,m+1)))")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,forsome(m:zz,p));")
       (instantiate-existential ("m"))
       (apply-macete-with-minor-premises approx-reflexivity))
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (cut-with-single-formula "forsome(m:zz,not(approx(u,v,m)))")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(m:zz,p));")
	(instantiate-existential ("m-1"))
	simplify)
       (apply-macete-with-minor-premises approx-separation))))
    (block 
     (script-comment "`case-split' at (2)")
     simplify
     (case-split ("u=v"))
     (block 
      (script-comment "`case-split' at (1)")
      simplify
      (cut-with-single-formula "0<[1/2]^sep%deg(x,y)")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises positivity-for-r^n)
       simplify))
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      simplify
      (force-substitution "2*[1/2]^sep%deg(u,v)"
			  "[1/2]^(sep%deg(u,v)-1)"
			  (0))
      (move-to-sibling 1)
      (block 
       (script-comment "`force-substitution' at (1)")
       simplify
       (apply-macete-with-minor-premises sum-of-exponents-law))
      (block 
       (script-comment "`force-substitution' at (0)")
       (apply-macete-with-minor-premises monotonicity-of-exponentiation)
       direct-and-antecedent-inference-strategy
       (move-to-sibling 2)
       simplify
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(apply-macete-with-minor-premises sep%deg-upper-bound)
	(cut-with-single-formula "forsome(m:zz ,sep%deg(u,v)=m)")
	(block 
	 (script-comment "`cut-with-single-formula' at (0)")
	 (antecedent-inference "with(p:prop,forsome(m:zz,p));")
	 (backchain "with(m,z:zz,z=m);")
	 (incorporate-antecedent "with(m,z:zz,z=m);")
	 (apply-macete-with-minor-premises alternate-iota-free-characterization-of-sep%deg)
	 direct-and-antecedent-inference-strategy
	 (contrapose "with(m:zz,v,u:pp,not(approx(u,v,m)));")
	 (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
                                                                 
					   ("m-1"))
	 (simplify-antecedent "with(r:rr,v,u:pp,approx(u,v,r+1));"))
	(instantiate-existential ("sep%deg(u,v)")))
       simplify)))

    )))

(def-theorem contraction-characterization-for-sep%dist
  "forall(f:[pp->pp], 
     forall(x,y:pp, m:zz, approx(x,y,m) implies approx(f(x),f(y),m+1))
        implies
     contraction(f))"
  (theory degree-equivalence)
  (proof
   (



    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) contraction)
    (instantiate-existential ("[1/2]"))
    simplify
    simplify
    (block 
     (script-comment "`instantiate-existential' at (0 2 0 0)")
     (apply-macete-with-minor-premises characterization-of-contractiveness)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      direct-and-antecedent-inference-strategy
      simplify)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (simplify-antecedent "with(p:prop,p and p);"))
     (simplify-antecedent "with(p:prop,p and p);"))

    )))


;;the proof of the following is virtually identical...

(def-theorem characterization-of-non-expansiveness
  "forall(x,y,u,v:pp,
       forall(m:zz,approx(x,y,m) implies approx(u,v,m))
        implies 
       sep%dist(u,v)<=sep%dist(x,y))"
  (theory degree-equivalence)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally sep%dist)
    (case-split ("x=y"))
    (block 
     (script-comment "`case-split' at (1)")
     simplify
     (case-split ("u=v"))
     simplify
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      (contrapose "with(p:prop,forall(m:zz,p));")
      (backchain "with(y,x:pp,x=y);")
      (cut-with-single-formula "forsome(m:zz, not(approx(u,v,m)))")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,forsome(m:zz,p));")
       (instantiate-existential ("m"))
       (apply-macete-with-minor-premises approx-reflexivity))
      (apply-macete-with-minor-premises approx-separation)))
    (block 
     (script-comment "`case-split' at (2)")
     simplify
     (case-split ("u=v"))
     (block 
      (script-comment "`case-split' at (1)")
      simplify
      (cut-with-single-formula "0<[1/2]^sep%deg(x,y)")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises positivity-for-r^n)
       simplify))
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      (apply-macete-with-minor-premises monotonicity-of-exponentiation)
      direct-and-antecedent-inference-strategy
      (move-to-sibling 1)
      simplify
      (move-to-sibling 2)
      simplify
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
       (apply-macete-with-minor-premises sep%deg-upper-bound)
       (cut-with-single-formula "forsome(m:zz, sep%deg(u,v)=m)")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(m:zz,p));")
	(backchain "with(m,z:zz,z=m);")
	(incorporate-antecedent "with(m,z:zz,z=m);")
	(apply-macete-with-minor-premises alternate-iota-free-characterization-of-sep%deg)
	direct-and-antecedent-inference-strategy
	(contrapose "with(m:zz,v,u:pp,not(approx(u,v,m)));")
	simplify)
       (instantiate-existential ("sep%deg(u,v)")))))

    )))