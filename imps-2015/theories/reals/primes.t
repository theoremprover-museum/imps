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


(herald primes)

(def-constant divides
  "lambda(a,b:rr, #(b/a,zz))"
  (theory h-o-real-arithmetic))

(def-parse-syntax divides
  (left-method infix-operator-method)
  (binding 95))

(def-print-syntax divides
  (token " divides ")
  (method present-binary-infix-operator)
  (binding 95))

(def-theorem divisibility-lemma 
  "forall(a,b:zz, not(a=0) implies (a divides b iff forsome(k:zz, b = k*a)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant (0) divides)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(k:zz, b/a=k)")
    (antecedent-inference "with(p:prop,forsome(k:zz,p));")
    (incorporate-antecedent "with(r:rr,#(r,zz));")
    (backchain "with(k:zz,r:rr,r=k);")
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(k:zz,r:rr,r=k);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("k"))
    (instantiate-existential ("b/a"))
    (cut-with-single-formula "b/a=k")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify    
    )))


(def-theorem divides-implies-le
  "forall(x,y:rr, 0<x and 0<y and x divides y implies x<=y)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant (0) divides)
    direct-and-antecedent-inference-strategy
    (force-substitution "x<=y" "0<=x*(y/x-1)" (0))
    (move-to-sibling 1)
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    simplify
    (cut-with-single-formula "0<y/x")
    simplify
    simplify
    (apply-macete-with-minor-premises positivity-of-inverse)

    )))


(def-constant positive%prime
  "lambda(m:zz, 1<m and forall(a:zz, 0<a and a divides m implies (a=1 or a=m)))"
  (theory h-o-real-arithmetic))

(def-constant no%factors%between
  "lambda(a,b:zz,c:rr, forall(k:zz, a<=k and k<=b implies not(k divides c)))"
  (theory h-o-real-arithmetic))

(def-theorem positive-prime-characterization
  "forall(m:zz,
     positive%prime(m)
       iff 
      (2<=m and no%factors%between(2,m-1,m)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    simplify
    (instantiate-universal-antecedent "with(p:prop,forall(a:zz,p));" ("k"))
    (simplify-antecedent "with(k:zz,not(0<k));")
    (simplify-antecedent "with(k:zz,2<=k);")
    (simplify-antecedent "with(m,k:zz,k<=m-1);")
    simplify
    (contrapose "with(m,a:zz,a divides m);")
    (case-split ("a<m"))
    (backchain "with(p:prop,forall(k:zz,p));")
    simplify
    (contrapose "with(m,a:zz,not(a<m));")
    (cut-with-single-formula "a<=m")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises divides-implies-le)
    simplify
    simplify

    )))

  
(def-theorem no-factors-recursion
  "forall(a,b:zz,theta:rr,
      a<=b
       implies 
      no%factors%between(a,b,theta)
       iff 
      (not(a divides theta) and no%factors%between(a+1,b,theta)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally no%factors%between)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(k:zz,p));")
    simplify
    (backchain "with(p:prop,forall(k:zz,p));")
    simplify
    (cut-with-single-formula "k=a or a+1<=k")
    (antecedent-inference "with(p:prop,p or p);")
    simplify
    (backchain "with(p:prop,forall(k_$0:zz,p));")
    simplify
    simplify
    )))

(def-theorem no-factors-base
  "forall(a,b:zz,theta:rr, b<a implies (no%factors%between(a,b,theta) iff truth))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant (0) no%factors%between)
    direct-and-antecedent-inference-strategy
    (simplify-antecedent "with(a,b:zz,b<a);")    
    )))


(def-compound-macete crude-primality-test
  (sequential
   positive-prime-characterization
   (repeat
    no-factors-recursion
    no-factors-base
    divides-equation_h-o-real-arithmetic
    simplify)))

(def-theorem primes-exist
  "positive%prime(37)"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete crude-primality-test)
    )))

(def-theorem primality-test-refinement-lemma
  "forall(a,n:zz,
    1<=a and n<a^2 and a<=n-1
     implies 
    no%factors%between(2,a,n) iff no%factors%between(2,n-1,n))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant-globally no%factors%between)
    direct-and-antecedent-inference-strategy

    (block
      (script-comment "One direction of the biconditional.")
      (cut-with-single-formula "k<=a or a<k")
      (antecedent-inference "with(p:prop,p or p);")
      (backchain "with(p:prop,forall(k_$0:zz,p));")
      direct-and-antecedent-inference-strategy
      (contrapose "with(p:prop,forall(k_$0:zz,p));")
      (instantiate-existential ("n/k"))
      (cut-with-single-formula "0<n/k")
      (cut-with-single-formula "1=n/k or 2<=n/k")
      (antecedent-inference "with(p:prop,p or p);")
      (contrapose "with(r:rr,1=r);")
      (apply-macete-with-minor-premises fractional-expression-manipulation)
      simplify
      (incorporate-antecedent "with(n,k:zz,k divides n);")
      (unfold-single-defined-constant (0) divides)
      simplify
      (apply-macete-with-minor-premises fractional-expression-manipulation)
      simplify
      (cut-with-single-formula "not(a^2<=n)")
      (move-to-sibling 1)
      simplify
      (contrapose "with(p:prop,not(p));")
      (force-substitution "n" "(n/k)*k" (0))
      (force-substitution "a^2" "a*a" (0))
      (apply-macete-with-minor-premises monotone-product-lemma)
      simplify
      simplify
      simplify
      (unfold-single-defined-constant (0) divides)
      simplify
      (incorporate-antecedent "with(n,k:zz,k divides n);")
      (unfold-single-defined-constant (0) divides)
      simplify
      simplify)

    (block
      (script-comment "The other direction now.")
      (cut-with-single-formula "positive%prime(n)")
      (incorporate-antecedent "with(n:zz,positive%prime(n));")
      (unfold-single-defined-constant (0) positive%prime)
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent 
       "with(p:prop,forall(a:zz,p and p implies (p or p)));"
       ("k_$0"))
      (simplify-antecedent "with(p:prop,not(p));")
      (simplify-antecedent "with(k_$0:zz,k_$0=1);")
      (simplify-antecedent "with(n,k_$0:zz,k_$0=n);")
      (apply-macete-with-minor-premises positive-prime-characterization)
      direct-and-antecedent-inference-strategy
      simplify
      (unfold-single-defined-constant (0) no%factors%between))

    )))


(def-theorem primality-test-refinement
  "forall(n:zz,
     positive%prime(n)
      iff 
     (n=2
      or 
     forsome(a:zz,
       1<=a and n<a^2 and a<=n-1 and no%factors%between(2,a,n))))"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    
    (apply-macete-with-minor-premises primality-test-refinement-lemma)
    (apply-macete-with-minor-premises positive-prime-characterization)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("n-1"))
    simplify
    simplify
    (cut-with-single-formula "3*n<=n^2")
    simplify
    (force-substitution "n^2" "n*n" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    simplify
    simplify
    simplify
    simplify
    simplify
    (apply-macete-with-minor-premises no-factors-base)
    )))


(def-theorem 3rd-mersenne-number-is-prime
  "positive%prime(2^2^3+1)"
  (theory h-o-real-arithmetic)
  (proof
   (
    simplify
    (apply-macete-with-minor-premises primality-test-refinement)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("17"))
    simplify
    simplify
    simplify
    (block 
      (let-macete no-factors-reduction
		  (repeat no-factors-recursion
			  no-factors-base
			  divides-equation_h-o-real-arithmetic
			  simplify))
      (apply-macete $no-factors-reduction))
    )))

(comment
 (def-theorem 4th-mersenne-number-is-prime
  "positive%prime(2^2^4+1)"
  (theory h-o-real-arithmetic)
  (proof
   (
    simplify
    (apply-macete-with-minor-premises primality-test-refinement)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("260"))
    simplify
    simplify
    simplify
    (block 
      (let-macete no-factors-reduction
		  (repeat no-factors-recursion
			  no-factors-base
			  divides-equation_h-o-real-arithmetic
			  simplify))
      (apply-macete $no-factors-reduction))
    ))))

(def-theorem prod-decomposition
  "forall(a,b,k:zz, f:[zz,zz], 
           a<=k and k<=b 
            implies 
          prod(a,b,f)==prod(a,k,f)*prod(k+1,b,f))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (induction integer-inductor ("b"))
    (backchain "with(p:prop,p implies p);")
    direct-and-antecedent-inference-strategy
    
    )))
  
(def-theorem prod-integer-definedness 
  "forall(m,n:zz,f:[zz,zz],forall(k:zz,m<=k and k<=n implies #(f(k),zz)) 
             implies
            #(prod(m,n,f),zz))"
  (theory h-o-real-arithmetic)
  
  (proof
   
   (
    
    
    (prove-iteration-operator-definedness "m" "n" prod)

    )))

(def-theorem product-is-divisible-by-factors
  "forall(a,b,k:zz, f:[zz,zz], a<=k and k<=b and
           forall(x:zz, a<=x and x<=b implies #(f(x))) and not(f(k)=0)
            implies
           f(k) divides prod(a,b,f))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "prod(a,b,f)=prod(a,k,f)*prod(k+1,b,f)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)") 
      (backchain "with(r:rr,r=r);")
      (unfold-single-defined-constant (0) prod) 
      simplify
      (unfold-single-defined-constant (0) divides)
      simplify
       sort-definedness
       (block 
	(script-comment "`sort-definedness' at (0)")
	(apply-macete-with-minor-premises prod-integer-definedness)
	direct-and-antecedent-inference-strategy simplify
	)
      (block 
	(script-comment "`sort-definedness' at (1)")
	(apply-macete-with-minor-premises prod-integer-definedness)
	direct-and-antecedent-inference-strategy simplify
	) )
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises prod-decomposition) simplify
      )

    )))


(def-theorem addition-preserves-divisibility
  "forall(a,b,c:rr, a divides b and a divides c implies a divides b+c)"
  (theory h-o-real-arithmetic)
  (proof
   (

    unfold-defined-constants
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x,y:zz, c*a^[-1]=y and b*a^[-1]=x)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(x,y:zz,p));")
      (incorporate-antecedent "with(p:prop,p and p);") simplify
      direct-and-antecedent-inference-strategy (backchain "with(x:zz,b,a:rr,a^[-1]*b=x);")
      (backchain "with(y:zz,c,a:rr,a^[-1]*c=y);") simplify
      )
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (instantiate-existential ("b/a" "c/a")) 
      simplify
      )    )))

(def-theorem subtraction-preserves-divisibility
  "forall(a,b,c:rr, a divides b and a divides c implies a divides b-c)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (force-substitution "b-c" "b+(-c)" (0))
    (apply-macete-with-minor-premises addition-preserves-divisibility)
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (force-substitution "(-c)/a" "[-1]*(c/a)" (0))
    simplify
    simplify
    simplify
    )))

(def-theorem multiplication-preserves-divisibility
  "forall(a,b:rr, c:zz, a divides b implies a divides c*b)"
  (theory h-o-real-arithmetic)
  (proof
   (
    

    unfold-defined-constants
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x:zz, a^[-1]*b=x)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(x:zz,p));")
      (force-substitution "c*a^[-1]*b" "c*(a^[-1]*b)" (0))
      (block 
	(script-comment "`force-substitution' at (0)") (backchain "with(x:zz,r:rr,r=x);")
	simplify
	)
      (block 
	(script-comment "`force-substitution' at (1)")
	(weaken (0)) simplify
	) )
    (instantiate-existential ("a^[-1]*b"))

    )))

(def-theorem non-divisibility-into-1
  "forall(a,b:rr, 1<a  implies not(a divides 1))"

  (theory h-o-real-arithmetic)
  (proof
   (
    

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "0<1/a and 1/a<1")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (antecedent-inference "with(p:prop,p and p);")
    (contrapose "with(r:rr,r<1);")
    (weaken (2))
    simplify

    )))

(def-theorem addition-of-one-destroys-divisibility
  "forall(a,b:rr, 1<a and a divides b implies not(a divides b+1))"
  (theory  h-o-real-arithmetic)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not(a divides 1)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises non-divisibility-into-1)
    (contrapose "with(p:prop,not(p));")
    (force-substitution "1" "(b+1)-b" (0))
    (apply-macete-with-minor-premises subtraction-preserves-divisibility)
    direct-and-antecedent-inference-strategy
    simplify
    )))

(def-theorem divisibility-is-transitive
  "forall(a,b,c:rr, a divides b and b divides c implies a divides c)"
  (theory h-o-real-arithmetic)
  (proof 
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x,y:zz,c/b=x and b/a=y)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(x,y:zz,p));")
      (force-substitution "c/a" "x*y" (0)) simplify
      (block 
	(script-comment "`force-substitution' at (1)") insistent-direct-inference
	(incorporate-antecedent "with(p:prop,p and p);")
	(apply-macete-with-minor-premises fractional-expression-manipulation) simplify
	direct-and-antecedent-inference-strategy
	(backchain-backwards "with(c,b:rr,x:zz,x*b=c);")
	(backchain-backwards "with(b,a:rr,y:zz,y*a=b);") (weaken (0 1)) simplify
	) )
    (instantiate-existential ("c/b" "b/a"))

    )))

(def-theorem self-divisibility
  "forall(k:rr, not(k=0) implies k divides k)"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (
    
    (unfold-single-defined-constant (0) divides)
    simplify

    )))


(comment
 ;;This is now moved to reals-supplements.t, where by rights it belongs 
 ;;We are going to use complete induction more frequently, so let's
 ;;make an inductor which does it:

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
   (theory h-o-real-arithmetic)))

(def-theorem divisibility-by-prime
  "forall(k:zz, 2<=k implies forsome(j:zz, positive%prime(j) and j divides k))"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    
    (induction complete-inductor ("k"))
    (case-split ("positive%prime(m)"))
    (instantiate-existential ("m"))
    (unfold-single-defined-constant (0) divides)
    simplify
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises positive-prime-characterization)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) no%factors%between)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,forall(j:zz,p or p));")
    (instantiate-universal-antecedent "with(p:prop,forall(k:zz,p));" ("k"))
    (simplify-antecedent "with(p:prop,not(p));")
    (instantiate-existential ("j"))
    (apply-macete-with-minor-premises divisibility-is-transitive)
    (instantiate-existential ("k"))

    )))

(def-theorem product-gte-1
  "forall(f:[zz,rr], 
           a,b:zz, forall(k:zz,a<=k and k<=b implies 1<=f(k))
            implies
           1<=prod(a,b,f))"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    
    direct-and-antecedent-inference-strategy
    (case-split ("a<=b"))
    (induction integer-inductor ())
    (force-substitution "1" "1*1" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    direct-inference
    (backchain "with(p:prop,forall(k:zz,p));")
    simplify
    (backchain "with(p:prop,p implies p);")
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    (unfold-single-defined-constant (0) prod)
    simplify
    )))

(def-theorem infinity-of-primes
  "forall(k:zz, forsome(m:zz, k<=m and positive%prime(m)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (cut-with-single-formula "forall(k:zz,0<=k implies forsome(m:zz,k<=m and positive%prime(m)))")
    (block
     (script-comment "`cut-with-single-formula' at (0)")
     direct-and-antecedent-inference-strategy
     (case-split ("0<=k"))
     (backchain "with(p:prop,forall(k:zz,p));")
     (block
      (script-comment "`case-split' at (2)")
      (instantiate-universal-antecedent "with(p:prop,forall(k:zz,p));"
					("0"))
      (simplify-antecedent "not(0<=0);")
      (block
       (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0)")
       (instantiate-existential ("m"))
       simplify)))
    (block
     (script-comment "`cut-with-single-formula' at (1)")
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "not(k<0)")
     (move-to-sibling 1)
     simplify
     (block
      (script-comment "`cut-with-single-formula' at (0)")
      (contrapose "with(p:prop,not(p));")
      (cut-with-single-formula "not(positive%prime(prod(2,k,lambda(j:zz,j))+1))")
      (move-to-sibling 1)
      (block
       (script-comment "`cut-with-single-formula' at (1)")
       (backchain "with(p:prop,forall(m:zz,p));")
       (block
	(script-comment "`backchain' at (0)")
	(weaken (0))
	unfold-defined-constants
	(cut-with-single-formula "k=0 or k=1 or 2<=k ")
	(move-to-sibling 1)
	simplify
	(block
	 (script-comment "`cut-with-single-formula' at (0)")
	 (antecedent-inference "with(p:prop,p or p or p);")
	 simplify
	 simplify
	 (block
	  (script-comment "`antecedent-inference' at (2)")
	  simplify
	  (cut-with-single-formula "k<=prod(2,[-1]+k,lambda(j:zz,j))*k")
	  simplify
	  (block
	   (script-comment "`cut-with-single-formula' at (1)")
	   simplify
	   (weaken (1))
	   (apply-macete-with-minor-premises product-gte-1)
	   beta-reduce-repeatedly
	   simplify))))
       (block
	(script-comment "`backchain' at (1)")
	sort-definedness
	(apply-macete-with-minor-premises prod-integer-definedness)
	beta-reduce-repeatedly))
      (block
       (script-comment "`cut-with-single-formula' at (0)")
       (contrapose "with(p:prop,not(p));")
       (instantiate-theorem divisibility-by-prime
			    ("prod(2,k,lambda(j:zz,j))+1"))
       (block
	(script-comment "`instantiate-theorem' at (0 0)")
	(contrapose "with(r:rr,not(2<=r));")
	simplify
	(apply-macete-with-minor-premises product-gte-1)
	simplify)
       (block
	(script-comment "`instantiate-theorem' at (0 1 0 0)")
	(contrapose "with(r:rr,j:zz,j divides r);")
	(apply-macete-with-minor-premises addition-of-one-destroys-divisibility)
	direct-and-antecedent-inference-strategy
	(block
	 (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	 (incorporate-antecedent "with(j:zz,positive%prime(j));")
	 (apply-macete-with-minor-premises positive-prime-characterization)
	 simplify)
	(block
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	 (force-substitution "j"
			     "lambda(j:zz,j)(j)"
			     (0))
	 (block
	  (script-comment "`force-substitution' at (0)")
	  (apply-macete-with-minor-premises product-is-divisible-by-factors)
	  direct-and-antecedent-inference-strategy
	  simplify
	  (block
	   (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	   (contrapose "with(j:zz,positive%prime(j));")
	   (backchain "with(p:prop,forall(m:zz,p));")
	   simplify)
	  beta-reduce-repeatedly
	  simplify)
	 beta-reduce-repeatedly)))))

    )))

(def-constant ideal
  "lambda(x:sets[zz], 
       nonempty_indic_q{x} and
       forall(a,b,c:zz, a in x and b in x 
        implies 
       (a+b) in x and c*a in x))"
  (theory h-o-real-arithmetic))

(def-theorem divisibility-preserves-ideal-membership
  "forall(x:sets[zz], k,m:zz , ideal(x) and k in x and k divides m implies m in x)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant (0) ideal)
    (unfold-single-defined-constant (0) divides)
    direct-and-antecedent-inference-strategy
    (force-substitution "m" "(m/k)*k" (0))
    (backchain "with(p:prop,forall(a,b,c:zz,p));")
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$0"))
    simplify
    (simplify-antecedent "with(k,m:zz,#(m/k,zz));")
    definedness
    simplify
    (simplify-antecedent "with(k,m:zz,#(m*k^[-1],zz));")
    )))

(def-constant princ%ideal
  "lambda(k:zz, if(k=0, singleton{0}, indic{n:zz, k divides n}))"
  (theory h-o-real-arithmetic))

(def-theorem princ%ideal-is-ideal
  "forall(k:zz, ideal(princ%ideal(k)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    unfold-defined-constants
    direct-inference
    (case-split ("k=0"))
    simplify-insistently
    (block 
      (script-comment "`case-split' at (2)") simplify-insistently
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(instantiate-existential ("k")) (unfold-single-defined-constant (0) divides) simplify
	)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0 0 0 0)")
	(apply-macete-with-minor-premises addition-preserves-divisibility)
	direct-and-antecedent-inference-strategy
	)
      (apply-macete-with-minor-premises multiplication-preserves-divisibility)
      )
    )))

(def-theorem princ%ideal-contains-its-generator
  "forall(k:zz, k in princ%ideal(k))"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) princ%ideal)
    (case-split ("k=0"))
    simplify
    simplify
    (apply-macete-with-minor-premises self-divisibility)
    )))


;; The following has been moved to reals-supplements where it belongs.

;(def-constant mod
;  "lambda(a,b:rr, a-b*floor(a/b))"
;  (theory h-o-real-arithmetic))

;(def-parse-syntax mod
;  (left-method infix-operator-method)
;  (binding 99))

;(def-print-syntax mod
;  (token " mod ")
;  (method present-binary-infix-operator)
;  (binding 99))

;(def-theorem mod-of-negative
;  "forall(a,b:rr, mod(-b,-a)==-mod(b,a))"
;  (theory h-o-real-arithmetic)
;  (proof
;   (
     
;    (unfold-single-defined-constant-globally mod)
;    simplify
;    )))

(def-theorem characterization-of-divisibility
  "forall(a,b:rr, a divides b iff b mod a = 0)"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "floor(b/a)=b/a")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises floor-characterization)
    simplify
    (incorporate-antecedent "with(r:rr,z:zz,z=r);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (cut-with-single-formula "floor(b/a)=b/a")
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    )))

(def-theorem division-with-remainder
  "forall(a,c:rr,
     0<a
      implies 
     a divides c-(c mod a) and 0<=c mod a and c mod a<a)"
  (theory h-o-real-arithmetic)
  (proof

   (

;;;proof used to be before d-r-convergence was added to floor:

;;;    (unfold-single-defined-constant-globally mod)
;;;    direct-and-antecedent-inference-strategy
;;;    (unfold-single-defined-constant (0) divides)
;;;    simplify
;;;    (instantiate-theorem floor-definedness ("c*a^[-1]"))
;;;    (move-to-ancestor 1)
;;;    (cut-with-single-formula "forsome(p:zz, floor(c/a)=p)")
;;;    (antecedent-inference "with(p:prop,forsome(p:zz,with(p:prop,p)));")
;;;    (backchain "with(p,z:zz,z=p);")
;;;    (backchain "with(p,z:zz,z=p);")
;;;    (backchain "with(p,z:zz,z=p);")
;;;    (incorporate-antecedent "with(p,z:zz,z=p);")
;;;    (apply-macete-with-minor-premises floor-characterization)
;;;    (apply-macete-with-minor-premises fractional-expression-manipulation)
;;;    simplify
;;;    direct-and-antecedent-inference-strategy
;;;    (unfold-single-defined-constant (0) divides)
;;;    simplify
;;;    (instantiate-existential ("floor(c/a)"))


    (unfold-single-defined-constant-globally mod)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    (cut-with-single-formula "forsome(p:zz, floor(c/a)=p)")
    (antecedent-inference "with(p:prop,forsome(p:zz,with(p:prop,p)));")
    (backchain "with(p,z:zz,z=p);")
    (backchain "with(p,z:zz,z=p);")
    (backchain "with(p,z:zz,z=p);")
    (incorporate-antecedent "with(p,z:zz,z=p);")
    (apply-macete-with-minor-premises floor-characterization)
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) divides)
    simplify
    (instantiate-existential ("floor(c/a)"))
    simplify

    )))

(comment
 (def-theorem mod-preserves-ideal-membership
  "forall(x:sets[zz], k,a:zz , ideal(x) and k in x and a in x  and 0<k 
                      implies
                     (a mod k) in x)"
  (theory h-o-real-arithmetic)
  (proof
   (

    ))))

(def-theorem every-non-trivial-ideal-contains-a-positive-element
  "forall(ide:sets[zz], 
          ideal(ide) 
           implies 
          (not(ide=singleton{0}) iff forsome(a:zz,0<a and a in ide)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,forall(a:zz,p));")
    (cut-with-single-formula "0<x_$2 or 0<-x_$2")
    (antecedent-inference "with(p:prop,p or p);")
    auto-instantiate-existential
    auto-instantiate-existential
    simplify
    (incorporate-antecedent "with(ide:sets[zz],ideal(ide));")
    (unfold-single-defined-constant (0) ideal)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(a,b,c:zz,p));")
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$0"))
    simplify
    (incorporate-antecedent "with(ide:sets[zz],ideal(ide));")
    (unfold-single-defined-constant (0) ideal)
    direct-and-antecedent-inference-strategy
    (force-substitution "x_$1" "0*x_$0" (0))
    (backchain "with(p:prop,forall(a,b,c:zz,p));")
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x_$0"))
    simplify
    (contrapose "with(a:zz,ide:sets[zz],a in ide);")
    (backchain "with(f,ide:sets[zz],ide=f);")
    (apply-macete-with-minor-premises indicator-facts-macete)
    simplify

    )))


(def-theorem principal-ideal-theorem
  "forall(x:sets[zz], ideal(x) iff forsome(k:zz,x=princ%ideal(k) and 0<=k))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (block
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
     (case-split ("forsome(a:zz, a in x and 0<a)"))
     (block
      (script-comment "`case-split' at (1)")
      (antecedent-inference "with(p:prop,forsome(a:zz,p));")
      (instantiate-theorem well-ordering-for-integers
			   ("lambda(j:zz,j in x and 0<j  )"))
      (block
       (script-comment "`instantiate-theorem' at (0 0 0)")
       (instantiate-universal-antecedent "with(p:prop,forall(y:zz,p));"
					 ("a"))
       (beta-reduce-antecedent "with(a:zz,x:sets[zz],not(lambda(j:zz,j in x and 0<j)(a)));"))
      (block
       (script-comment "`instantiate-theorem' at (0 0 1)")
       (contrapose "with(p:prop,forall(n:zz,p));")
       beta-reduce-repeatedly
       (instantiate-existential ("0"))
       simplify)
      (block
       (script-comment "`instantiate-theorem' at (0 1 0 0)")
       (beta-reduce-antecedent "with(x:sets[zz],u:zz,
  forall(v:zz,
    v<u implies not(lambda(j:zz,j in x and 0<j)(v))));")
       (beta-reduce-antecedent "with(u:zz,x:sets[zz],lambda(j:zz,j in x and 0<j)(u));")
       (instantiate-existential ("u"))
       (block
	(script-comment "`instantiate-existential' at (0 0)")
	(unfold-single-defined-constant (0) princ%ideal)
	simplify
	(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	simplify-insistently
	direct-and-antecedent-inference-strategy
	(block
	 (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
	 (contrapose "with(p:prop,forall(v:zz,p));")
	 (instantiate-existential ("x_$2 mod u"))
	 (instantiate-theorem division-with-remainder
			      ("u" "x_$2"))
	 (block
	  (script-comment "`instantiate-existential' at (0 1 0)")
	  (unfold-single-defined-constant (0)
                                                                 
					  mod)
	  (incorporate-antecedent "with(x:sets[zz],ideal(x));")
	  (unfold-single-defined-constant (0)
                                                                 
					  ideal)
	  direct-and-antecedent-inference-strategy
	  simplify
	  (backchain "with(p:prop,forall(a,b,c:zz,p));")
	  direct-and-antecedent-inference-strategy
	  (backchain "with(p:prop,forall(a,b,c:zz,p));")
	  direct-inference
	  simplify-insistently
	  (instantiate-existential ("u")))
	 (block
	  (script-comment "`instantiate-existential' at (0 1 1)")
	  simplify
	  sort-definedness
	  (instantiate-theorem floor-definedness
			       ("x_$2*u^[-1]"))
	  simplify
	  (instantiate-theorem division-with-remainder
			       ("u" "x_$2"))
	  (case-split ("0=x_$2 mod u"))
	  (move-to-sibling 2)
	  simplify
	  (block
	   (script-comment "`case-split' at (1)")
	   (contrapose "with(p:prop,not(p));")
	   (incorporate-antecedent "with(r:rr,0=r);")
	   (apply-macete-with-minor-premises characterization-of-divisibility)
	   direct-and-antecedent-inference-strategy))
	 (block
	  (script-comment "`instantiate-existential' at (1)")
	  unfold-defined-constants
	  simplify))
	(block
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0)")
	 sort-definedness
	 (assume-theorem floor-definedness)
	 simplify
	 (force-substitution "x_$1" "(x_$1/u)*u" (0))
	 (block
	  (script-comment "`force-substitution' at (0)")
	  (incorporate-antecedent "with(x:sets[zz],ideal(x));")
	  (unfold-single-defined-constant (0)
                                                                 
					  ideal)
	  direct-and-antecedent-inference-strategy
	  (backchain "with(p:prop,forall(a,b,c:zz,p));")
	  (block
	   (script-comment "`backchain' at (0)")
	   direct-inference
	   (instantiate-existential ("a")))
	  (block
	   (script-comment "`backchain' at (1)")
	   (incorporate-antecedent "with(x_$1,u:zz,u divides x_$1);")
	   (unfold-single-defined-constant (0)
                                                                 
					   divides)
	   simplify))
	 simplify))
       simplify))
     (block
      (script-comment "`case-split' at (2)")
      (case-split ("x=singleton{0}"))
      (block
       (script-comment "`case-split' at (1)")
       (backchain "with(f,x:sets[zz],x=f);")
       (instantiate-existential ("0"))
       (unfold-single-defined-constant (0) princ%ideal)
       simplify)
      (block
       (script-comment "`case-split' at (2)")
       (incorporate-antecedent "with(f,x:sets[zz],not(x=f));")
       (apply-macete-with-minor-premises every-non-trivial-ideal-contains-a-positive-element)
       direct-and-antecedent-inference-strategy
       (contrapose "with(p:prop,not(p));")
       auto-instantiate-existential)))
    (block
     (script-comment "`direct-and-antecedent-inference-strategy' 
at (0 1 0 0)")
     (backchain "with(k:zz,0<=k);")
     (backchain "with(k:zz,0<=k);")
     (backchain "with(f,x:sets[zz],x=f);")
     (apply-macete-with-minor-premises princ%ideal-is-ideal))
    )))


(def-constant generator
  "lambda(x:sets[zz], iota(k:zz,x=princ%ideal(k) and 0<=k))"
  (theory h-o-real-arithmetic))

(def-theorem iota-free-characterization-of-generator
  "forall(x:sets[zz],k:zz, generator(x)=k iff (0<=k and x=princ%ideal(k)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant (0) generator)
    (label-node l_0)
    direct-and-antecedent-inference-strategy
    (jump-to-node l_0)
    (for-nodes
     (unsupported-descendents)
     (if (matches? "with(p:prop,p)" "with(u:zz,p:prop,iota(k:zz,p)=u)")
	 (block
	  
	  (contrapose "with(k,z:zz,z=k);")
	  (eliminate-defined-iota-expression 0 w)
	  (simplify-antecedent "with(p:prop,not(p));"))
       (if (matches? "with(u:zz,p:prop,iota(k:zz,p)=u)")
	   (apply-macete-with-minor-premises eliminate-iota-macete)
	 (skip))))
    (backchain "with(f:sets[zz],x:sets[rr],x=f);")
    (backchain "with(f:sets[zz],x:sets[rr],x=f);")
    direct-and-antecedent-inference-strategy
    (weaken (0 3))
    (incorporate-antecedent "with(f:sets[zz],f=f);")
    (unfold-single-defined-constant-globally princ%ideal)
    (label-node l_1)
    (case-split ("k=0" "b=0"))
    (jump-to-node l_1)
    (for-nodes
     (unsupported-descendents)
     (block
      
      simplify
      (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
      simplify-insistently
      direct-and-antecedent-inference-strategy))

    (cut-with-single-formula "b<=k and k<=b")
    simplify
    (apply-macete-with-minor-premises divides-implies-le)
    simplify
    direct-and-antecedent-inference-strategy
    (backchain "with(b,k:zz,
  forall(x_$2:zz,k divides x_$2 implies b divides x_$2));")
    (apply-macete-with-minor-premises self-divisibility)
    (backchain "with(k,b:zz,
  forall(x_$1:zz,b divides x_$1 implies k divides x_$1));")
    (apply-macete-with-minor-premises self-divisibility)
    (instantiate-existential ("b"))
    (apply-macete-with-minor-premises self-divisibility)
    (instantiate-universal-antecedent "with(p:prop,forall(x_$2:zz,p));" ("k"))
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises self-divisibility)



    )))

(def-theorem definedness-of-generator
  "forall(x:sets[zz],k:zz, ideal(x) implies #(generator(x)))"
  (theory h-o-real-arithmetic)
  (usages d-r-convergence)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(k:zz, generator(x)=k)")
    (antecedent-inference "with(p:prop,forsome(k:zz,p));")
    (apply-macete-with-minor-premises iota-free-characterization-of-generator)
    (instantiate-theorem principal-ideal-theorem ("x"))
    auto-instantiate-existential

    )))

(def-theorem divisibility-characterization-of-generator
  "forall(x:sets[zz], 
     ideal(x) and not(x = singleton{0})
      implies 
     forall(k:zz, k in x iff generator(x) divides k))"
  (theory h-o-real-arithmetic)
  reverse
  (proof

   (
    
    direct-inference
    direct-inference
    (cut-with-single-formula "forsome(k:zz, generator(x_$1)=k)")
    (antecedent-inference "with(p:prop,forsome(k:zz,p));")
    (backchain "with(k,z:zz,z=k);")
    (incorporate-antecedent "with(k,z:zz,z=k);")
    (apply-macete-with-minor-premises iota-free-characterization-of-generator)
    (case-split ("k=0"))
    (unfold-single-defined-constant (0) princ%ideal)
    simplify
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f,x_$1:sets[zz],x_$1=f);")
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (unfold-single-defined-constant (0) princ%ideal)
    simplify-insistently
    (unfold-single-defined-constant (0) princ%ideal)
    (apply-macete-with-minor-premises divisibility-preserves-ideal-membership)
    (instantiate-existential ("k"))
    (backchain "with(f,x_$1:sets[zz],x_$1=f);")
    (unfold-single-defined-constant (0) princ%ideal)
    simplify
    (apply-macete-with-minor-premises self-divisibility)
    (instantiate-existential ("generator(x_$1)"))
    simplify

    )))


(def-theorem integer-combinations-form-an-ideal
  "forall(a,b:zz, ideal(indic{x:zz,  forsome(r,s:zz, x=r*b+s*a)}))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant (0) ideal)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      (instantiate-existential ("a")) simplify-insistently (instantiate-existential ("0" "1"))
      simplify
      )
    (incorporate-antecedent
     "with(a_$0,a,b:zz,
  a_$0 in indic{x:zz,  forsome(r,s:zz,x=r*b+s*a)});"
     )
    (incorporate-antecedent
     "with(b_$0,a,b:zz,
  b_$0 in indic{x:zz,  forsome(r,s:zz,x=r*b+s*a)});"
     )
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("r_$0+r" "s_$0+s"))
    simplify
    (block 
      (script-comment "`simplify' at (0)")
      (backchain "with(a,s_$0,b,r_$0,b_$0:zz,b_$0=r_$0*b+s_$0*a);")
      (backchain "with(a,s,b,r,a_$0:zz,a_$0=r*b+s*a);") (weaken (0 1)) simplify
      )
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0 1 0 0)")
      (incorporate-antecedent
       "with(a_$0,a,b:zz,
  a_$0 in indic{x:zz,  forsome(r,s:zz,x=r*b+s*a)});"
       )
      simplify-insistently direct-and-antecedent-inference-strategy
      (instantiate-existential ("c_$0*r" "c_$0*s"))
      (cut-with-single-formula "0<c_$0 or c_$0=0 or c_$0<0")
      (antecedent-inference "with(p:prop,p or p or p);") (move-to-ancestor 2)
      (move-to-descendent (1)) simplify simplify simplify simplify
      )
    )))

(def-constant gcd
  "lambda(a,b:zz, generator(indic{x:zz, forsome(r,s:zz, x=r*a + s*b)}))"
  (theory h-o-real-arithmetic))

(def-theorem symmetry-of-gcd
  "forall(a,b:zz, gcd(a,b)=gcd(b,a))"
  (theory h-o-real-arithmetic)
  (proof
   (
    

    (unfold-single-defined-constant-globally gcd)
    direct-inference
    (force-substitution 
     "forsome(r,s:zz,x=r*a+s*b)"
     "forsome(r,s:zz,x=r*b+s*a)" (0))
    simplify
    (apply-macete-with-minor-premises definedness-of-generator)
    (apply-macete-with-minor-premises integer-combinations-form-an-ideal)
    (label-node l_0)
    direct-and-antecedent-inference-strategy
    (jump-to-node l_0)
    (for-nodes
     (unsupported-descendents)
     (block
       (instantiate-existential ("s" "r"))
       simplify))
    )))

(def-theorem gcd-usually-is-non-zero
  "forall(a,b:zz, gcd(a,b)=0 iff (a =0 and b=0))"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    (unfold-single-defined-constant (0) gcd)
    (apply-macete-with-minor-premises iota-free-characterization-of-generator)
    (unfold-single-defined-constant (0) princ%ideal)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (let-script prove-cut 3
		(
		 (contrapose "with(p:prop,forall(x:zz,p))")
		 (instantiate-existential ($1))
		 (instantiate-existential ($2 $3))
		 simplify))
    ($prove-cut "a" "1" "0")
    ($prove-cut "b" "0" "1")


    (simplify-antecedent "with(r:rr,x_$2:zz,x_$2=r+r);")
    (instantiate-existential ("0" "0"))
    simplify
    )))

(def-theorem characterization-of-gcd
  "forall(a,b:zz,
     not(b=0)
       implies
     gcd(a,b) divides a
      and 
     gcd(a,b) divides b
      and 
     forall(k:zz,
       k divides a and k divides b implies k divides gcd(a,b)))"
  (theory h-o-real-arithmetic)
  (proof
   (



    (unfold-single-defined-constant (0 1) gcd)
    (apply-macete-with-minor-premises rev%divisibility-characterization-of-generator)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("1" "0"))
    simplify
    (instantiate-existential ("0" "1"))
    simplify
    (case-split ("k=0"))
    (contrapose "with(b,k:zz,k divides b);")
    (unfold-single-defined-constant (0) divides)
    simplify
    (cut-with-single-formula "forsome(k:zz, gcd(a,b)=k)")
    (antecedent-inference "with(p:prop,forsome(k:zz,p));")
    (backchain "with(k_$0,b,a:zz,gcd(a,b)=k_$0);")
    (incorporate-antecedent "with(k_$0,b,a:zz,gcd(a,b)=k_$0);")
    (unfold-single-defined-constant (0) gcd)
    (apply-macete-with-minor-premises iota-free-characterization-of-generator)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "k_$0 in indic{x:zz,  forsome(r,s:zz,x=r*a+s*b)}")
    (incorporate-antecedent "with(k_$0:zz,f:sets[zz],k_$0 in f);")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (backchain "with(b,s,a,r,k_$0:zz,k_$0=r*a+s*b);")
    (apply-macete-with-minor-premises addition-preserves-divisibility)
    (apply-macete-with-minor-premises multiplication-preserves-divisibility)
    direct-inference
    (backchain "with(f:sets[zz],f=f);")
    (apply-macete-with-minor-premises princ%ideal-contains-its-generator)
    (instantiate-existential ("gcd(a,b)"))
    simplify
    (unfold-single-defined-constant (0) gcd)
    (apply-macete-with-minor-premises definedness-of-generator)
    (apply-macete-with-minor-premises integer-combinations-form-an-ideal)
    (weaken (0))
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,forall(x_$2:zz,p));")
    (instantiate-existential ("b"))
    (weaken (0))
    (apply-macete-with-minor-premises integer-combinations-form-an-ideal)
    )))


(def-constant relatively%prime
  "lambda(a,b:zz, gcd(a,b)=1)"
  (theory h-o-real-arithmetic))

(def-theorem relative-primality-to-primes
  "forall(a,b:zz, positive%prime(b) implies (b divides a or relatively%prime(a,b)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    (unfold-single-defined-constant (0) positive%prime)
    (unfold-single-defined-constant (0) relatively%prime)
    direct-and-antecedent-inference-strategy
    (instantiate-theorem characterization-of-gcd ("a" "b"))
    (simplify-antecedent "with(b:zz,b=0);")
    (instantiate-universal-antecedent
     "with(p:prop,forall(a:zz,p and p implies (p or p)));"
     ("gcd(a,b)"))
    (cut-with-single-formula "0<=gcd(a,b) and not(gcd(a,b)=0)")
    (simplify-antecedent "with(z:zz,not(0<z));")
    (apply-macete-with-minor-premises gcd-usually-is-non-zero)
    simplify
    (cut-with-single-formula "forsome(k:zz,gcd(a,b)=k)")
    (antecedent-inference "with(p:prop,forsome(k:zz,p));")
    (backchain "with(k,z:zz,z=k);")
    (incorporate-antecedent "with(k,z:zz,z=k);")
    (unfold-single-defined-constant (0) gcd)
    (apply-macete-with-minor-premises iota-free-characterization-of-generator)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("gcd(a,b)"))
    (contrapose "with(p:prop,not(p));")
    (backchain-backwards "with(b,z:zz,z=b);")
    )))


(def-theorem relatively-prime-divisors-of-a-product
  "forall(a,b,c:zz,
     relatively%prime(a,b) and a divides b*c
      implies 
     a divides c)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant (0) relatively%prime)
    (unfold-single-defined-constant (0) gcd)
    (apply-macete-with-minor-premises iota-free-characterization-of-generator)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,f:sets[zz],
  forall(x_$1:zz,x_$1 in f implies forsome(r,s:zz,p)));"
				      ("1"))
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises princ%ideal-contains-its-generator)
    (cut-with-single-formula "c=r*c*a+s*(c*b)")
    (backchain "with(b,s,a,r,c:zz,c=r*c*a+s*(c*b));")
    (apply-macete-with-minor-premises addition-preserves-divisibility)
    (apply-macete-with-minor-premises multiplication-preserves-divisibility)
    (apply-macete-with-minor-premises self-divisibility)
    direct-inference
    (contrapose "with(r:rr,a:zz,a divides r);")
    (unfold-single-defined-constant (0) divides)
    simplify
    (cut-with-single-formula "c<0 or c=0 or 0<c")
    (antecedent-inference "with(p:prop,p or p or p);")
    simplify
    simplify
    simplify
    simplify
    (unfold-single-defined-constant (0) princ%ideal)
    )))


(def-theorem prime-divisor-of-a-product
  "forall(a,b,c:zz,
     positive%prime(a) and a divides b*c and not(a divides b)
      implies
     a divides c)"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises relatively-prime-divisors-of-a-product)
    (instantiate-existential ("b"))
    (assume-theorem relative-primality-to-primes)
    (cut-with-single-formula "relatively%prime(b,a)")
    (move-to-sibling 1)
    (backchain "with(p:prop,forall(a,b:zz,p));")
    direct-inference
    (incorporate-antecedent "with(a,b:zz,relatively%prime(b,a));")
    (unfold-single-defined-constant-globally relatively%prime)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises symmetry-of-gcd)

    )))

(def-theorem prime-divisor-of-a-general-product
  "forall(f:[zz,zz],m,n,p:zz,
     positive%prime(p)
      implies 
      p divides prod(m,n,f)
         iff 
      (forsome(j:zz,m<=j and j<=n and p divides f(j))
        and 
      forall(j:zz,m<=j and j<=n implies #(f(j)))))"
  (theory h-o-real-arithmetic)
  (proof
   (
    


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "m<=n")
    (induction trivial-integer-inductor ())
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) prod)
    simplify
    (unfold-single-defined-constant (0) prod)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("m"))
    (cut-with-single-formula "p divides prod(m,t,f) or p divides f(1+t)")
    (antecedent-inference "with(p:prop,p or p);")
    (antecedent-inference "with(p:prop,p implies p);")
    (instantiate-existential ("j"))
    simplify
    (instantiate-existential ("1+t"))
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prime-divisor-of-a-product)
    (instantiate-existential ("prod(m,t,f)"))
    simplify
    (apply-macete-with-minor-premises prod-integer-definedness)
    simplify
    (apply-macete-with-minor-premises prod-definedness-converse)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (contrapose "with(r:rr,p:zz,p divides r);")
    (unfold-single-defined-constant (0) prod)
    simplify
    (apply-macete-with-minor-premises non-divisibility-into-1)
    (incorporate-antecedent "with(p:zz,positive%prime(p));")
    (unfold-single-defined-constant (0) positive%prime)
    simplify
    (cut-with-single-formula "forall(j:zz, m<=j and j<=n implies #(f(j)))")
    simplify
    (apply-macete-with-minor-premises prod-definedness-converse)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("n" "m"))
    
    (block
     (script-comment "This is the trivial case.")
     (case-split ("f(j)=0"))
     (force-substitution "prod(m,n,f)" "prod(m,j,f)*prod(j+1,n,f)" (0))
     (move-to-sibling 1)
     (apply-macete-with-minor-premises prod-decomposition)
     (unfold-single-defined-constant (0) prod)
     (cut-with-single-formula "#(prod(m,j-1,f))")
     (cut-with-single-formula "#(prod(j+1,n,f))")
     simplify
     (apply-macete-with-minor-premises prod-definedness)
     direct-and-antecedent-inference-strategy
     simplify
     (apply-macete-with-minor-premises prod-definedness)
     direct-and-antecedent-inference-strategy
     simplify
     (apply-macete-with-minor-premises divisibility-is-transitive)
     auto-instantiate-existential
     (apply-macete-with-minor-premises product-is-divisible-by-factors)
     direct-and-antecedent-inference-strategy)

    )))

(def-theorem prime-divisor-of-a-power
  "forall(p,q,n:zz, 1<=n and
                   positive%prime(p) and positive%prime(q) and p divides q^n 
                     implies p=q)"
  
  (theory h-o-real-arithmetic)
  (proof
   (

    
    (force-substitution "q^n" "prod(1,n,lambda(j:zz,q))" (0))
    (apply-macete-with-minor-premises prime-divisor-of-a-general-product)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(p:zz,positive%prime(p));")
    (incorporate-antecedent "with(q:zz,positive%prime(q));")
    (unfold-single-defined-constant-globally positive%prime)
    direct-and-antecedent-inference-strategy
    (backchain "with(q:zz,
  forall(a:zz,0<a and a divides q implies (a=1 or a=q)));")
    simplify
    (induction integer-inductor ())
    (backchain-backwards "with(r:rr,r==r);")
    simplify
    )))

(def-theorem prime-divisor-of-a-prime
  "forall(p,q:zz, positive%prime(p) and positive%prime(q) and p divides q
                implies
               p=q)"
  
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally positive%prime)
    direct-and-antecedent-inference-strategy
    (backchain "with(q:zz,
  forall(a:zz,0<a and a divides q implies (a=1 or a=q)));")
    simplify    
    )))

;;;(def-constant prime%power%decomposition
;;;  "lambda(p,r:[zz,zz],n:zz,
;;;           1<=n
;;;            and
;;;           forall(j:zz, 1<=j and j<=n implies positive%prime(p(j)) and 1<=r(j))
;;;            and
;;;           forall(j,k:zz, 1<=j and j<k and k<=n implies p(k)<p(j)))"
;;;  (theory h-o-real-arithmetic))

(def-constant prime%decomposition
  "lambda(p:[zz,zz],n:zz,
           forall(j:zz, 1<=j and j<=n implies positive%prime(p(j)))
            and
           forall(j,k:zz, 1<=j and j<=k and k<=n implies p(k)<=p(j)))"
  (theory h-o-real-arithmetic))

;;We now proceed to show any positive integer is the product of primes:

(def-constant smallest%factor
  "lambda(x:zz,iota(y:zz,2<=y and y divides x and 
                         forall(z:zz, 2<=z and z divides x implies y<=z)))"
  (theory h-o-real-arithmetic))

(def-theorem iota-free-smallest%proper%factor
  "forall(j,k:zz, smallest%factor(j)=k iff 
                  (2<=k and k divides j and 
                   forall(p:zz, 2<=p and p divides j implies k<=p)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    

    (unfold-single-defined-constant-globally smallest%factor)
    direct-and-antecedent-inference-strategy
    (let-script scripto
		0
		((contrapose "with(k,z:zz,z=k);")
		 (apply-macete-with-minor-premises eliminate-iota-macete)
		 (contrapose "with(p:prop,not(p));")))
    $scripto
    $scripto
    $scripto
    (backchain "with(p:prop,p and p);")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "b<=k and k<=b")
    simplify
    direct-inference
    (backchain "with(b,j:zz,forall(z:zz,2<=z and z divides j implies b<=z));")
    direct-and-antecedent-inference-strategy
    (backchain "with(k,j:zz,forall(p:zz,2<=p and p divides j implies k<=p));")
    direct-and-antecedent-inference-strategy

    )))

(def-theorem smallest%proper%factor-defined
  "forall(x:zz,2<=x implies #(smallest%factor(x)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:zz, smallest%factor(x)=s)")
    (antecedent-inference "with(p:prop,forsome(s:zz,p));")
    (apply-macete-with-minor-premises iota-free-smallest%proper%factor)
    (instantiate-theorem well-ordering-for-integers
			 ("lambda(j:zz, 2<=j and j divides x)"))
    (contrapose "with(p:prop,forall(y:zz,p));")
    (instantiate-existential ("x"))
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises self-divisibility)
    simplify
    (instantiate-universal-antecedent "with(p:prop,forall(n:zz,p));" ("1"))
    (simplify-antecedent "with(m:zz,f:[zz,prop],f(m));")
    (instantiate-existential ("u"))
    (instantiate-universal-antecedent "with(p:prop,forall(v:zz,p));" ("p"))
    simplify
    (simplify-antecedent "with(p:prop,not(p));")
    )))

(def-theorem smallest%proper%factor-is-prime
  "forall(x:zz,2<=x implies positive%prime(smallest%factor(x)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:zz, smallest%factor(x)=s)")
    (antecedent-inference "with(p:prop,forsome(s:zz,p));")
    (backchain "with(s,z:zz,z=s);")
    (incorporate-antecedent "with(s,z:zz,z=s);")
    (apply-macete-with-minor-premises iota-free-smallest%proper%factor)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) positive%prime)
    direct-and-antecedent-inference-strategy
    simplify
    (cut-with-single-formula "a<=s and s<=a")
    simplify
    direct-inference
    (apply-macete-with-minor-premises divides-implies-le)
    simplify
    (backchain "with(p:prop,forall(p:zz,with(p:prop,p)));")
    (apply-macete-with-minor-premises divisibility-is-transitive)
    direct-and-antecedent-inference-strategy
    simplify
    auto-instantiate-existential
    (instantiate-existential ("smallest%factor(x)"))
    simplify
    (apply-macete-with-minor-premises smallest%proper%factor-defined)

    )))

;;;(def-constant biggest%factor
;;;  "lambda(n:zz, n/smallest%factor(n))"
;;;  (theory h-o-real-arithmetic))
;;;
;;;(def-theorem prime-decomposition-lemma-1
;;;  "forall(m:zz, 2<=m implies #(biggest%factor(m),zz))"
;;;  (theory h-o-real-arithmetic)
;;;  (proof
;;;   (
;;;    
;;;    direct-and-antecedent-inference-strategy
;;;    (unfold-single-defined-constant (0) biggest%factor)
;;;    (cut-with-single-formula "forsome(s:zz, smallest%factor(m)=s)")
;;;    (antecedent-inference "with(p:prop,forsome(s:zz,p));")
;;;    (backchain "with(s,z:zz,z=s);")
;;;    (incorporate-antecedent "with(s,z:zz,z=s);")
;;;    (apply-macete-with-minor-premises iota-free-smallest%proper%factor)
;;;    (unfold-single-defined-constant (0) divides)
;;;    simplify
;;;    (instantiate-existential ("smallest%factor(m)"))
;;;    (move-to-ancestor 1)
;;;    (move-to-descendent (1 0))
;;;    (apply-macete-with-minor-premises smallest%proper%factor-defined)
;;;    simplify
;;;    )))
;;;
;;;(def-theorem prime-decomposition-lemma-2
;;;  "forall(m:zz, 2<=m implies m=biggest%factor(m)*smallest%factor(m))"
;;;  (theory h-o-real-arithmetic)
;;;  (proof
;;;   (
;;;
;;;
;;;    (unfold-single-defined-constant (0) biggest%factor)
;;;    direct-and-antecedent-inference-strategy
;;;    (cut-with-single-formula "2<=smallest%factor(m)")
;;;    simplify
;;;    (cut-with-single-formula "forsome(s:zz, smallest%factor(m)=s)")
;;;    (antecedent-inference "with(p:prop,forsome(s:zz,p));")
;;;    (backchain "with(s,z:zz,z=s);")
;;;    (incorporate-antecedent "with(s,z:zz,z=s);")
;;;    (apply-macete-with-minor-premises iota-free-smallest%proper%factor)
;;;    simplify
;;;    (instantiate-existential ("smallest%factor(m)"))
;;;    (move-to-ancestor 1)
;;;    (move-to-descendent (1 0))
;;;    (apply-macete-with-minor-premises smallest%proper%factor-defined)
;;;    simplify
;;;    )))

(def-theorem existence-of-prime-factorization
  "forall(m:zz,
     2<=m
      implies 
     forsome(p:[zz,zz],n:zz,
       prime%decomposition(p,n) and m=prod(1,n,p)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (let-script use-macete-on
		2
		((incorporate-antecedent ($2))
		 (apply-macete-with-minor-premises $1)
		 direct-and-antecedent-inference-strategy
		 simplify))
    (let-script use-definition
		1
		((incorporate-antecedent ((% "~a" $1)))
		 (unfold-single-defined-constant-globally $1)
		 direct-and-antecedent-inference-strategy
		 simplify))

    (induction complete-inductor ("m"))
    (cut-with-single-formula "forsome(s:zz,smallest%factor(m)=s)")
    (antecedent-inference "with(p:prop,forsome(s:zz,p));")
    (case-split ("s=m"))

    (block (cut-with-single-formula "positive%prime(m)")
	   (move-to-sibling 1)
	   (backchain-backwards "with(m,s:zz,s=m);")
	   (backchain-backwards "with(s,m:zz,smallest%factor(m)=s);")
	   (apply-macete-with-minor-premises smallest%proper%factor-is-prime)
	   (instantiate-existential ("1" "lambda(j:zz,m)"))
	   (unfold-single-defined-constant (0) prime%decomposition)
	   simplify
	   (unfold-single-defined-constant (0) prod)
	   (unfold-single-defined-constant (0) prod)
	   simplify)
    (cut-with-single-formula "forsome(t:zz, m/s=t)")
    (antecedent-inference "with(p:prop,forsome(t:zz,p));")
    (block (cut-with-single-formula "2<=t and t<m")
	   (move-to-sibling 1)
	   (cut-with-single-formula "0<t and not(t=1)")
	   simplify
	   (backchain-backwards "with(t,s,m:zz,m/s=t);")
	   (apply-macete-with-minor-premises fractional-expression-manipulation)
	   simplify
	   ($use-macete-on iota-free-smallest%proper%factor "smallest%factor")
	   ($use-macete-on iota-free-smallest%proper%factor "smallest%factor")
	   (backchain-backwards "with(t,s,m:zz,m/s=t);")
	   (backchain-backwards "with(t,s,m:zz,m/s=t);")
	   (apply-macete-with-minor-premises fractional-expression-manipulation)
	   simplify
	   ($use-macete-on iota-free-smallest%proper%factor "smallest%factor"))
    (move-to-ancestor 3)
    (move-to-descendent (1))
    ($use-macete-on iota-free-smallest%proper%factor "smallest%factor")
    ($use-definition divides)
    ($use-definition divides)
    (instantiate-universal-antecedent "with(p:prop,forall(k:zz,p));" ("t"))
    ($use-definition prime%decomposition)
    (instantiate-existential ("lambda(j:zz, if(j=n+1,s,p(j)))" "n+1"))
    beta-reduce-repeatedly
    (case-split ("j_$0<=n"))
    simplify
    simplify
    (backchain-backwards "with(s,m:zz,smallest%factor(m)=s);")
    (apply-macete-with-minor-premises smallest%proper%factor-is-prime)
    beta-reduce-repeatedly
    (case-split ("k_$0<=n " "j_$0<=n"))
    simplify
    simplify
    simplify
    ($use-macete-on iota-free-smallest%proper%factor "smallest%factor")
    (backchain "with(s:zz,
		       forall(p:zz,
				with(p:prop,
				       with(p:prop,p and p) implies with(p:zz,s<=p))));")
    (apply-macete-with-minor-premises divisibility-is-transitive)
    direct-inference
    ($use-macete-on positive-prime-characterization "positive%prime")
    (instantiate-existential ("prod(1,n,p)"))
    (apply-macete-with-minor-premises product-is-divisible-by-factors)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent
     "with(p:[zz,zz],n:zz,
	     forall(j:zz,1<=j and j<=n implies positive%prime(p(j))));"
				       ("x"))
    ($use-macete-on positive-prime-characterization "positive%prime")
    (backchain-backwards "with(p:[zz,zz],n,t:zz,t=prod(1,n,p));")
    (cut-with-single-formula "m/t=s")
    (unfold-single-defined-constant (0) divides)
    (incorporate-antecedent "with(t,s,m:zz,m/s=t);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (instantiate-universal-antecedent
     "with(p:[zz,zz],n:zz,
	     forall(j:zz,1<=j and j<=n implies positive%prime(p(j))));"
      ("j_$0"))
    simplify
    (incorporate-antecedent "with(t,s,m:zz,m/s=t);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) prod)
    simplify
    (case-split ("n<=0"))
    (contrapose "with(p:[zz,zz],n,t:zz,t=prod(1,n,p));")
    (unfold-single-defined-constant (0) prod)
    simplify
    simplify
    beta-reduce-repeatedly
    (cut-with-single-formula "prod(1,n,lambda(j:zz,if(j=1+n, s, p(j))))==prod(1,n,p)")
    (backchain "with(r:rr,r==r);")
    (backchain-backwards "with(p:[zz,zz],n,t:zz,t=prod(1,n,p));")
    (cut-with-single-formula "1<=n")

    (move-to-sibling 1)
    simplify
    (cut-with-single-formula "forsome(q:[zz,zz],q=lambda(j:zz,if(j=1+n, s, p(j))))")
    (antecedent-inference "with(p:prop,forsome(q:[zz,zz],p));")
    (backchain-backwards "with(f,q:[zz,zz],q=f);")
    (cut-with-single-formula "forall(k:zz,1<=k and k<=n implies q(k)==p(k))")
    (weaken (4 5 6 7 13 12 11 10 9 8 14 3 1))
    (induction integer-inductor ("n"))
    (backchain "with(p:prop,p implies p);")
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(k:zz,p));")
    simplify
    (backchain "with(p,q:[zz,zz],t:zz,
		       forall(k:zz,1<=k and k<=1+t implies q(k)==p(k)));")
    simplify
    (backchain "with(f,q:[zz,zz],q=f);")
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify
    (instantiate-existential ("lambda(j:zz,if(j=1+n, s, p(j)))"))
    (instantiate-existential ("smallest%factor(m)"))
    (move-to-ancestor 1)
    (move-to-descendent (1 0))
    (apply-macete-with-minor-premises smallest%proper%factor-defined)
    simplify


    )))


(comment;; modified proof

 (let-script use-macete-on
	     2
	     ((incorporate-antecedent ($2))
	      (apply-macete-with-minor-premises $1)
	      direct-and-antecedent-inference-strategy
	      simplify))
 (let-script use-definition
	     1
	     ((incorporate-antecedent ((% "~a" $1)))
	      (unfold-single-defined-constant-globally $1)
	      direct-and-antecedent-inference-strategy
	      simplify))
 (induction complete-inductor ("m"))
 (cut-with-single-formula "forsome(s:zz,smallest%factor(m)=s)")
 (antecedent-inference "with(p:prop,forsome(s:zz,p));")
 (case-split ("s=m"))
 (block (cut-with-single-formula "positive%prime(m)")
	(move-to-sibling 1)
	(backchain-backwards "with(m,s:zz,s=m);")
	(backchain-backwards "with(s,m:zz,smallest%factor(m)=s);")
	(apply-macete-with-minor-premises smallest%proper%factor-is-prime)
	(instantiate-existential ("1" "lambda(j:zz,m)"))
	(unfold-single-defined-constant (0) prime%decomposition)
	simplify
	(unfold-single-defined-constant (0) prod)
	(unfold-single-defined-constant (0) prod)
	simplify)
 (cut-with-single-formula "forsome(t:zz, m/s=t)")
 (antecedent-inference "with(p:prop,forsome(t:zz,p));")
 (block (cut-with-single-formula "2<=t and t<m")
	(move-to-sibling 1)
	(cut-with-single-formula "0<t and not(t=1)")
	simplify
	(backchain-backwards "with(t,s,m:zz,m/s=t);")
	(apply-macete-with-minor-premises fractional-expression-manipulation)
	simplify
	($use-macete-on iota-free-smallest%proper%factor "smallest%factor")
	($use-macete-on iota-free-smallest%proper%factor "smallest%factor")
	(backchain-backwards "with(t,s,m:zz,m/s=t);")
	(backchain-backwards "with(t,s,m:zz,m/s=t);")
	(apply-macete-with-minor-premises fractional-expression-manipulation)
	simplify
	($use-macete-on iota-free-smallest%proper%factor "smallest%factor"))
 (move-to-ancestor 3)
 (move-to-descendent (1))
 ($use-macete-on iota-free-smallest%proper%factor "smallest%factor")
 ($use-definition divides)
 ($use-definition divides)
 (instantiate-universal-antecedent "with(p:prop,forall(k:zz,p));" ("t"))
 ($use-definition prime%decomposition)
 (instantiate-existential ("lambda(j:zz, if(j=n+1,s,p(j)))" "n+1"))
 beta-reduce-repeatedly
 (case-split ("j_$0<=n"))
 simplify
 simplify
 (backchain-backwards "with(s,m:zz,smallest%factor(m)=s);")
 (apply-macete-with-minor-premises smallest%proper%factor-is-prime)
 beta-reduce-repeatedly
 (case-split ("k_$0<=n " "j_$0<=n"))
 simplify
 simplify
 simplify
 ($use-macete-on iota-free-smallest%proper%factor "smallest%factor")
 (backchain "with(s:zz,
  forall(p:zz,
    with(p:prop,
      with(p:prop,p and p) implies with(p:zz,s<=p))));")
 (apply-macete-with-minor-premises divisibility-is-transitive)
 direct-inference
 ($use-macete-on positive-prime-characterization "positive%prime")
 (instantiate-existential ("prod(1,n,p)"))
 (apply-macete-with-minor-premises product-is-divisible-by-factors)
 direct-and-antecedent-inference-strategy
 (instantiate-universal-antecedent "with(p:[zz,zz],n:zz,
  forall(j:zz,1<=j and j<=n implies positive%prime(p(j))));"
				   ("x"))
 ($use-macete-on positive-prime-characterization "positive%prime")
 (backchain-backwards "with(p:[zz,zz],n,t:zz,t=prod(1,n,p));")
 (cut-with-single-formula "m/t=s")
 (unfold-single-defined-constant (0) divides)
 (incorporate-antecedent "with(t,s,m:zz,m/s=t);")
 (apply-macete-with-minor-premises fractional-expression-manipulation)
 simplify
 simplify
 (unfold-single-defined-constant (0) prod)
 simplify
 (move-to-ancestor 1)
 (case-split ("n<=0"))
 (contrapose "with(p:[zz,zz],n,t:zz,t=prod(1,n,p));")
 (unfold-single-defined-constant (0) prod)
 simplify
 simplify
 beta-reduce-repeatedly
 (cut-with-single-formula "prod(1,n,lambda(j:zz,if(j=1+n, s, p(j))))==prod(1,n,p)")
 (backchain "with(r:rr,r==r);")
 (backchain-backwards "with(p:[zz,zz],n,t:zz,t=prod(1,n,p));")
 (cut-with-single-formula "1<=n")
 (move-to-sibling 1)
 simplify
 (cut-with-single-formula "forsome(q:[zz,zz],q=lambda(j:zz,if(j=1+n, s, p(j))))")
 (antecedent-inference "with(p:prop,forsome(q:[zz,zz],p));")
 (backchain-backwards "with(f,q:[zz,zz],q=f);")
 (cut-with-single-formula "forall(k:zz,1<=k and k<=n implies q(k)==p(k))")
 (incorporate-antecedent "with(t,s,m:zz,m/s=t);")
 (apply-macete-with-minor-premises fractional-expression-manipulation)
 simplify
 (backchain "with(f,q:[zz,zz],q=f);")
 beta-reduce-repeatedly
 direct-and-antecedent-inference-strategy
 simplify
 (instantiate-existential ("lambda(j:zz,if(j=1+n, s, p(j)))"))
 (cut-with-single-formula "forsome(q:[zz,zz],q=lambda(j:zz,if(j=1+n, s, p(j))))")
 (antecedent-inference "with(p:prop,forsome(q:[zz,zz],p));")
 (backchain-backwards "with(f,q:[zz,zz],q=f);")
 (cut-with-single-formula "forall(k:zz,1<=k and k<=n implies q(k)==p(k))")
 (cut-with-single-formula "1<=n")
 (move-to-sibling 1)
 simplify
 (weaken (13 2 3 4 5 6 7 8 9 10 11 12))
 (induction integer-inductor ("n"))
 (backchain "with(p:prop,p implies p);")
 direct-and-antecedent-inference-strategy
 (backchain "with(p:prop,forall(k:zz,p));")
 simplify
 (backchain "with(p,q:[zz,zz],t:zz,
  forall(k:zz,1<=k and k<=1+t implies q(k)==p(k)));")
 simplify
 (backchain "with(f,q:[zz,zz],q=f);")
 beta-reduce-repeatedly
 direct-and-antecedent-inference-strategy
 simplify
 (instantiate-existential ("lambda(j:zz,if(j=1+n, s, p(j)))"))
 (instantiate-existential ("smallest%factor(m)"))
 simplify
 (apply-macete-with-minor-premises smallest%proper%factor-defined))


(def-theorem unique-factorization-lemma-1
  "forall(p,q:[zz,zz],m,n:zz,
    1<=n
      and 
     1<=m
      and 
     prime%decomposition(p,n)
      and 
     prime%decomposition(q,m)
      and 
     prod(1,n,p)=prod(1,m,q)
      implies 
     p(n)<=q(m))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally prime%decomposition)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(r:rr,r=r);")
    (unfold-single-defined-constant (1) prod)
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "q(m) divides prod(1,n,p)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises divisibility-lemma)
    (instantiate-existential ("prod(1,[-1]+m,q)"))
    (apply-macete-with-minor-premises prod-integer-definedness)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "positive%prime(q(k))")
    simplify
    (cut-with-single-formula "positive%prime(q(m))")
    (incorporate-antecedent "with(z:zz,positive%prime(z));")
    (apply-macete-with-minor-premises positive-prime-characterization)
    simplify
    simplify
    (apply-macete-with-minor-premises prod-integer-definedness)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "positive%prime(p(k))")
    simplify
    (cut-with-single-formula "forsome(v:zz, 1<=v and v<=n and q(m)=p(v))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises prime-divisor-of-a-prime)
    (incorporate-antecedent "with(r:rr,z:zz,z divides r);")
    (apply-macete-with-minor-premises prime-divisor-of-a-general-product)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("j"))
    simplify
    (antecedent-inference "with(p:prop,forsome(v:zz,p));")
    (cut-with-single-formula "p(n)<=p(v)")
    simplify
    simplify)))



(def-theorem unique-factorization-lemma-2
  "forall(p,q:[zz,zz],m,n:zz,
    1<=n
      and 
     1<=m
      and 
     prime%decomposition(p,n)
      and 
     prime%decomposition(q,m)
      and 
     prod(1,n,p)=prod(1,m,q)
      implies 
     p(n)=q(m))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "p(n)<=q(m) and q(m)<=p(n)")
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises unique-factorization-lemma-1)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises unique-factorization-lemma-1)
    direct-and-antecedent-inference-strategy

    )))


(def-theorem unique-factorization-lemma-3
  "forall(p,q:[zz,zz],m,n:zz,
    1<=n
      and 
     1<=m
      and 
     prime%decomposition(p,n)
      and 
     prime%decomposition(q,m)
      and 
     prod(1,n,p)=prod(1,m,q)
      implies 
     prod(1,n-1,p)=prod(1,m-1,q))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "p(n)=q(m)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises unique-factorization-lemma-2)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(q:[zz,zz],m:zz,p:[zz,zz],n:zz,prod(1,n,p)=prod(1,m,q));")
    (unfold-single-defined-constant (0 1) prod)
    simplify
    (backchain "with(z:zz,z=z);")
    (cut-with-single-formula "2<=q(m)")
    simplify
    (cut-with-single-formula "positive%prime(q(m))")
    (incorporate-antecedent "with(z:zz,positive%prime(z));")
    (apply-macete-with-minor-premises positive-prime-characterization)
    simplify
    (incorporate-antecedent "with(m:zz,q:[zz,zz],prime%decomposition(q,m));")
    (unfold-single-defined-constant (0) prime%decomposition)
    direct-and-antecedent-inference-strategy
    simplify
    )))


(def-theorem unique-factorization-lemma-4
  "forall(p,q:[zz,zz],m,n:zz,
     prime%decomposition(p,n) and 1<=n
      implies 
     not(prod(1,n,p)=1))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "2<=prod(1,n,p)")
    simplify
    (unfold-single-defined-constant (0) prod)
    simplify
    (force-substitution "2" "1*2" (0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises monotone-product-lemma)
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises product-gte-1)
    direct-and-antecedent-inference-strategy
    (let-script
     use-prime-def
     1
     ((cut-with-single-formula (% "positive%prime(p(~a))" $1))
      (incorporate-antecedent "with(z:zz,positive%prime(z));")
      (apply-macete-with-minor-premises positive-prime-characterization)
      simplify
      (incorporate-antecedent "with(n:zz,p:[zz,zz],prime%decomposition(p,n));")
      (unfold-single-defined-constant-globally prime%decomposition)
      direct-and-antecedent-inference-strategy
      simplify))
    ($use-prime-def "k")
    simplify
    ($use-prime-def "n")
    )))


(def-theorem unique-factorization-lemma-5
  "forall(p,q:[zz,zz],m,n,k:zz,
     k<=m
      and 
     k<=n
      and 
     0<=k
      and 
     prime%decomposition(p,n)
      and 
     prime%decomposition(q,m)
      and 
     prod(1,n,p)=prod(1,m,q)
      implies 
     prod(1,n-k,p)=prod(1,m-k,q))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (induction trivial-integer-inductor ("k"))
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify
    (force-substitution "[-1]+n+[-1]*t" "(n-t)-1" (0))
    (move-to-sibling 1)
    simplify
    (force-substitution "[-1]+m+[-1]*t" "(m-t)-1" (0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises unique-factorization-lemma-3)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    (let-script use-def
		1
		((incorporate-antecedent $1)
		 (unfold-single-defined-constant-globally prime%decomposition)
		 direct-and-antecedent-inference-strategy
		 simplify
		 simplify))
    ($use-def "prime%decomposition(p,n)")
    ($use-def "prime%decomposition(q,m)")
    simplify
    )))


(def-theorem unique-factorization-theorem
  "forall(p,q:[zz,zz],m,n,k:zz,
     1<=m
      and 
     1<=n
      and 
     prime%decomposition(p,n)
      and 
     prime%decomposition(q,m)
      and 
     prod(1,n,p)=prod(1,m,q)
      implies 
     m=n and forall(k:zz,1<=k and k<=m implies p(k)=q(k)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (let-script use-def 1
		((incorporate-antecedent $1) (unfold-single-defined-constant-globally prime%decomposition)
					     direct-and-antecedent-inference-strategy simplify simplify
					     ) )
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
      (cut-with-single-formula
       "forall(k:zz, 1<=k and k<=n and k<=m implies 
                           prod(1,n-k,p)=prod(1,m-k,q))"
       )
      (block 
	(script-comment "`cut-with-single-formula' at (0)") (case-split ("n<=m"))
	(block 
	  (script-comment "`case-split' at (1)")
	  (instantiate-universal-antecedent "with(p:prop,forall(k:zz,p));" ("n"))
	  (simplify-antecedent "with(p:prop,not(p));")
	  (block 
	    (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	    (contrapose
	     "with(q:[zz,zz],m:zz,p:[zz,zz],n:zz,
  prod(1,n-n,p)=prod(1,m-n,q));"
	     )
	    (unfold-single-defined-constant (0) prod) simplify
	    (force-substitution "1=prod(1,[-1]*n+m,q)" "prod(1,[-1]*n+m,q)=1" (0))
	    (block 
	      (script-comment "`force-substitution' at (0)")
	      (apply-macete-with-minor-premises unique-factorization-lemma-4) simplify
	      ($use-def "prime%decomposition(q,m)")
	      )
	    simplify
	    ) )
	(block 
	  (script-comment "`case-split' at (2)")
	  (instantiate-universal-antecedent "with(p:prop,forall(k:zz,p));" ("m"))
	  (simplify-antecedent "with(m,n:zz,not(n<=m));")
	  (simplify-antecedent "with(m:zz,not(m<=m));")
	  (block 
	    (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	    (contrapose "with(q,p:[zz,zz],m,n:zz,prod(1,n-m,p)=prod(1,m-m,q));")
	    (unfold-single-defined-constant (1) prod) simplify
	    (apply-macete-with-minor-premises unique-factorization-lemma-4)
	    direct-and-antecedent-inference-strategy ($use-def "prime%decomposition(p,n)")
	    simplify
	    ) ) )
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	direct-and-antecedent-inference-strategy
	(apply-macete-with-minor-premises unique-factorization-lemma-5)
	direct-and-antecedent-inference-strategy
	(apply-macete-with-minor-premises unique-factorization-lemma-2) simplify
	) )
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0 0 0)")
      (apply-macete-with-minor-premises unique-factorization-lemma-2)
      direct-and-antecedent-inference-strategy ($use-def "prime%decomposition(p,n)")
      ($use-def "prime%decomposition(q,m)")
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (4)")
	(force-substitution "k" "n-(n-k)" (0))
	(block 
	  (script-comment "`force-substitution' at (0)")
	  (force-substitution "k" "m-(n-k)" (1))
	  (block 
	    (script-comment "`force-substitution' at (0)")
	    (apply-macete-with-minor-premises unique-factorization-lemma-5)
	    direct-and-antecedent-inference-strategy simplify simplify simplify
	    )
	  simplify
	  )
	simplify
	) )

    )))
