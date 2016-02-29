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


(herald applications)

(include-files
 (files (imps theories/partial-orders/knaster-fixed-point-theorem)
	(imps theories/partial-orders/real-order-properties)
	))

;; (set (proof-log-port)(standard-output))



(def-constant monotone%between
  "lambda(a,b:rr, f:[rr,rr],
     forall(x,y:rr,
       a <= x
        and 
       x <= b
        and 
       a <= y
        and 
       y <= b
        and 
       x <= y
        implies 
       f(x) <= f(y)))"
  (theory h-o-real-arithmetic))

(def-theorem monotone-fixed-point-theorem
  "forall(b,a:rr,f:[rr,rr],
     a <= b
      and 
     a <= f(a)
      and 
     f(b) <= b
      and 
     monotone%between(a,b,f)
      implies 
     forsome(z:rr,(a <= z and z <= b) and f(z)=z))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant (0) monotone%between)
    (apply-macete-with-minor-premises tr%knaster-fixed-point-theorem-corollary)
    )))

(def-constant weakly%lipschitz%between
  "lambda(a,b:rr,f:[rr,rr], forsome(k:rr, 
         forall(x,y:rr, x<=y and a<=x and y<=b implies f(y)-f(x)<=k*(y-x))))"
  (theory h-o-real-arithmetic))

(def-theorem weak-lipschitz-constant-positive 
  "forall(a,b:rr,f:[rr,rr], weakly%lipschitz%between(a,b,f) iff forsome(k:rr, 0<k and 
         forall(x,y:rr, x<=y and a<=x and y<=b implies f(y)-f(x)<=k*(y-x))))"
  (theory h-o-real-arithmetic)
  (proof (
	  (unfold-single-defined-constant-globally weakly%lipschitz%between)
	  direct-and-antecedent-inference-strategy
	  (case-split ("0<k"))
	  auto-instantiate-existential
	  (instantiate-existential ("1"))
	  simplify
	  (apply-macete-with-minor-premises transitivity-of-<=)
	  (instantiate-existential ("0"))
	  (case-split ("k=0"))
	  (incorporate-antecedent "with(p:prop,forall(x,y:rr,p));")
	  simplify
	  (cut-with-single-formula "k*(y-x)<=0")
	  (auto-instantiate-universal-antecedent "with(k:rr,f:[rr,rr],b,a:rr,
  forall(x,y:rr,
    x<=y and a<=x and y<=b implies f(y)-f(x)<=k*(y-x)));")
	  simplify
	  (force-substitution "k*(y-x)<=0" "(-k)*0<=(-k)*(y-x)" (0))
	  (apply-macete-with-minor-premises monotonicity-for-multiplication)
	  simplify
	  simplify
	  simplify
	  simplify
	  auto-instantiate-existential)))

(def-theorem weak-intermediate-value-thm
  "forall(a,b:rr, f:[rr,rr], f(a)<=0 and 0<=f(b) 
              and
             a<=b
              and
             weakly%lipschitz%between(a,b,f)
              implies
             forsome(x:rr, a<=x and x<=b and f(x)=0))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises weak-lipschitz-constant-positive)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x:rr, (a<=x and x<=b) and lambda(z:rr,z-f(z)/k)(x)=x)")
    (block (script-comment "First use the assertion.")
	   (instantiate-existential ("x"))
	   (incorporate-antecedent "with(p:prop,p and p);")
	   (apply-macete-with-minor-premises fractional-expression-manipulation)
	   simplify)
    (block (script-comment "Now prove the assertion useing the knaster fp theorem.")
	   (apply-macete-with-minor-premises tr%knaster-fixed-point-theorem-corollary)
	   (incorporate-antecedent "with(p:prop,forall(x,y:rr,p));")
	   (apply-macete-with-minor-premises fractional-expression-manipulation)
	   simplify
	   direct-and-antecedent-inference-strategy-with-simplification
	   (instantiate-universal-antecedent "with(p:prop,forall(x,y:rr,p));"
    ("x_$0" "y_$0")
  )
	   simplify)
    )))


(comment old-proof
	 (unfold-single-defined-constant (0) weakly%lipschitz%between)
    direct-and-antecedent-inference-strategy
    (case-split ("f(b)=0"))
    (instantiate-existential ("b"))
    simplify
    (cut-with-single-formula "k<=0 or 0<k")
    (antecedent-inference "with(p:prop,p or p);")
    (contrapose "with(p:prop,forall(x,y:rr,p));")
    (instantiate-existential ("a" "b"))
    simplify
    simplify
    (cut-with-single-formula "k*(b-a)<=0")
    simplify
    (case-split ("k=0"))
    simplify
    simplify
    (cut-with-single-formula "forsome(x:rr, (a<=x and x<=b) and lambda(z:rr,z-f(z)/k)(x)=x)")
    (instantiate-existential ("x"))
    (contrapose "with(p:prop,p and p);")
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (apply-macete-with-minor-premises tr%knaster-fixed-point-theorem-corollary)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(x,y:rr,p));"
				      ("x_$0" "y_$0"))
    simplify
    simplify
    )


(def-theorem power-fn-is-monotone
  "forall(n:zz, x,y:rr, 1<=n and 0<=x and x<=y implies x^n <= y^n)"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (
    
    
    (induction integer-inductor ("n"))
    (apply-macete-with-minor-premises exp-out)
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    (case-split ("x=0"))
    simplify
    (cut-with-single-formula "0<x^t")
    simplify
    (apply-macete-with-minor-premises positivity-for-r^n)
    simplify

    )))

(def-theorem power-fn-is-weakly%lipschitz
  "forall(r:rr, n:zz, 1<=n implies weakly%lipschitz%between(0,r, lambda(x:rr,x^n)))"
  (theory h-o-real-arithmetic)
  (proof
   (



    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) weakly%lipschitz%between)
    (case-split ("r=0"))
    (instantiate-existential ("1"))
    (cut-with-single-formula "x_$0=y_$0")
    simplify
    simplify
    (instantiate-existential ("n*r^(n-1)"))
    (induction trivial-integer-inductor ("n"))
    simplify
    (cut-with-single-formula
     "y_$1*(y_$1^t-x_$1^t)<=t*r^t*(y_$1-x_$1) and x_$1^t*(y_$1-x_$1)<=r^t*(y_$1-x_$1)")
    simplify
    (force-substitution "t*r^t*(y_$1-x_$1)" "r*(t*r^(t-1)*(y_$1-x_$1))" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    (force-substitution "0" "0^t" (0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises power-fn-is-monotone)
    simplify
    simplify

    )))

(def-theorem nth-roots-exist
  "forall(x:rr, n:zz, 1<=n and 0<=x implies forsome(y:rr, 0<=y and y^n=x))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forsome(a:rr, forsome(y:rr, 0<=y and y<=a and lambda(theta:rr, theta^n-x)(y)=0))")
    (antecedent-inference "with(p:prop,forsome(a:rr,p));")
    (instantiate-existential ("y"))
    (simplify-antecedent "with(p:prop,p and p and p);")
    (apply-macete-with-minor-premises weak-intermediate-value-thm)
    beta-reduce-repeatedly
    (force-substitution "weakly%lipschitz%between(0,a,lambda(theta:rr,theta^n-x))"
			"weakly%lipschitz%between(0,a,lambda(theta:rr,theta^n))"
			(0))
    (move-to-sibling 1)
    (unfold-single-defined-constant-globally weakly%lipschitz%between)
    simplify
    (apply-macete-with-minor-premises power-fn-is-weakly%lipschitz)
    simplify
    (case-split ("x<=1"))
    (instantiate-existential ("1"))
    simplify
    simplify
    (instantiate-existential ("x"))
    (induction integer-inductor ("n"))
    (apply-macete-with-minor-premises exp-out)
    (force-substitution "x" "1*x" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    simplify    )))
	     
(def-theorem nth-roots-are-unique
  "forall(x,y:rr, n:zz, 1<=n and 0<=x and 0<=y and x^n=y^n implies x=y)"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    (cut-with-single-formula "forall(x,y:rr, n:zz, 1<=n and 0<=x and x<y implies x^n<y^n)")
    (move-to-sibling 1)
    direct-and-antecedent-inference-strategy
    (case-split ("x=0"))
    simplify
    (apply-macete-with-minor-premises positivity-for-r^n)
    (cut-with-single-formula "forall(t:rr, 1<t implies 1<t^n)")
    (instantiate-universal-antecedent "with(p:prop,forall(t:rr,p));" ("y/x"))
    (contrapose "with(r:rr,not(1<r));")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (incorporate-antecedent "with(r:rr,1<r);")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (apply-macete-with-minor-premises positivity-for-r^n)
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "1+n*(t-1)<=t^n and 0<n*(t-1)")
    simplify
    (force-substitution "t" "1+(t-1)" (1))
    (apply-macete-with-minor-premises bernoullis-inequality)
    simplify
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "x<y or x=y or y<x")
    (antecedent-inference "with(p:prop,p or p or p);")
    (instantiate-universal-antecedent "with(p:prop,forall(x,y:rr,n:zz,p));"
				      ("x" "y" "n"))
    simplify
    (instantiate-universal-antecedent "with(p:prop,forall(x,y:rr,n:zz,p));"
				      ("y" "x" "n"))
    simplify
    simplify
    )))


(def-constant nth%root
  "lambda(n:zz,x:rr, iota(y:rr, 1<=n and 0<=y and y^n=x))"
  (theory h-o-real-arithmetic))

(def-theorem iota-free-characterization-of-nth%root
  "forall(n:zz,x,y:rr, 1<=n implies (nth%root(n,x)=y iff (0<=y and y^n=x)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant (0) nth%root)
    direct-and-antecedent-inference-strategy
    (contrapose "with(y,r:rr,r=y);")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (contrapose "with(p:prop,not(p));")
    (contrapose "with(y,r:rr,r=y);")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises nth-roots-are-unique)
    (instantiate-existential ("n"))    
    )))


;;;(def-theorem iota-free-characterization-of-rad%pos
;;;  "forall(n:zz,x,y:rr, 0<=y and 1<=n implies (nth%root(n,x)=y iff y^n=x))"
;;;  (theory h-o-real-arithmetic)
;;;  (proof
;;;   (
;;;
;;;    
;;;    (unfold-single-defined-constant (0) nth%root)
;;;    direct-and-antecedent-inference-strategy
;;;    (contrapose "with(y,r:rr,r=y);")
;;;    (apply-macete-with-minor-premises eliminate-iota-macete)
;;;    (contrapose "with(p:prop,not(p));")
;;;    (apply-macete-with-minor-premises eliminate-iota-macete)
;;;    direct-and-antecedent-inference-strategy
;;;    (apply-macete-with-minor-premises nth-roots-are-unique)
;;;    (instantiate-existential ("n"))
;;;    )))


(def-theorem nth%root%existence
  "forall(n:zz, x:rr, 0 <=x and 1<=n implies #(nth%root(n,x)))"
  (theory h-o-real-arithmetic)
  (usages d-r-convergence)
  (proof
   (
    
    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(y:rr, 0<=y and nth%root(n,x)=y)")
    (antecedent-inference "with(p:prop,forsome(y:rr,p));")
    (apply-macete-with-minor-premises iota-free-characterization-of-nth%root)
    simplify
    (apply-macete-with-minor-premises nth-roots-exist)
    direct-and-antecedent-inference-strategy
    )))


(def-theorem nth%root-power
  "forall(a,b:rr,n:zz,0<=a and 1<=n implies nth%root(n,a)^n=a)"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:rr, nth%root(n,a)=s)")
    (move-to-sibling 1)
    (instantiate-existential ("nth%root(n,a)"))
    simplify
    (antecedent-inference "with(p:prop,forsome(s:rr,p));")
    (backchain "with(s,r:rr,r=s);")
    (incorporate-antecedent "with(s,r:rr,r=s);")
    (apply-macete-with-minor-premises iota-free-characterization-of-nth%root)
    direct-and-antecedent-inference-strategy

    )))


(def-theorem strict-monotonicity-of-nth%root
  "forall(a,b:rr, n:zz, 0<=a and a<b and 1<=n implies nth%root(n,a)<nth%root(n,b))"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (case-split ("nth%root(n,b)<=nth%root(n,a)"))
    (move-to-sibling 2)
    simplify
    (cut-with-single-formula "not(b<=a)")
    (move-to-sibling 1)
    simplify
    (contrapose "with(p:prop,not(p));")
    (cut-with-single-formula "(nth%root(n,b))^n<=(nth%root(n,a))^n")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises power-fn-is-monotone)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:rr, nth%root(n,b)=s)")
    (antecedent-inference "with(p:prop,forsome(s:rr,p));")
    (backchain "with(s,r:rr,r=s);")
    (incorporate-antecedent "with(s,r:rr,r=s);")
    (apply-macete-with-minor-premises iota-free-characterization-of-nth%root)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("nth%root(n,b)"))
    (contrapose "with(n:zz,r:rr,r^n<=r^n);")
    (apply-macete-with-minor-premises nth%root-power)


    )))

(def-theorem monotonicity-of-nth%root
  "forall(a,b:rr, n:zz, 0<=a and a<=b and 1<=n implies nth%root(n,a)<=nth%root(n,b))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("a=b"))
    simplify
    (cut-with-single-formula "nth%root(n,a)<nth%root(n,b)")
    simplify
    (apply-macete-with-minor-premises strict-monotonicity-of-nth%root)
    simplify)))
    


(def-theorem nth-root-is-multiplicative
  "forall(a,b:rr, n:zz,
     0<=a and 0<=b and 1<=n implies nth%root(n,a*b)=nth%root(n,a)*nth%root(n,b))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s,t:rr, nth%root(n,a)=s and nth%root(n,b)=t)"
			     )
    (move-to-sibling 1)
    (instantiate-existential ("nth%root(n,a)" "nth%root(n,b)"))
    (block 
	(script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(s,t:rr,p));")
      (backchain "with(p:prop,p and p);") (backchain "with(p:prop,p and p);")
      (incorporate-antecedent "with(p:prop,p and p);")
      (apply-macete-with-minor-premises iota-free-characterization-of-nth%root)
      simplify direct-and-antecedent-inference-strategy
      (block
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0)"
			  )
	(apply-macete-with-minor-premises positivity-for-products) simplify
	)
      simplify
      ))))


(def-theorem nth%root-of-zero
  "forall(n:zz,  1<=n implies nth%root(n,0)=0)"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-inference
    (instantiate-theorem nth%root%existence ("n" "0"))
    (simplify-antecedent "with(p:prop,p);")
    direct-inference
    (incorporate-antecedent "with(p:prop,p);")
    (unfold-single-defined-constant-globally nth%root)
    (eliminate-defined-iota-expression 1 zero)
    simplify)))


(def-theorem nth%root-non-negative
  "forall(x:rr,n:zz, 0<=x and 1<=n implies 0<= nth%root(n,x))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem strict-monotonicity-of-nth%root ("0" "x" "n"))
    (simplify-antecedent "with(p:prop,not(p));")
    (cut-with-single-formula "x=0")
    simplify
    (apply-macete-with-minor-premises nth%root-of-zero)
    simplify
    (contrapose "with(r:rr,r<r);")
    (apply-macete-with-minor-premises nth%root-of-zero)
    simplify)))

(def-theorem nth%root-positive-for-positive
  "forall(x:rr,n:zz, 0<x and 1<=n implies 0<nth%root(n,x))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem strict-monotonicity-of-nth%root ("0" "x" "n"))
    (simplify-antecedent "with(p:prop,not(p));")
    (contrapose "with(x:rr,n:zz,nth%root(n,0)<nth%root(n,x));")
    (apply-macete-with-minor-premises nth%root-of-zero))))


(def-theorem iterated-nth%root
  "forall(x:rr,n,m:zz, 0<=x and 1<=n and 1<=m implies nth%root(n*m,x)=nth%root(n,nth%root(m,x)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises iota-free-characterization-of-nth%root)
    (apply-macete-with-minor-premises nth%root-non-negative)
    (apply-macete-with-minor-premises nth%root-non-negative)
    (force-substitution "nth%root(n,nth%root(m,x))^(n*m)"
			"(nth%root(n,nth%root(m,x))^(n))^m"
			(0))
    (apply-macete-with-minor-premises nth%root-power)
    (apply-macete-with-minor-premises nth%root-power)
    simplify
    (apply-macete-with-minor-premises nth%root-non-negative)
    simplify
    (apply-macete-with-minor-premises product-power-is-iterated-power)
    (force-substitution "1" "1*1" (0))
    (apply-macete-with-minor-premises monotone-product-lemma)
    simplify
    simplify

    )))

