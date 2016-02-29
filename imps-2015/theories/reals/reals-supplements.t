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


(herald reals-supplements)

(def-theorem archimedean
  "forall(a:rr,forsome(n:zz,a<n))"
  (theory h-o-real-arithmetic)
  (proof 

   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem completeness ("lambda(j:zz, truth)"))
    (block (script-comment "node added by `instantiate-theorem' at (0 0 0)")
	   (instantiate-universal-antecedent "with(p:prop,p);" ("1"))
	   (contrapose "with(p:prop,p);")
	   simplify)
    (block (script-comment "node added by `instantiate-theorem' at (0 0 1)")
	   (contrapose "with(p:prop,p);")
	   (instantiate-existential ("a"))
	   (instantiate-universal-antecedent "with(p:prop,forall(n:zz,p));"
					     ("theta"))
	   simplify)
    (block (script-comment "node added by `instantiate-theorem' at (0 1 0 0)")
	   (contrapose "with(gamma:rr,p:prop,
  forall(gamma_1:rr,
    forall(theta:rr,p) implies gamma<=gamma_1));")
	   (instantiate-existential ("gamma-1"))
	   (prove-by-logic-and-simplification 3)
	   simplify)

    )))

(def-constant convergent%to%infinity
  "lambda(s:[zz,rr],
         forall(m:rr,forsome(x:zz, forall(j:zz, x<=j implies m<=s(j)))))"
  (theory h-o-real-arithmetic))

(def-theorem convergent%to%infinity-linear-form
  "forall(a,b:rr, 0<a implies convergent%to%infinity(lambda(j:zz,a*j+b)))"
  (theory h-o-real-arithmetic)
  
  (proof


   (

    (unfold-single-defined-constant (0) convergent%to%infinity)
    direct-and-antecedent-inference-strategy
    (force-substitution "forall(j_$0:zz,x_$0<=j_$0 implies m_$0<=a*j_$0+b)" "a^[-1]*(m_$0-b)<x_$0" (0))
    (apply-macete-with-minor-premises archimedean)
    (force-substitution "m_$0<=a*j_$0+b" "a^[-1]*(m_$0-b)<j_$0" (0))
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify


    )))

(def-theorem bernoullis-inequality
  "forall(h:rr,n:zz,-1<h and 1<=n implies 1+n*h<=(1+h)^n)"
  (theory h-o-real-arithmetic)
  (proof 


   (

    (induction integer-inductor ("n"))
    (cut-with-single-formula "0<=t*h^2 and (1+h)*(1+h*t)<=(1+h)*(1+h)^t")
    simplify
    simplify

    )))


(def-theorem unbounded-heredity
  "forall(s,t:[zz,rr],convergent%to%infinity(s) and forsome(m:zz,forall(n:zz,m<=n implies s(n)<=t(n))) implies convergent%to%infinity(t))"
  (theory h-o-real-arithmetic)

  (proof

   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(m:rr,forsome(x:zz,p)));"
				      ("m"))
    (instantiate-existential ("max(m_$0,x)"))
    (apply-macete-with-minor-premises transitivity-of-<=)
    (block (script-comment "node added by `apply-macete-with-minor-premises' at (0)")
	   (instantiate-existential ("s(j_$0)"))
	   (block (script-comment "node added by `instantiate-existential' at (0 0)")
		  (backchain "with(s:[zz,rr],m:rr,x:zz,forall(j:zz,x<=j implies m<=s(j)));")
		  (apply-macete-with-minor-premises transitivity-of-<=)
		  (instantiate-existential ("max(m_$0,x)"))
		  (apply-macete-with-minor-premises maximum-2nd-arg))
	   (block (script-comment "node added by `instantiate-existential' at (0 1)")
		  (backchain "with(t,s:[zz,rr],m_$0:zz,
  forall(n:zz,m_$0<=n implies s(n)<=t(n)));")
		  (apply-macete-with-minor-premises transitivity-of-<=)
		  (instantiate-existential ("max(m_$0,x)"))
		  (apply-macete-with-minor-premises maximum-1st-arg))
	   (cut-with-single-formula "s(j_$0)<=t(j_$0)"))
    (cut-with-single-formula "s(j_$0)<=t(j_$0)"))))

(def-theorem r^n-convergent-to-infinity
  "forall(r:rr,1<r implies convergent%to%infinity(lambda(n:zz,r^n)))"
  (theory h-o-real-arithmetic)

  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises unbounded-heredity)
    (instantiate-existential ("lambda(k:zz, (r-1)*k+1)"))
    (block (script-comment "node added by `instantiate-existential' at (0 0)")
	   (apply-macete-with-minor-premises convergent%to%infinity-linear-form)
	   simplify)
    (block (script-comment "node added by `instantiate-existential' at (0 1)")
	   beta-reduce-repeatedly
	   (force-substitution "(r-1)*n_$0+1<=r^n_$0"
			       "1+n_$0*(r-1)<=(1+(r-1))^n_$0"
			       (0))
	   (block (script-comment "node added by `force-substitution' at (0)")
		  (apply-macete-with-minor-premises bernoullis-inequality)
		  (instantiate-existential ("1"))
		  simplify)
	   simplify)

    )))

(def-theorem complete-induction
  "forall(p:[zz,prop],n:zz,
     forall(m:zz,
       n<=m and forall(k:zz,n<=k and k<m implies p(k))
        implies 
       p(m))
      implies 
     forall(k:zz,n<=k implies p(k)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(k:zz,n<=k implies forall(s:zz, n<=s and s<= k implies p(s)))")
    (block (script-comment "node added by `cut-with-single-formula' at (0)")
	   (backchain "with(p:prop,n:zz,forall(k:zz,n<=k implies forall(s:zz,p)));")
	   (instantiate-existential ("k"))
	   simplify)
    (block (script-comment "node added by `cut-with-single-formula' at (1)")
	   (weaken (0))
	   (induction integer-inductor ())
	   (block (script-comment "node added by `induction' at (0 0 0)")
		  direct-and-antecedent-inference-strategy
		  (backchain "with(p:prop,forall(m:zz,p));")
		  direct-and-antecedent-inference-strategy
		  (contrapose "with(n,s_$0:zz,s_$0<=n);")
		  simplify)
	   (prove-by-logic-and-simplification 3))

    )))

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


(def-theorem well-ordering-for-integers
  "forall(s:[zz,prop],forsome(y:zz,s(y)) and
     forsome(n:zz, forall(m:zz,m<=n implies not(s(m))))
          implies
     forsome(u:zz, s(u) and forall(v:zz,v<u implies not s(v))))"
  (theory h-o-real-arithmetic)

  (proof
   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(y:zz,s:[zz,prop],s(y));")
    (cut-with-single-formula "y<=n or n<=y")
    (antecedent-inference "with(n,y:zz,y<=n or n<=y);")
    (backchain "with(s:[zz,prop],n:zz,forall(m:zz,m<=n implies not(s(m))));")
    (incorporate-antecedent "with(y,n:zz,n<=y);")
    (force-substitution "not s(y)" "lambda (z:zz,not s(z))(y)" (0))
    (apply-macete-with-minor-premises complete-induction)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("n"))
    (backchain "with(s:[zz,prop],
  forall(u:zz,not(s(u)) or forsome(v:zz,v<u and s(v))));")
    direct-and-antecedent-inference-strategy
    (case-split ("n<=v"))
    (prove-by-logic-and-simplification 3)
    simplify
    beta-reduce-repeatedly
    simplify
    )))

;;;direct-and-antecedent-inference-strategy
;;;(contrapose "with(y:zz,s:[zz,prop],s(y));")
;;;(cut-with-single-formula "y<=n or n<=y")
;;;(antecedent-inference "with(n,y:zz,y<=n or n<=y);")
;;;(backchain "with(s:[zz,prop],n:zz,forall(m:zz,m<=n implies not(s(m))));")
;;;(cut-with-single-formula "forall(z:zz, z<=y implies not(s(z)))")
;;;(backchain "with(s:[zz,prop],y:zz,forall(z:zz,z<=y implies not(s(z))));")
;;;simplify
;;;(incorporate-antecedent "with(y,n:zz,n<=y);")
;;;(induction integer-inductor ()) ; move up  one 
;;;(cut-with-single-formula "z<=t or z=1+t")
;;;(antecedent-inference "with(t,z:zz,z<=t or z=1+t);")
;;;(backchain "with(t:zz,s:[zz,prop],n:zz,
;;;  forall(m:zz,m<=n implies not(s(m)))
;;;   implies 
;;;  forall(z:zz,z<=t implies not(s(z))));")
;;;direct-inference
;;;(backchain "with(t,z:zz,z=1+t);")
;;;(backchain "with(s:[zz,prop],
;;;  forall(u:zz,not(s(u)) or forsome(v:zz,v<u and s(v))));")
;;;direct-and-antecedent-inference-strategy
;;;(backchain "with(t:zz,s:[zz,prop],n:zz,
;;;  forall(m:zz,m<=n implies not(s(m)))
;;;   implies 
;;;  forall(z:zz,z<=t implies not(s(z))));")
;;;direct-and-antecedent-inference-strategy
;;;simplify
;;;simplify
;;;simplify


(def-constant set%min
  "lambda(s:sets[zz], iota(k:zz, k in s and forall(j:zz, j<k implies not(j in s))))"
  (theory h-o-real-arithmetic))

(def-theorem iota-free-characterization-of-set%min
  "forall(s:sets[zz],k:zz,  set%min(s)=k iff (k in s and forall(j:zz, j<k implies not(j in s))))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant-globally set%min)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (contrapose "with(p:prop,p);")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      (contrapose "with(p:prop,p);"))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0)")
      (contrapose "with(k,z:zz,z=k);")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      (contrapose "with(j:zz,s:sets[zz],j in s);")
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
      (apply-macete-with-minor-premises eliminate-iota-macete)
      direct-and-antecedent-inference-strategy
      (contrapose "with(b:zz,s:sets[zz],b in s);")
      (backchain "with(s:sets[zz],k:zz,forall(j:zz,j<k implies not(j in s)));")
      (contrapose "with(k:zz,s:sets[zz],k in s);")
      (backchain "with(s:sets[zz],b:zz,forall(j:zz,j<b implies not(j in s)));")
      simplify)
    )))

(def-theorem definedness-of-set%min
  "forall(s:sets[zz], 
     #(set%min(s)) iff 
     (forsome(k:zz, k in s) and forsome(k:zz, forall(j:zz, j<=k implies not(j in s)))))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-inference
    direct-inference
    (block 
      (script-comment "`direct-inference' at (0)")
      (cut-with-single-formula "forsome(k:zz, set%min(s)=k)")
      (move-to-sibling 1)
      (instantiate-existential ("set%min(s)"))
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(k:zz,p));")
	(incorporate-antecedent "with(k,z:zz,z=k);")
	(apply-macete-with-minor-premises iota-free-characterization-of-set%min)
	direct-and-antecedent-inference-strategy
	(instantiate-existential ("k"))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0)")
	  (instantiate-existential ("k-1"))
	  simplify)))
    (block 
      (script-comment "`direct-inference' at (1)")
      (cut-with-single-formula "forsome(k:zz, set%min(s)=k)")
      (antecedent-inference "with(p:prop,forsome(k:zz,p));")
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises iota-free-characterization-of-set%min)
	(instantiate-theorem well-ordering-for-integers
			     ("lambda(k:zz, k in s)"))
	(block 
	  (script-comment "`instantiate-theorem' at (0 0 0)")
	  (contrapose "with(p:prop,forall(y:zz,p));")
	  simplify-insistently)
	(block 
	  (script-comment "`instantiate-theorem' at (0 0 1)")
	  (contrapose "with(p:prop,forall(n:zz,p));")
	  simplify)
	(block 
	  (script-comment "`instantiate-theorem' at (0 1 0 0)")
	  (beta-reduce-antecedent "with(s:sets[zz],u:zz,
  forall(v:zz,v<u implies not(lambda(k:zz,k in s)(v))));")
	  (beta-reduce-antecedent "with(u:zz,s:sets[zz],lambda(k:zz,k in s)(u));")
	  (instantiate-existential ("u")))))

    )))


(def-theorem well-ordering-for-natural-numbers
  "forall(s:[nn,prop],
     nonvacuous_q{s}
          implies
     forsome(u:nn, s(u) and forall(v:nn,v<u implies not s(v))))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem well-ordering-for-integers ("s"))
    (instantiate-universal-antecedent "with(p:prop, forall(y:zz,p))" ("x_0"))
    (instantiate-universal-antecedent "with(p:prop, forall(n:zz,p))" ("[-1]"))
    (cut-with-single-formula "not(#(m,nn))")
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    auto-instantiate-existential
    (backchain "with(p:prop, forall(v:zz,p))")
    )))

(def-constant floor
  "lambda(x:rr, iota(z:zz,z<=x and x<1+z))"
  (theory h-o-real-arithmetic))

(def-theorem floor-definedness
  "forall(x:rr, #(floor(x)))"
  (usages d-r-convergence)
  (proof
   (
    insistent-direct-inference
    unfold-defined-constants
    (eliminate-iota 0)
    (cut-with-single-formula "forsome(y%iota:zz,y%iota<=x and x<1+y%iota)")
    (instantiate-existential ("y%iota"))
    simplify
    (instantiate-theorem well-ordering-for-integers ("lambda(u:zz,x<u)"))
    (contrapose 0)
    beta-reduce-insistently
    (apply-macete-with-minor-premises archimedean)
    (contrapose 0)
    (cut-with-single-formula "forsome(u:zz,-x<u)")
    (instantiate-existential ("-u"))
    simplify
    (apply-macete-with-minor-premises archimedean)
    (instantiate-existential ("u-1"))
    (instantiate-universal-antecedent 0 ("u-1"))
    simplify
    (contrapose 0)
    simplify
    (simplify-antecedent 0)
    simplify
))
  
  (theory h-o-real-arithmetic))

(def-theorem floor-characterization
  "forall(x:rr, n:zz, floor(x)=n iff (n<=x and x<n+1))"
  (theory h-o-real-arithmetic)
  (proof

   (

    (unfold-single-defined-constant (0) floor)
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify



    )))

(def-theorem floor-below-arg
  "forall(x:rr, floor(x)<=x)"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-inference
    (instantiate-theorem floor-definedness ("x"))
    (incorporate-antecedent "with(p:prop,p);")
    (unfold-single-defined-constant-globally floor)
    direct-and-antecedent-inference-strategy
    (eliminate-defined-iota-expression 0 i))))

(def-theorem floor-plus-1-exceeds-arg
  "forall(x:rr, x<1+floor(x))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-inference
    (instantiate-theorem floor-definedness ("x"))
    (incorporate-antecedent "with(p:prop,p);")
    (unfold-single-defined-constant-globally floor)
    direct-and-antecedent-inference-strategy
    (eliminate-defined-iota-expression 0 i))))

(def-theorem floor-not-much-below-arg
  "forall(x:rr, n:zz, n<=x implies n<=floor(x))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem floor-definedness ("x"))
    (incorporate-antecedent "with(z:zz,#(z));")
    (unfold-single-defined-constant-globally floor)
    direct-and-antecedent-inference-strategy
    (eliminate-defined-iota-expression 0 f)
    simplify)))

(def-theorem floor-inequality-characterization
  "forall(x,y:rr, (floor(x)<=floor(y) iff floor(x)<=y))"
  (theory h-o-real-arithmetic)
  (proof
   (direct-and-antecedent-inference-strategy-with-simplification)))

(def-theorem monotonicity-of-floor
  "forall(x,y:rr, x<=y implies floor(x)<=floor(y))"
  (theory h-o-real-arithmetic)
  (proof
   (simplify)))


(def-theorem integer-exponentiation-definedness 
  "forall(m,n:zz, 1<=n implies #(m^n,zz))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (induction integer-inductor ())
    (apply-macete-with-minor-premises exp-out)
    sort-definedness
    simplify)))

(def-theorem integer-exponentiation-definedness-dr
  "forall(m,n:ind, #(m,zz) and #(n,zz) and 1<=n implies #(m^n,zz))"
  (usages d-r-convergence)
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises integer-exponentiation-definedness)
    simplify)))

(def-theorem product-power-is-iterated-power
  "forall(z:rr, n,m:zz, 1<=n and 1<=m implies z^(n*m) ==(z^n)^m)"
  (theory h-o-real-arithmetic)
  (proof
   (
    simplify)))


(def-constant mod
  "lambda(a,b:rr, a-b*floor(a/b))"
  (theory h-o-real-arithmetic))

(def-parse-syntax mod
  (left-method infix-operator-method)
  (binding 99))

(def-print-syntax mod
  (token " mod ")
  (method present-binary-infix-operator)
  (binding 99))

(def-print-syntax mod
  tex 
  (token "\\; \\mbox{\\rm mod} \\;")
  (method present-tex-binary-infix-operator)
  (binding 99))

(def-theorem mod-of-negative
  "forall(a,b:rr, mod(-b,-a)==-mod(b,a))"
  (theory h-o-real-arithmetic)
  (proof
   (
     
    (unfold-single-defined-constant-globally mod)
    simplify
    )))

(def-constant div
  "lambda(x,y:rr, floor(x/y))"
  (theory h-o-real-arithmetic))


(def-parse-syntax div
  (left-method infix-operator-method)
  (binding 99))

(def-print-syntax div
  (token " div ")
  (method present-binary-infix-operator)
  (binding 99))


(def-theorem mod-of-integer-is-integer
  "forall(a,b:zz, not(b=0) implies #(a mod b,zz))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) mod)
    sort-definedness

    )))
