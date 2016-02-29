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


(herald ARITHMETIC-MACETES)

(def-theorem exp-out   
 "forall(n:zz,x:rr,2<=n implies x^n=x*x^(n-1))"
 
 (proof

  (
   simplify
   ))

 (theory h-o-real-arithmetic))

(def-theorem monotonicity-for-multiplication
 "forall(x,y,r:rr, 0<r implies (r*x<=r*y iff x<=y))"

 (proof

  (
   simplify
   ))

 (theory h-o-real-arithmetic))

(def-theorem strict-monotonicity-for-multiplication
  "forall(x,y,r:rr, 0<r implies (r*x<r*y iff x<y))"
  (proof

   (
    simplify
    ))

  (theory h-o-real-arithmetic))

(def-theorem domain-of-inverse
  "forall(x:rr,#(x^[-1]) iff (#(x) and not(x=0)))"
  (proof


   (

    direct-inference
    (case-split ("x=0"))
    simplify
    simplify


    ))


  (theory h-o-real-arithmetic))

(def-theorem domain-of-quotient 
  "forall(x,y:rr,#(x/y) iff (#(x) and #(y) and not(y=0)))"
  (theory h-o-real-arithmetic)


  (proof

   (

    direct-inference
    (case-split ("y=0"))
    simplify
    simplify

    )))

(def-theorem domain-of-exponentiation
  "forall(x:rr,y:zz,#(x^y) iff (#(x) and #(y) and (not(x=0) or 0<y)))"
  (theory h-o-real-arithmetic)

  (proof

   (

    direct-and-antecedent-inference-strategy
    (contrapose "with(y:zz,x:rr,#(x^y));")
    simplify
    simplify
    simplify


    ))
  )

(def-theorem totality-of-addition 
  "forall(x,y:rr,#(x+y) iff (#(x) and #(y)))"

  (proof

   (
    simplify
    insistent-direct-inference-strategy
    ))

  (theory h-o-real-arithmetic))

(def-theorem totality-of-multiplication;; simplification.
  "forall(x,y:rr,#(x*y) iff (#(x) and #(y)))"


  (proof

   (
    simplify
    insistent-direct-inference-strategy 
    ))

  (theory h-o-real-arithmetic))

(def-theorem inverse-replacement ;;;simplification
  "forall(x:rr,x^[-1] ==1/x)"
  (proof

   (
    simplify
    ))
  (theory h-o-real-arithmetic))

(def-theorem subtraction-replacement 
  "forall(x,y,z,u:rr,x - y =x+[-1]*y)"
  (proof

   (
    simplify
    ))
 
  (theory h-o-real-arithmetic))

(def-theorem negative-replacement
  "forall(x,y,z,u:rr, - y =[-1]*y)"

  (proof

   (
    simplify
    ))
  (theory h-o-real-arithmetic))

(def-theorem multiplication-of-fractions-left 
 "forall(x,y,u:rr,(x/u)*y == (x*y)/u)"

 (proof

   (
    simplify
    ))
 (theory h-o-real-arithmetic))

(def-theorem multiplication-of-fractions-right
 "forall(x,y,u:rr,y*(x/u) == (y*x)/u)"
 (proof

   (
    simplify
    ))
 (theory h-o-real-arithmetic))

(def-theorem multiplication-of-fractions 
 "forall(x,y,z,u:rr,x/u*y/z == (x*y)/(u*z))"
 (proof

   (
    simplify
    ))
 (theory h-o-real-arithmetic))

(def-theorem addition-of-fractions-left 
  "forall(x,y,z,u:rr,x/u + y == (x+u*y)/u)"

  (proof


   (

    direct-inference
    (case-split ("u=0"))
    simplify
    simplify
    ))

  (theory h-o-real-arithmetic))

(def-theorem addition-of-fractions-right
  "forall(x,y,z,u:rr,y+x/u == (x+u*y)/u)"

  (proof

   (
    direct-inference
    (case-split ("u=0"))
    simplify
    simplify
    ))
  (theory h-o-real-arithmetic))

(def-theorem division-of-fractions  
 "forall(x,y,z:rr,(x/y)/z==x/(y*z))"
 (proof
  (
  simplify
  ))
 (theory h-o-real-arithmetic))

(def-theorem division-of-fractions-2 
 "forall(x,y,z:rr,not(z=0) implies x/(y/z)==(x*z)/y)"
 (proof
  (
  simplify
  ))
 (theory h-o-real-arithmetic))

(def-theorem exponents-of-fractions 
  "forall(x,y:rr,n:zz,(x/y)^n ==x^n/y^n)"

  (proof
   (
    direct-inference
    (case-split ("y=0"))
    simplify
    simplify

    ))
  (theory h-o-real-arithmetic))

(def-theorem negative-exponent-replacement 
 "forall(x:rr,n:zz,not(x=0) implies x^([-1]*n)==1/x^n)"

 (proof

  (
   simplify
   ))
 (theory h-o-real-arithmetic))

(def-theorem right-denominator-removal-for-equalities
  "forall(x,y,z:rr, x = y/z iff (#(z^[-1]) and x*z=y))"


  (proof

   (
    direct-inference
    (force-substitution "x=y/z" "z^[-1]*(x*z-y)=0" (0))
    (case-split ("z=0"))
    simplify
    (apply-macete-with-minor-premises cancel)
    (cut-with-single-formula "not(z^[-1]=0)")
    simplify
    (contrapose "with(z:rr,not(z=0));")
    (force-substitution "z" "z*z^[-1]*z" (0))
    simplify
    (cut-with-single-formula "#(z^[-1])")
    (weaken (1))
    simplify
    (case-split ("z=0"))
    simplify
    simplify
    ))
  (theory h-o-real-arithmetic))

(def-theorem left-denominator-removal-for-equalities 
  "forall(x,y,z:rr, y/z=x iff (#(z^[-1]) and x*z=y))"
  (proof

   (
    (force-substitution "y/z=x" "x=y/z" (0))
    (apply-macete-with-minor-premises right-denominator-removal-for-equalities)
    direct-and-antecedent-inference-strategy
    ))

  (theory h-o-real-arithmetic))

(def-theorem equality-of-fractions
  "forall(x,y,z,u:rr, x/u = y/z iff (#(u^[-1]) and #(z^[-1]) and x*z=y*u))"

  (proof

   (
    (apply-macete-with-minor-premises right-denominator-removal-for-equalities)
    (apply-macete-with-minor-premises multiplication-of-fractions-left)
    (apply-macete-with-minor-premises left-denominator-removal-for-equalities)
    direct-and-antecedent-inference-strategy
    ))
  (theory h-o-real-arithmetic))

(def-theorem positivity-of-inverse 
  "forall(x:rr,0<x^[-1] iff 0<x)"

  (proof

   (

    (cut-with-single-formula "forall(x:rr, 0<x implies 0<x^[-1])")
    direct-and-antecedent-inference-strategy
    (force-substitution "x" "(x^[-1])^[-1]" (0))
    (backchain "forall(x:rr,0<x implies 0<x^[-1]);")
    simplify
    (backchain "forall(x:rr,0<x implies 0<x^[-1]);")
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "0<x^[-1] or 0=x^[-1] or 0<[-1]*x^[-1]")
    (antecedent-inference "with(x:rr,0<x^[-1] or 0=x^[-1] or 0<[-1]*x^[-1]);")
    (cut-with-single-formula "1=x*x^[-1]")
    (contrapose "with(x:rr,1=x*x^[-1]);")
    simplify
    (weaken (0))
    simplify
    (cut-with-single-formula "0<x*([-1]*x^[-1])")
    (contrapose "with(x:rr,0<x*([-1]*x^[-1]))")
    (weaken (0 1 2))
    (case-split ("x=0"))
    simplify
    simplify
    (apply-macete-with-minor-premises strict-positivity-for-products)
    simplify
    simplify

    ))
  (theory h-o-real-arithmetic))
  
(def-theorem right-denominator-removal-for-strict-inequalities 
  "forall(x,y,z:rr, 0<z implies x < y/z iff x*z<y)"
  (proof

   (
    (force-substitution "x<y/z" "0<z^[-1]*(y-x*z)" (0))
    direct-inference
    direct-inference
    (cut-with-single-formula "0<z^[-1]")
    simplify
    (apply-macete-with-minor-premises positivity-of-inverse)
    (weaken (0))
    (case-split ("z=0"))
    simplify
    simplify
    ))

  (theory h-o-real-arithmetic))

(def-theorem left-denominator-removal-for-strict-inequalities 
  "forall(x,y,z:rr, 0<z implies y/z<x iff y<x*z)"

  (proof

   (

    (force-substitution "y/z<x" "0<z^[-1]*(x*z-y)" (0))
    direct-inference
    direct-inference
    (cut-with-single-formula "0<z^[-1]")
    simplify
    (apply-macete-with-minor-premises positivity-of-inverse)
    (weaken (0))
    (case-split ("z=0"))
    simplify
    simplify


    ))
 
  (theory h-o-real-arithmetic))

(def-theorem right-denominator-removal-for-inequalities
 "forall(x,y,z:rr, 0<z implies x <= y/z iff x*z<=y)"
 (theory h-o-real-arithmetic)

   (proof

   (
    (force-substitution "x<=y/z" "0<=z^[-1]*(y-x*z)" (0))
    direct-inference
    direct-inference
    (cut-with-single-formula "0<z^[-1]")
    simplify
    (apply-macete-with-minor-premises positivity-of-inverse)
    (weaken (0))
    (case-split ("z=0"))
    simplify
    simplify
    )))

(def-theorem left-denominator-removal-for-inequalities  
  "forall(x,y,z:rr, 0<z implies y/z<=x iff y<=x*z)"
  (theory h-o-real-arithmetic)

  (proof

   (
    (force-substitution "y/z<=x" "0<=z^[-1]*(x*z-y)" (0))
    direct-inference
    direct-inference
    (cut-with-single-formula "0<z^[-1]")
    simplify
    (apply-macete-with-minor-premises positivity-of-inverse)
    (weaken (0))
    (case-split ("z=0"))
    simplify
    simplify
    )))

(def-theorem positivity-for-r^n
  "forall(r:rr,n:zz,0<r implies 0<r^n)"
  (theory h-o-real-arithmetic)
  (proof
   (
    
    (cut-with-single-formula "forall(r:rr,n:zz,0<r and 0<=n implies 0<r^n)")
    direct-and-antecedent-inference-strategy
    (case-split ("0<=n"))
    (backchain "forall(r:rr,n:zz,0<r and 0<=n implies 0<r^n);")
    direct-and-antecedent-inference-strategy
    (force-substitution "r^n" "(r^[-1])^([-1]*n)" (0))
    (backchain "forall(r:rr,n:zz,0<r and 0<=n implies 0<r^n);")
    (apply-macete-with-minor-premises positivity-of-inverse)
    simplify
    simplify
    (induction integer-inductor ("n"))
    (force-substitution "r^(1+t)" "r^t*r" (0))
    (apply-macete-with-minor-premises strict-positivity-for-products)
    direct-inference
    simplify
    
    )))

(def-compound-macete fractional-expression-manipulation
  (series
   beta-reduce
   (repeat
    inverse-replacement
    subtraction-replacement
    negative-replacement
    addition-of-fractions-left
    addition-of-fractions-right
    multiplication-of-fractions-left
    multiplication-of-fractions-right
    division-of-fractions
    division-of-fractions-2
    exponents-of-fractions
    negative-exponent-replacement)
   (repeat
    left-denominator-removal-for-equalities
    right-denominator-removal-for-equalities
    right-denominator-removal-for-strict-inequalities
    left-denominator-removal-for-strict-inequalities
    right-denominator-removal-for-inequalities
    left-denominator-removal-for-inequalities
    multiplication-of-fractions-left
    multiplication-of-fractions-right)))

(def-theorem non-zero-product
  "forall(x,y:rr, #(x) and #(y) and not(x=0) and not(y=0) implies not(x*y=0))"
  (proof
   (
    (apply-macete-with-minor-premises cancel)
    
    ))
  (theory h-o-real-arithmetic))

(def-script prove-iteration-operator-definedness 3 
  ;;$1 is lower var -- a string
  ;;$2 is upper var -- a string
  ;;$3 is iteration operator name -- a symbol
  (
   direct-inference
   (case-split ((% "~A<=~A" $1 $2)))
   (induction integer-inductor ())
   (prove-by-logic-and-simplification 3)
   (unfold-single-defined-constant (0) $3)
   simplify
   ))

(def-theorem sum-definedness
  "forall(m,n:zz,f:[zz,rr],forall(k:zz,m<=k and k<=n implies #(f(k))) 
             implies  
             #(sum(m,n,f)))"
  (theory h-o-real-arithmetic)
  
  (proof
   
   (
    (prove-iteration-operator-definedness "m" "n" sum)
    
    ))


  (usages d-r-convergence))

(def-theorem prod-definedness 
  "forall(m,n:zz,f:[zz,rr],forall(k:zz,m<=k and k<=n implies #(f(k))) 
             implies
            #(prod(m,n,f)))"
  (theory h-o-real-arithmetic)
  
  (proof
   
   (
    (prove-iteration-operator-definedness "m" "n" prod)
    ))
  
  (usages d-r-convergence))

(def-theorem prod-non-zero  
  "forall(m,n:zz,f:[zz,rr],forall(k:zz,m<=k and k<=n implies not(f(k)=0))
            implies 
         not(prod(m,n,f)=0))"

  (proof

   (

    direct-inference
    (case-split ("m<=n"))
    (induction integer-inductor ())
    (case-split ("#(f(1+t)) and #(prod(m,t,f))"))
    (apply-macete-with-minor-premises cancel)
    (contrapose "with(t,m:zz,m<=t);")
    (antecedent-inference "with(m,t:zz,f:[zz,rr],f(1+t)=0 or prod(m,t,f)=0);")
    (contrapose "with(t:zz,f:[zz,rr],f(1+t)=0);")
    (prove-by-logic-and-simplification 3)
    (contrapose "with(f:[zz,rr],t,m:zz,prod(m,t,f)=0);")
    (prove-by-logic-and-simplification 3)
    (contrapose "with(m,t:zz,f:[zz,rr],not(#(f(1+t)) and #(prod(m,t,f))));")
    simplify
    (unfold-single-defined-constant (0) prod)
    simplify

    ))
  (theory h-o-real-arithmetic))

(def-theorem monotonicity-for-sum
  "forall(f,g:[zz,rr], a,b:zz, forall(z:zz,a<=z and z<=b implies f(z)<=g(z))
                       implies sum(a,b,f)<=sum(a,b,g))"


  (proof

   (

    direct-and-antecedent-inference-strategy
    (case-split ("a<=b"))
    (induction integer-inductor ())
    direct-inference
    (cut-with-single-formula "f(1+t)<=g(1+t) and sum(a,t,f)<=sum(a,t,g)")
    simplify
    (prove-by-logic-and-simplification 3)
    (unfold-single-defined-constant (0 1) sum)
    simplify

    )

   )
  (theory h-o-real-arithmetic))

(def-theorem monotonicity-of-inverse
  "forall(x,y:rr,0<x and 0<y implies y^[-1]<=x^[-1] iff x<=y)"
 
  (proof
   (
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    ))
  

  (theory h-o-real-arithmetic))

(def-theorem strict-monotonicity-of-inverse  
 "forall(x,y:rr,0<x and 0<y implies y^[-1]<x^[-1] iff x<y)"
  (proof
   (
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    ))
  (theory h-o-real-arithmetic))

(def-theorem absolute-value-inversion 
  "forall(x:rr, abs(x^[-1])==abs(x)^[-1])"
  (theory h-o-real-arithmetic)

  (proof
   (
    direct-inference
    unfold-defined-constants
    (cut-with-single-formula "0<x or 0=x or x<0")
    (antecedent-inference "with(x:rr,0<x or 0=x or x<0);")
    (cut-with-single-formula "0<x^[-1]")
    simplify
    (apply-macete-with-minor-premises positivity-of-inverse)
    simplify
    (cut-with-single-formula "x^[-1]<0")
    simplify
    (force-substitution "x^[-1]<0" "0<([-1]*x)^[-1]" (0))
    (apply-macete-with-minor-premises positivity-of-inverse)
    simplify
    simplify
    simplify

    )))

(def-theorem absolute-value-product
  "forall(x,y:rr,abs(x*y)=abs(x)*abs(y))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-inference
    unfold-defined-constants
    (cut-with-single-formula "0<x and 0<y and 0<x*y or 0<x and y<0 and 0<[-1]*y*x or 
 0<y and x<0 and 0<[-1]*x*y or x<0 and y<0 and 0<([-1]*y)*([-1]*x) or (x=0 or y=0) and x*y=0")
    (prove-by-logic-and-simplification 3)
    (apply-macete-with-minor-premises strict-positivity-for-products)
    (apply-macete-with-minor-premises cancel)
    (prove-by-logic-and-simplification 3)

    )))

(def-theorem absolute-value-quotient
  "forall(x,y:rr,abs(x/y)==abs(x)/abs(y))"
  (theory h-o-real-arithmetic)
  (proof

   (
    simplify
    (apply-macete-with-minor-premises absolute-value-product)
    (apply-macete-with-minor-premises absolute-value-inversion)

    )))

(def-theorem absolute-value-zero
  "forall(x:rr,abs(x)=0 iff x=0)"
  (theory h-o-real-arithmetic)
  (proof
   (
    unfold-defined-constants
    direct-inference
    (case-split ("0<=x"))
    simplify
    simplify
    )))

(def-theorem absolute-value-non-negative
  "forall(x:rr,0<=x implies abs(x)=x)"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    simplify

    ))
  )

(def-theorem absolute-value-non-positive
  "forall(x:rr,x<=0 implies abs(x)=-x)"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    (case-split ("x<0"))
    simplify
    simplify
    ))
  )

(def-theorem absolute-value-absolute-value
  "forall(x:rr,abs(abs(x))=abs(x))"
  (theory h-o-real-arithmetic)
  (usages rewrite)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete absolute-value-non-negative)
    )))

(def-compound-macete integer-induction
  (sequential
   (sound
    abstraction-for-induction
    beta-reduce
    beta-reduce)
   induct))

(def-theorem ()
  "forall(x,y:zz, #(max(x,y),zz))"
  (theory h-o-real-arithmetic)
  (usages d-r-convergence)
  (proof
   (
    unfold-defined-constants
    ))
  )

(def-theorem ()
  "forall(x,y:zz,#(min(x,y),zz))"
 (theory h-o-real-arithmetic)
 (proof
   (
    unfold-defined-constants
    ))
 (usages d-r-convergence))

(def-theorem factorial-non-zero
  "forall(m:zz,not(m!=0))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant (0) factorial)
    (apply-macete-with-minor-premises prod-non-zero)
    simplify
    )))

(def-theorem factorial-non-zero-1
  "forall(m:zz, y:rr, m!=y implies not(y=0))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (backchain-backwards "with(y:rr,m:zz,m!=y);")
    (apply-macete-with-minor-premises factorial-non-zero)
    ))
  (usages d-r-value))

(def-theorem factorial-out
  "forall(m:zz,1<=m implies m!=(m-1)!*m)"

  (proof

   (
    (unfold-single-defined-constant (0 1) factorial)
    (unfold-single-defined-constant (0) prod)
    simplify
    ))
  (theory h-o-real-arithmetic))

(def-theorem factorial-definedness
  "forall(m:zz,#(m!))"
  (proof
   (
    (unfold-single-defined-constant (0) factorial)
    insistent-direct-inference
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises prod-definedness)
    simplify

    )
   )
  (theory h-o-real-arithmetic)
  (usages d-r-convergence))

;;;(def-compound-macete arithmetic-manipulations
;;;  (series
;;;   (repeat
;;;    beta-reduce
;;;    addition-of-fractions-left
;;;    addition-of-fractions-right
;;;    multiplication-of-fractions-left
;;;    multiplication-of-fractions-right
;;;    equality-of-fractions
;;;    left-denominator-removal-for-equalities
;;;    right-denominator-removal-for-equalities)
;;;   (repeat
;;;    (without-minor-premises factorial-out)
;;;    beta-reduce)))
;;;
(def-compound-macete definedness-manipulations
  (series
   (repeat
    totality-of-addition
    totality-of-multiplication
    domain-of-exponentiation
    domain-of-inverse
    non-zero-product
    factorial-non-zero
    sum-definedness
    factorial-definedness)
   simplify))

(def-theorem monotone-product-lemma
  "forall(x,y,z,u:rr, 0<=x and x<=y and 0<=u and u<=z implies x*u<=y*z)"

  (proof

   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("x*z"))
    (cut-with-single-formula "0<=x*(z-u)")
    simplify
    (apply-macete-with-minor-premises positivity-for-products)
    simplify
    (cut-with-single-formula "0<=(y-x)*z")
    simplify
    (apply-macete-with-minor-premises positivity-for-products)
    simplify


    )


   )
  (theory h-o-real-arithmetic))

(def-theorem prod-definedness-converse
  "forall(m,n:zz,f:[zz,rr], 
      #(prod(m,n,f))
         implies
      forall(k:zz,m<=k and k<=n implies #(f(k))))"
  (theory h-o-real-arithmetic)
  
  (proof
   
   (


    direct-inference
    direct-inference
    (case-split ("m<=n"))
    (induction integer-inductor ())
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "k_$0=m")
    simplify
    simplify
    (case-split ("k=1+t"))
    simplify
    simplify
    direct-and-antecedent-inference-strategy
    (simplify-antecedent "with(p:prop,not(p));")
    ))
  )

(def-theorem monotonicity-of-exponentiation
  "forall(a:rr, x,y:zz, x<=y and 0<a and a<=1 implies a^y<=a^x)"
  (theory h-o-real-arithmetic)
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

    )))