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


(herald pre-reals)

(include-files 
 (files (imps theories/reals/reals)))

(def-theory ORDERED-FIELD
  (language pre-numerical-structures)
  (axioms
   (trichotomy-pre-reals "forall(y,x:rr,x<y or x=y or y<x)")
   (irreflexivity "not(0<0)")
   (strict-positivity-for-products-pre-reals "forall(y,x:rr,(0<x and 0<y) implies 0<x*y)")
   (<-translated "forall(z,y,x:rr,x<y iff x+z<y+z)")
   (transitivity-pre-reals "forall(z,y,x:rr,(x<y and y<z) implies x<z)")
   (negative-characterization-pre-reals "forall(x:rr,x+(-x)=0)")
   (0-characterization "forall(x:rr,x+0=x)")
   (associative-law-for-multiplication-pre-reals "forall(z,y,x:rr,(x*y)*z=x*(y*z))")
   (left-distributive-law-pre-reals "forall(z,y,x:rr,x*(y+z)=x*y+x*z)")
   (multiplicative-identity-pre-reals "forall(x:rr,1*x=x)")
   (commutative-law-for-multiplication-pre-reals "forall(y,x:rr,x*y=y*x)")
   (associative-law-for-addition-pre-reals "forall(z,y,x:rr,(x+y)+z=x+(y+z))")
   (commutative-law-for-addition-pre-reals "forall(y,x:rr,x+y=y+x)")
   (division-characterization-pre-reals "forall(a,b:rr, not(b=0) implies b*(a/b)=a)")
   (div-by-zero-undefined-pre-reals "forall(a,b:ind,b=0 implies not(#(a/b)))")
   (zz-+-closed "forall(x,y:zz,#(x+y,zz))")
   (zz-minus-closed "forall(x:zz,#(-x,zz))")
   (induction-pre-reals "forall(s:[zz,prop],forall(t:zz,0<t implies s(t)) 
 iff (s(1) and forall(t:zz,0<t implies (s(t) implies s(t+1)))))")
   (negative-one-characterization "[-1]=-1" rewrite)
   (zz-quotient-field-pre-reals "forall(x:rr, #(x,qq) iff forsome(a,b:zz,x=a/b))")

   ))   

;;(set (current-theory) (name->theory 'ordered-field))

(def-constant <=
  "lambda(x,y:rr, x=y or x<y)"
  (theory ordered-field))


(def-theorem <=-characterization
  "forall(y,x:rr,x<=y iff (x=y or x<y))"
  (theory ordered-field)
  (proof

   (
    unfold-defined-constants
    )))

(def-constant SUB
 "lambda(x,y:rr,x+(-y))"
 (theory ordered-field))

(def-theorem ()
  "total_q(+,[rr,rr,rr])" 
  (theory ordered-field)
  (proof
   (
    (assume-theorem associative-law-for-addition-pre-reals)
    insistent-direct-inference
    ))
  (usages d-r-convergence))


(def-theorem ()
  "total_q(*,[rr,rr,rr])" 
  (theory ordered-field)
  (usages d-r-convergence)
  (proof
   (
    (assume-theorem associative-law-for-multiplication-pre-reals)
    insistent-direct-inference
    )))

(def-theorem ()
  "total_q(-,[rr,rr])" 
  (theory ordered-field)
  (usages d-r-convergence)
  (proof
   (
    (assume-theorem negative-characterization-pre-reals)
    insistent-direct-inference
    )))

(def-theorem ()
  "forall(y,x:rr,x-y=x+-y)"
  (proof

   (
    unfold-defined-constants
    simplify
    ))
  (theory ordered-field))

(def-theorem ()
  "total_q{sub,[rr,rr,rr]}"
  (theory ordered-field)
  (proof
   (
    unfold-defined-constants
    insistent-direct-inference-strategy
    beta-reduce-repeatedly

    )))

(def-theorem ()
  "forall(x,y:rr,not(y=0) implies #(x/y))"
  (theory ordered-field)
  (usages d-r-convergence)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "y*(x/y)=x")
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    )))

(def-theorem add-right-cancellation
  "forall(a,b,c:rr, b+a=c+a iff b=c)"
  lemma
  (theory ordered-field)
  (proof

   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(b,a:rr,a=b)")
    (force-substitution "b+a=c+a" "b+a+-a=c+a+-a" (0))
    (apply-macete-with-minor-premises associative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises negative-characterization-pre-reals)
    (apply-macete-with-minor-premises 0-characterization)
    direct-and-antecedent-inference-strategy

    )))

(def-theorem add-left-cancellation
  "forall(a,b,c:rr, a+b=a+c iff b=c)"
  lemma
  (theory ordered-field)
  (proof

   (
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises add-right-cancellation)
    )))


(def-theorem times-right-cancellation
  "forall(a,b,c:rr, not(a=0) implies b*a=c*a iff b=c)"
  lemma
  (theory ordered-field)
  (proof

   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(b,a:rr,a=b)")
    (force-substitution "b*a=c*a" "b*a*(1/a)=c*a*(1/a)" (0))
    (apply-macete-with-minor-premises associative-law-for-multiplication-pre-reals)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
    (apply-macete-with-minor-premises multiplicative-identity-pre-reals)
    (weaken (0))
    direct-and-antecedent-inference-strategy
    simplify
    )))


(def-theorem times-left-cancellation
  "forall(a,b,c:rr, not(a=0) implies a*b=a*c iff b=c)"
  lemma
  (theory ordered-field)
  (proof

   (
    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
    (apply-macete-with-minor-premises times-right-cancellation)

    )))
  
(def-theorem 0-times-is-0
  "forall(a:rr, a*0=0)"
  lemma
  (theory ordered-field)
  (proof
   (
    direct-inference
    (cut-with-single-formula "a*0+a*0=a*0+0")
    (incorporate-antecedent "with(a:rr,a*0+a*0=a*0+0)")
    (apply-macete-with-minor-premises add-left-cancellation)
    (apply-macete-with-minor-premises 0-characterization)
    (force-substitution "0" "(0+0)" (2))
    (apply-macete-with-minor-premises left-distributive-law-pre-reals)
    (apply-macete-with-minor-premises 0-characterization)

    )))

(def-theorem cancel-pre-reals  
  "forall(a,b:rr,a*b=0 iff (a=0 or b=0))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(b,a:rr,a*b=0)")
    (force-substitution "0" "a*0" (0))
    (apply-macete-with-minor-premises times-left-cancellation)
    (apply-macete-with-minor-premises 0-times-is-0)
    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
    (backchain "with(a:rr,a=0)")
    (apply-macete-with-minor-premises 0-times-is-0)
    (backchain "with(b:rr,b=0)")
    (apply-macete-with-minor-premises 0-times-is-0)

    )))


(def-theorem positivity-for-products-pre-reals 
  "forall(y,x:rr,(0<=x and 0<=y) implies 0<=x*y)"
  (theory ordered-field)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises <=-characterization)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises strict-positivity-for-products-pre-reals)
    direct-inference
    (contrapose "with(x:rr,0<=x)")
    (apply-macete-with-minor-premises <=-characterization)
    (contrapose "with(x:rr,not(0<x))")
    (antecedent-inference "with(x:rr,0=x or 0<x)")
    (contrapose "with(y,x:rr,not(0=x*y))")
    (force-substitution "0=x*y" "x*y=0" (0))
    (apply-macete-with-minor-premises cancel-pre-reals)
    direct-and-antecedent-inference-strategy
    simplify
    (contrapose "with(y:rr,0<=y)")
    (apply-macete-with-minor-premises <=-characterization)
    (contrapose "with(y:rr,not(0<y))")
    (antecedent-inference "with(y:rr,0=y or 0<y)")
    (contrapose "with(y,x:rr,not(0=x*y))")
    (force-substitution "0=x*y" "x*y=0" (0))
    (apply-macete-with-minor-premises cancel-pre-reals)
    direct-inference
    simplify

    )))

(def-theorem <-translated-reverse
  "forall(z,y,x:rr,x+z<y+z iff x<y)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises <-translated)
    auto-instantiate-existential
    (apply-macete-with-minor-premises <-translated)
    (apply-macete-with-minor-premises associative-law-for-addition-pre-reals)
    (instantiate-existential ("-z"))
    (apply-macete-with-minor-premises negative-characterization-pre-reals)
    (apply-macete-with-minor-premises 0-characterization)

    )))



(def-theorem <=-translated
  "forall(z,y,x:rr,x<=y iff x+z<=y+z)"
  reverse
  (theory ordered-field)
  (proof
   (

    (apply-macete-with-minor-premises <=-characterization)
    direct-and-antecedent-inference-strategy
    (contrapose "with(y,z,x:rr,not(x+z=y+z))")
    (apply-macete-with-minor-premises <-translated)
    (apply-macete-with-minor-premises associative-law-for-addition-pre-reals)
    (instantiate-existential ("-z"))
    (apply-macete-with-minor-premises negative-characterization-pre-reals)
    (apply-macete-with-minor-premises 0-characterization)
    (contrapose "with(y,z,x:rr,x+z=y+z)")
    (apply-macete-with-minor-premises add-right-cancellation)
    (apply-macete-with-minor-premises <-translated)
    (instantiate-existential ("z"))

    )))


(def-theorem transitivity-of-<=-pre-reals
  "forall(z,y,x:rr,(x<=y and y<=z) implies x<=z)"
  (theory ordered-field)
  (proof

   (

    (apply-macete-with-minor-premises <=-characterization)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    (apply-macete-with-minor-premises transitivity-pre-reals)
    (instantiate-existential ("y"))

    )))


(def-theorem negative-times-negative
  "(-1)*(-1)=1"
  (theory ordered-field)
  (proof

   (
    (cut-with-single-formula "1+-1=(-1)*(-1)+-1")
    (contrapose "with(a,b:rr,a=b)")
    (apply-macete-with-minor-premises add-right-cancellation)
    simplify
    (apply-macete-with-minor-premises negative-characterization-pre-reals)
    (force-substitution "(-1)*(-1)+-1" "(-1)*(-1+1)" (0))
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises negative-characterization-pre-reals)
    (apply-macete-with-minor-premises 0-times-is-0)
    (apply-macete-with-minor-premises left-distributive-law-pre-reals)
    insistent-direct-inference
    (apply-macete-with-minor-premises add-left-cancellation)
    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
    (apply-macete-with-minor-premises multiplicative-identity-pre-reals)
    )))


(def-theorem 1-positive
  "0<1"
  (theory ordered-field)
  (proof
   (
    (cut-with-single-formula "1<0 or 1=0 or 0<1")
    (antecedent-inference "1<0 or 1=0 or 0<1")
    (force-substitution "1" "(-1)*(-1)" (0))
    (apply-macete-with-minor-premises strict-positivity-for-products-pre-reals)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises <-translated)
    (instantiate-existential ("1"))
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises negative-characterization-pre-reals)
    (apply-macete-with-minor-premises 0-characterization)
    (apply-macete-with-minor-premises negative-times-negative)
    (contrapose "1=0")
    (apply-macete-with-minor-premises trichotomy-pre-reals)

    )))



(def-theorem 1-not-negative
  "not(1<0)"
  (theory ordered-field)
  (proof
   (
    (cut-with-single-formula "not(0<0)")
    (contrapose "not(0<0)")
    (apply-macete-with-minor-premises transitivity-pre-reals)
    (instantiate-existential ("1"))
    (force-substitution "1" "(-1)*(-1)" (0))
    (apply-macete-with-minor-premises strict-positivity-for-products-pre-reals)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises <-translated)
    (instantiate-existential ("1"))
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises negative-characterization-pre-reals)
    (apply-macete-with-minor-premises 0-characterization)
    (apply-macete-with-minor-premises negative-times-negative)
    (apply-macete-with-minor-premises irreflexivity)

    )))

(def-theorem order-discreteness-pre-reals
  "forall(m,n:zz, m<n iff m+1<=n)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises <=-translated)
    (instantiate-existential ("-m"))
    (apply-macete-with-minor-premises associative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises negative-characterization-pre-reals)
    (apply-macete-with-minor-premises 0-characterization)
    (contrapose "with(n,m:zz,m<n)")
    (force-substitution "m<n" "m+-m<n+-m" (0))
    (apply-macete-with-minor-premises negative-characterization-pre-reals)
    (contrapose "with(m,n:zz,not(1<=n+-m))")
    (cut-with-single-formula "forall(m:zz,0<m implies 1<=m)")
    (backchain "forall(m:zz,0<m implies 1<=m)")
    (apply-macete-with-minor-premises zz-+-closed)
    (apply-macete-with-minor-premises zz-minus-closed)
    (force-substitution "1<=m" "lambda(m:zz,1<=m)(m)" (0))
    (apply-macete-with-minor-premises induction-pre-reals)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises <=-characterization)
    beta-reduce-with-minor-premises
    (force-substitution "1" "0+1" (0))
    (apply-macete-with-minor-premises rev%<=-translated)
    (apply-macete-with-minor-premises <=-characterization)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises 0-characterization)
    (apply-macete-with-minor-premises zz-+-closed)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises <-translated-reverse)
    (incorporate-antecedent "with(n,m:zz,m+1<=n)")
    (apply-macete-with-minor-premises <=-characterization)
    direct-and-antecedent-inference-strategy
    (backchain-backwards "with(n,m:zz,m+1=n)")
    (force-substitution "m" "m+0" (0))
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises <-translated-reverse)
    (apply-macete-with-minor-premises 1-positive)
    (apply-macete-with-minor-premises 0-characterization)
    (apply-macete-with-minor-premises transitivity-pre-reals)
    (instantiate-existential ("m+1"))
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (force-substitution "m" "0+m" (0))
    (apply-macete-with-minor-premises <-translated-reverse)
    (apply-macete-with-minor-premises 1-positive)
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises 0-characterization)

    )))

(def-algebraic-processor pre-rr-algebraic-processor
  cancellative
  (language ordered-field)
  (base ((scalars *rational-type*)
	 (operations
	  (zero 0)
	  (unit 1)
	  (+ +)
	  (* *)
	  (- -)
	  (sub sub))
	 commutes)))

(def-order-processor pre-rr-order
  (algebraic-processor pre-rr-algebraic-processor)
  (operations (< <) (<= <=))
  (discrete-sorts zz))
  
(def-theory-processors ordered-field
 (algebraic-simplifier (pre-rr-algebraic-processor * + - sub))
 (algebraic-order-simplifier (pre-rr-order < <=))
 (algebraic-term-comparator pre-rr-order))

;; Add usages: Try proving the next theorem BEFORE installing them and notice the difference.

(def-theorem zz-+-closed 
  zz-+-closed
  (theory ordered-field)
  (proof existing-theorem)
  (usages d-r-convergence))

(def-theorem zz-minus-closed 
  zz-minus-closed 
  (theory ordered-field)
  (proof existing-theorem)
  (usages d-r-convergence))

(def-theorem zz-sub-closed
  "forall(x,y:zz,#(x-y,zz))"
  (theory ordered-field)
  (proof
   (
    unfold-defined-constants
    simplify
    ))
  (usages d-r-convergence))

(def-theorem div-by-zero-undefined-pre-reals
  div-by-zero-undefined-pre-reals
  (theory ordered-field)
  (proof existing-theorem)
  (usages d-r-convergence))

(def-theorem () 
  "forall(x,y:rr,not(y=0) implies #(x/y))" 
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "y*(x/y)=x")
    (apply-macete-with-minor-premises division-characterization-pre-reals)

    ))
  (usages d-r-convergence))

(def-theorem division-non-zero
  "forall(x,y:rr,x/y=0 iff (not(y=0) and x=0))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(x/y)")
    (contrapose "with(y,x:rr,#(x/y))")
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    (force-substitution "x" "y*(x/y)" (0))
    simplify
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (cut-with-single-formula "y*(x/y)=y*0")
    (contrapose "with(x,y:rr,y*(x/y)=y*0)")
    (apply-macete-with-minor-premises times-left-cancellation)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    )))

(def-theorem inverse-of-inverse
  "forall(x:rr,not(x=0) implies 1/(1/x)=x)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "1/x*(1/(1/x))=(1/x)*x")
    (contrapose "with(x:rr,1/x*(1/(1/x))=1/x*x)")
    (apply-macete-with-minor-premises times-left-cancellation)
    (apply-macete-with-minor-premises division-non-zero)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (apply-macete-with-minor-premises division-non-zero)

    )))

(def-theorem product-division-interchange
  "forall(x,y,z:rr, x*(y/z)==(x*y)/z)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("z=0"))
    (cut-with-single-formula "not(#(y/0)) and not(#((x*y)/0))")
    insistent-direct-inference-strategy
    (antecedent-inference "with(z,y,x:rr,#(x*(y/z)) or #((x*y)/z))")
    simplify
    simplify
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    insistent-direct-inference
    (weaken (0))
    (cut-with-single-formula "z*(x*(y/z))=z*((x*y)/z)")
    (contrapose "with(y,x,z:rr,z*(x*(y/z))=z*((x*y)/z))")
    (apply-macete-with-minor-premises times-left-cancellation)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (force-substitution "z*(x*(y/z))" "z*y/z*x" (0))
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    simplify

    )))

(def-theorem inverse-of-product
  "forall(x,y:rr,not(x=0) and not(y=0) implies 1/(x*y)=(1/x)*(1/y))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "x*y*(1/(x*y))=x*y*((1/x)*(1/y))")
    (contrapose "with(y,x:rr,x*y*(1/(x*y))=x*y*(1/x*(1/y)))")
    (apply-macete-with-minor-premises times-left-cancellation)
    (apply-macete-with-minor-premises cancel-pre-reals)
    (contrapose "with(y:rr,not(y=0))")
    (antecedent-inference "with(x,y:rr,y=0 or x=0)")
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (apply-macete-with-minor-premises associative-law-for-multiplication-pre-reals)
    (force-substitution "y*(1/x*(1/y))" "y*(1/y)*1/x" (0))
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    (apply-macete-with-minor-premises cancel-pre-reals)
    (contrapose "with(y:rr,not(y=0))")
    (antecedent-inference "with(x,y:rr,y=0 or x=0)")

    )))

(def-theorem general-induction
  "forall(s:[zz,prop],m:zz,forall(t:zz,m<=t implies s(t)) 
 iff (s(m) and forall(t:zz,m<=t implies (s(t) implies s(t+1)))))"
  (theory ordered-field)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (backchain "with(s:[zz,prop],m:zz,forall(t:zz,m<=t implies s(t)))")
    simplify
    (backchain "with(s:[zz,prop],m:zz,forall(t:zz,m<=t implies s(t)))")
    simplify
    (instantiate-theorem induction-pre-reals ("lambda(n:zz,s(n+m-1))"))
    (beta-reduce-antecedent "with(m:zz,s:[zz,prop],
  forall(t:zz,0<t implies lambda(n:zz,s(n+m-1))(t)))")
    (force-substitution "t" "(t-m+1)+m-1" (0))
    (backchain "with(m:zz,s:[zz,prop],forall(t:zz,0<t implies s(t+m-1)))")
    simplify
    simplify
    (simplify-antecedent "with(m:zz,s:[zz,prop],not(lambda(n:zz,s(n+m-1))(1)))")
    (contrapose "with(t_$0,m:zz,s:[zz,prop],
  not(lambda(n:zz,s(n+m-1))(t_$0+1)))")
    (incorporate-antecedent "with(t_$0,m:zz,s:[zz,prop],lambda(n:zz,s(n+m-1))(t_$0))")
    beta-reduce-with-minor-premises
    (force-substitution "t_$0+1+m-1" "(t_$0+m-1)+1" (0))
    (backchain "with(s:[zz,prop],m:zz,
  forall(t:zz,m<=t implies (s(t) implies s(t+1))))")
    simplify
    simplify

    )))

;;;    Here's a proof without d-r-convergence:

;;;    direct-and-antecedent-inference-strategy
;;;    (backchain "with(s:[zz,prop],m:zz,forall(t:zz,m<=t implies s(t)))")
;;;    simplify
;;;    (backchain "with(s:[zz,prop],m:zz,forall(t:zz,m<=t implies s(t)))")
;;;    simplify
;;;    (apply-macete-with-minor-premises zz-+-closed)
;;;    (instantiate-theorem induction-pre-reals ("lambda(n:zz,s(n+m-1))"))
;;;    (incorporate-antecedent "with(m:zz,s:[zz,prop],
;;;  forall(t:zz,0<t implies lambda(n:zz,s(n+m-1))(t)))")
;;;    beta-reduce-with-minor-premises
;;;    direct-and-antecedent-inference-strategy
;;;    (instantiate-universal-antecedent "with(m:zz,s:[zz,prop],forall(t:zz,0<t implies s(t+m-1)))" ("t-m+1"))
;;;    (contrapose "with(m,t:zz,not(0<t-m+1))")
;;;    simplify
;;;    (simplify-antecedent "with(m,t:zz,s:[zz,prop],s(t-m+1+m-1))")
;;;    (apply-macete-with-minor-premises zz-+-closed)
;;;    (apply-macete-with-minor-premises zz-+-closed)
;;;    (force-substitution "[-1]*m" "-m" (0))
;;;    (apply-macete-with-minor-premises zz-minus-closed)
;;;    simplify
;;;    (contrapose "with(m:zz,s:[zz,prop],not(lambda(n:zz,s(n+m-1))(1)))")
;;;    simplify
;;;    (contrapose "with(t_$0,m:zz,s:[zz,prop],
;;;  not(lambda(n:zz,s(n+m-1))(t_$0+1)))")
;;;    (incorporate-antecedent "with(t_$0,m:zz,s:[zz,prop],lambda(n:zz,s(n+m-1))(t_$0))")
;;;    beta-reduce-with-minor-premises
;;;    (instantiate-universal-antecedent "with(s:[zz,prop],m:zz,
;;;  forall(t:zz,m<=t implies (s(t) implies s(t+1))))" ("t_$0+m-1"))
;;;    (contrapose "with(t_$0,m:zz,not(m<=t_$0+m-1))")
;;;    simplify
;;;    direct-inference
;;;    direct-and-antecedent-inference-strategy
;;;    (incorporate-antecedent "with(m,t_$0:zz,s:[zz,prop],s(t_$0+m-1+1))")
;;;    simplify
;;;    (apply-macete-with-minor-premises zz-+-closed)
;;;    (apply-macete-with-minor-premises zz-+-closed)
;;;    (apply-macete-with-minor-premises zz-+-closed)




(def-inductor pre-rr-integer-inductor
  general-induction
  (theory ordered-field))

(def-recursive-constant ^ 
 "lambda(exp:[rr,zz,rr],lambda(r:rr,n:zz,
          if(n<0,1/exp(r,-n) ,1+1<=n,exp(r,n-1)*r,1=n, r, not(r=0),1,?rr)))"
 (theory ordered-field))


(def-theorem division-in-terms-of-exponential
  "forall(y,x:rr,x/y==x*y^(-1))"
  (theory ordered-field)
  (proof

   (
    (unfold-single-defined-constant (0) ^)
    simplify
    (unfold-single-defined-constant (0) ^)
    simplify
    insistent-direct-inference-strategy
    (case-split ("y=0"))
    (antecedent-inference "with(y,x:rr,#(x/y) or #(1/y*x))")
    (contrapose "with(y,x:rr,#(x/y))")
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    (contrapose "with(x,y:rr,#(1/y*x))")
    simplify
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    (cut-with-single-formula "y*(x/y)=y*((1/y)*x)")
    (contrapose "with(x,y:rr,y*(x/y)=y*(1/y*x))")
    (apply-macete-with-minor-premises times-left-cancellation)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (force-substitution "y*(1/y*x)" "(y*1/y)*x" (0))
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    (apply-macete-with-minor-premises associative-law-for-multiplication-pre-reals)

    )))


(def-theorem ()
  "forall(y,x:rr,x/y==x*y^[-1])"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises negative-one-characterization)
    (apply-macete-with-minor-premises division-in-terms-of-exponential)

    )))

(def-theorem exponential-of-0-lemma-1
  "forall(m:zz,1<=m implies 0^m=0)"
  (theory ordered-field)
  (proof
   (
    (induction pre-rr-integer-inductor ("m"))
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) ^)
    simplify

    )))

(def-theorem exponential-of-0-lemma-2
  "forall(m:zz,m<=0 implies not(#(0^m)))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "m<0 or m=0")
    (antecedent-inference "with(m:zz,m<0 or m=0)")
    (weaken (1))
    (unfold-single-defined-constant (0) ^)
    simplify
    (apply-macete-with-minor-premises exponential-of-0-lemma-1)
    simplify
    (force-substitution "(-1)*m" "-m" (0))
    simplify
    (unfold-single-defined-constant (0) ^)
    simplify
    simplify

    )
   ))

(def-theorem exponential-of-0
  "forall(m:zz, #(0^m,rr) implies 0^m=0)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("m<=0"))
    (contrapose "with(m:zz,#(0^m,rr))")
    (cut-with-single-formula "not(#(0^m))")
    (apply-macete-with-minor-premises exponential-of-0-lemma-2)
    (apply-macete-with-minor-premises exponential-of-0-lemma-1)
    )))

(def-theorem exponential-of-0-corollary
  "forall(m:zz, #(0^m) implies 0^m=0)"
  (theory ordered-field)
  (proof
   (
    (assume-theorem exponential-of-0)
    direct-and-antecedent-inference-strategy
    (backchain "forall(m:zz,#(0^m,rr) implies 0^m=0)")
    )))

(def-theorem exponential-of-1-lemma-0
  "forall(n:zz,0<=n implies 1^n=1)"
  (theory ordered-field)
  (proof
   (
    (induction pre-rr-integer-inductor ("n"))
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) ^)
    simplify

    )))

(def-theorem exponential-of-1-lemma
  "forall(n:zz,1^n=1)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("0<=n"))
    (apply-macete-with-minor-premises exponential-of-1-lemma-0)
    (unfold-single-defined-constant (0) ^)
    simplify
    (force-substitution "1^((-1)*n)" "1" (0))
    (cut-with-single-formula "1*(1/1)=1*1")
    simplify
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    (apply-macete-with-minor-premises exponential-of-1-lemma-0)
    (force-substitution "(-1)*n" "-n" (0))
    simplify

    )
   ))

(def-theorem exponential-of-1-corollary
  "forall(n:zz, #(1^n,rr) implies 1^n=1)"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises exponential-of-1-lemma)
    )))

(def-theorem zero-exponent
  "forall(x:rr,#(x^0,rr) implies x^0=1)"
  (theory ordered-field)
  (proof
   (
    (unfold-single-defined-constant (0 1) ^)
    simplify
    )))

(def-theorem zero-exponent-corollary
  "forall(x:rr,#(x^0) implies x^0=1)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises zero-exponent)

    )))

(def-theorem one-exponent
  "forall(x:rr,x^1=x)"
  (theory ordered-field)
  (proof
   (
    (unfold-single-defined-constant (0) ^)
    simplify
    )))


(def-theorem exponent-defined-lemma-0
  "forall(n:zz,x:rr, 1<=n implies #(x^n))"
  (theory ordered-field)
  (proof
   (
    (induction pre-rr-integer-inductor ("n"))
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) ^)
    simplify
    )))

(def-theorem exponent-non-zero-lemma-0
  "forall(n:zz,x:rr, 1<=n and not(x=0) implies not(x^n = 0))"
  (theory ordered-field)
  (proof
   (
    (induction pre-rr-integer-inductor ("n"))
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) ^)
    simplify
    (apply-macete-with-minor-premises cancel-pre-reals)
    (contrapose "with(x:rr,not(x=0))")
    (antecedent-inference "with(t:zz,x:rr,x^t=0 or x=0)")
    (apply-macete-with-minor-premises exponent-defined-lemma-0)

    )))



(def-theorem exponent-defined-lemma-1
  "forall(n:zz,x:rr, not(x=0) implies #(x^n))"
  (theory ordered-field)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (case-split ("1<=n"))
    (apply-macete-with-minor-premises exponent-defined-lemma-0)
    (unfold-single-defined-constant (0) ^)
    (case-split ("n<0"))
    simplify
    definedness
    (apply-macete-with-minor-premises exponent-non-zero-lemma-0)
    simplify
    (force-substitution "(-1)*n" "-n" (0))
    simplify
    (apply-macete-with-minor-premises exponent-defined-lemma-0)
    simplify

    )))

(def-theorem exponent-domain
  "forall(n:zz,x:rr, #(x^n) iff (not(x=0) or 1<=n))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(n:zz,x:rr,#(x^n))")
    (backchain "with(x:rr,x=0)")
    (apply-macete-with-minor-premises exponential-of-0-lemma-2)
    simplify
    (apply-macete-with-minor-premises exponent-defined-lemma-1)
    (apply-macete-with-minor-premises exponent-defined-lemma-0)
    )))


(def-theorem ()
  "forall(x:rr,y:zz,(0<y or not(x=0)) implies #(x^y))" 
  (theory ordered-field)
  (usages d-r-convergence)
  (proof

   (
    (apply-macete-with-minor-premises exponent-domain)
    direct-and-antecedent-inference-strategy
    simplify

    )))

(def-theorem () 
  "forall(x,y:ind,#(y,zz) and x=0 and not(0<y) implies not(#(x^y)))"
  (theory ordered-field)
  (usages d-r-convergence)
  (proof
   (
    (apply-macete-with-minor-premises exponent-domain)
    direct-and-antecedent-inference-strategy
    simplify
    )))

(def-theorem exponent-non-zero-lemma-1
  "forall(n:zz,x:rr, not(x=0) implies not(x^n = 0))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("1<=n"))
    (apply-macete-with-minor-premises exponent-non-zero-lemma-0)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) ^)
    simplify
    (case-split ("n=0"))
    simplify
    simplify
    (cut-with-single-formula "not(x^((-1)*n)*(1/x^((-1)*n))=x^((-1)*n)*0)")
    (contrapose "with(n:zz,x:rr,not(x^((-1)*n)*(1/x^((-1)*n))=x^((-1)*n)*0))")
    simplify
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    (apply-macete-with-minor-premises exponent-non-zero-lemma-0)
    direct-and-antecedent-inference-strategy
    simplify
    (force-substitution "(-1)*n" "-n" (0))
    simplify
    simplify
    simplify
    )))

(def-theorem sum-of-exponents-law-lemma-0
  "forall(n,m:zz, x:rr,1<=m and 1<=n implies x^(m+n)=x^m*x^n)"
  (theory ordered-field)
  (proof
   (
    (induction pre-rr-integer-inductor ())
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises one-exponent)
    (unfold-single-defined-constant (0) ^)
    simplify
    (apply-macete-with-minor-premises exponent-defined-lemma-0)
    (unfold-single-defined-constant (0) ^)
    simplify
    )))

(def-theorem negative-exponent-law
  "forall(x:rr,n:zz, not(x=0) implies x^(-n) = 1/(x^n))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("0<n"))
    (unfold-single-defined-constant (0) ^)
    simplify
    definedness
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (case-split ("n=0"))
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    (cut-with-single-formula "1*1=1*(1/1)")
    simplify
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    (unfold-single-defined-constant (1) ^)
    simplify
    (apply-macete-with-minor-premises inverse-of-inverse)
    simplify
    (apply-macete-with-minor-premises exponent-domain)
    simplify
    (force-substitution "(-1)*n" "-n" (0))
    simplify
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)

    )))


(def-theorem sum-of-exponents-law-lemma-1
  "forall(n,m:zz,x:rr,
      not(x=0) and 1<=n and 1<=m implies x^(m+-n)=x^m*x^(-n))"
  (theory ordered-field)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (case-split ("n<m"))
    (cut-with-single-formula "x^(m+-n)*x^n=x^m*x^(-n)*x^n")
    (contrapose "with(n,m:zz,x:rr,x^(m+-n)*x^n=x^m*x^(-n)*x^n)")
    (apply-macete-with-minor-premises times-right-cancellation)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-0)
    direct-and-antecedent-inference-strategy
    (force-substitution "(-1)*n" "-n" (0))
    simplify
    (force-substitution "x^(m+-n)*x^n" "x^((m+-n+n))" (0))
    (apply-macete-with-minor-premises associative-law-for-multiplication-pre-reals)
    (force-substitution "x^(-n)*x^n" "1" (0))
    simplify
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-locally-with-minor-premises sum-of-exponents-law-lemma-0 (0) " x^(m+-n+n) ")
    (case-split ("n=m"))
    (apply-macete-with-minor-premises negative-exponent-law)
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (cut-with-single-formula "m<n")
    (weaken (1 2))
    (force-substitution "m+-n" "-(n+-m)" (0))
    (apply-macete-with-minor-premises negative-exponent-law)
    (cut-with-single-formula "forall(m,n:zz,x:rr, n<m and 1<=m and 1<=n and not(x=0) implies x^(m+-n)=x^m*x^(-n))")
    (backchain "forall(m,n:zz,x:rr,
  n<m and 1<=m and 1<=n and not(x=0)
   implies 
  x^(m+-n)=x^m*x^(-n))")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises inverse-of-product)
    (apply-macete-locally-with-minor-premises commutative-law-for-multiplication-pre-reals (0) " x^m*(1/x^n) ")
    (apply-macete-with-minor-premises times-left-cancellation)
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises inverse-of-inverse)
    simplify
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises division-non-zero)
    definedness
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (force-substitution "(-1)*m" "-m" (0))
    simplify
    (weaken (0 1 2 3))
    direct-and-antecedent-inference-strategy
    simplify
    simplify

;;;    modified failed proof.

;;;    direct-and-antecedent-inference-strategy
;;;    (case-split ("n<m"))
;;;    (cut-with-single-formula "x^(m+-n)*x^n=x^m*x^(-n)*x^n")
;;;    (contrapose "with(n,m:zz,x:rr,x^(m+-n)*x^n=x^m*x^(-n)*x^n)")
;;;    (apply-macete-with-minor-premises times-right-cancellation)
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-0)
;;;    direct-and-antecedent-inference-strategy
;;;    (force-substitution "x^(m+-n)*x^n" "x^((m+-n+n))" (0))
;;;    (apply-macete-with-minor-premises associative-law-for-multiplication-pre-reals)
;;;    (force-substitution "x^(-n)*x^n" "1" (0))
;;;    simplify
;;;    (apply-macete-with-minor-premises negative-exponent-law)
;;;    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
;;;    (apply-macete-with-minor-premises division-characterization-pre-reals)
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (apply-macete-locally-with-minor-premises sum-of-exponents-law-lemma-0 (0) " x^(m+-n+n) ")
;;;    (case-split ("n=m"))
;;;    simplify
;;;    (apply-macete-with-minor-premises zero-exponent)
;;;    (force-substitution "(-1)*m" "-m" (0))
;;;    (apply-macete-with-minor-premises negative-exponent-law)
;;;    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
;;;    (apply-macete-with-minor-premises division-characterization-pre-reals)
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (cut-with-single-formula "m<n")
;;;    (weaken (1 2))
;;;    (force-substitution "m+-n" "-(n+-m)" (0))
;;;    (apply-macete-with-minor-premises negative-exponent-law)
;;;    (cut-with-single-formula "forall(m,n:zz,x:rr, n<m and 1<=m and 1<=n and not(x=0) implies x^(m+-n)=x^m*x^(-n))")
;;;    (backchain "forall(m,n:zz,x:rr,
;;;  n<m and 1<=m and 1<=n and not(x=0)
;;;   implies 
;;;  x^(m+-n)=x^m*x^(-n))")
;;;    direct-and-antecedent-inference-strategy
;;;    (apply-macete-with-minor-premises inverse-of-product)
;;;    (apply-macete-locally-with-minor-premises commutative-law-for-multiplication-pre-reals (0) " x^m*(1/x^n) ")
;;;    (apply-macete-with-minor-premises times-left-cancellation)
;;;    (apply-macete-with-minor-premises negative-exponent-law)
;;;    (apply-macete-with-minor-premises inverse-of-inverse)
;;;    simplify
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (apply-macete-with-minor-premises division-non-zero)
;;;    definedness
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (weaken (0 1 2 3))
;;;    direct-and-antecedent-inference-strategy
;;;    simplify
;;;    simplify
;;;    
    
    ;;  failed proof BEFORE modification.    
;;;    direct-and-antecedent-inference-strategy
;;;    (case-split ("n<m"))
;;;    (cut-with-single-formula "x^(m+-n)*x^n=x^m*x^(-n)*x^n")
;;;    (contrapose "with(n,m:zz,x:rr,x^(m+-n)*x^n=x^m*x^(-n)*x^n)")
;;;    (apply-macete-with-minor-premises times-right-cancellation)
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-0)
;;;    direct-and-antecedent-inference-strategy
;;;    (force-substitution "(-1)*n" "-n" (0))
;;;    simplify
;;;    (force-substitution "x^(m+-n)*x^n" "x^((m+-n+n))" (0))
;;;    (apply-macete-with-minor-premises associative-law-for-multiplication-pre-reals)
;;;    (force-substitution "x^(-n)*x^n" "1" (0))
;;;    simplify
;;;    (apply-macete-with-minor-premises negative-exponent-law)
;;;    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
;;;    (apply-macete-with-minor-premises division-characterization-pre-reals)
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (apply-macete-locally-with-minor-premises sum-of-exponents-law-lemma-0 (0) " x^(m+-n+n) ")
;;;    (case-split ("n=m"))
;;;    simplify
;;;    (apply-macete-with-minor-premises zero-exponent)
;;;    (force-substitution "(-1)*n" "-n" (0))
;;;    (apply-macete-with-minor-premises negative-exponent-law)
;;;    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
;;;    (apply-macete-with-minor-premises division-characterization-pre-reals)
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (cut-with-single-formula "m<n")
;;;    (weaken (1 2))
;;;    (force-substitution "m+-n" "-(n+-m)" (0))
;;;    (apply-macete-with-minor-premises negative-exponent-law)
;;;    (cut-with-single-formula
;;;     "forall(m,n:zz,x:rr, n<m and 1<=m and 1<=n and not(x=0) implies x^(m+-n)=x^m*x^(-n))")
;;;    (backchain "forall(m,n:zz,x:rr,
;;;  n<m and 1<=m and 1<=n and not(x=0)
;;;   implies 
;;;  x^(m+-n)=x^m*x^(-n))")
;;;    direct-and-antecedent-inference-strategy
;;;    (apply-macete-with-minor-premises inverse-of-product)
;;;    (apply-macete-locally-with-minor-premises
;;;     commutative-law-for-multiplication-pre-reals (0) " x^m*(1/x^n) ")
;;;    (apply-macete-with-minor-premises times-left-cancellation)
;;;    (apply-macete-with-minor-premises negative-exponent-law)
;;;    (apply-macete-with-minor-premises inverse-of-inverse)
;;;    simplify
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (apply-macete-with-minor-premises division-non-zero)
;;;    definedness
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
;;;    (force-substitution "(-1)*m" "-m" (0))
;;;    simplify
;;;    (weaken (0 1 2 3))
;;;    direct-and-antecedent-inference-strategy
;;;    simplify
;;;    simplify

    )))


(def-theorem sum-of-exponents-law-pre-reals
  "forall(n,m:zz,x:rr,not(x=0) implies x^(m+n)=x^m*x^n)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("1<=n" "1<=m"))
    (apply-macete-with-minor-premises sum-of-exponents-law-lemma-0)
    simplify
    (case-split ("m=0"))
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    simplify
    (force-substitution "m" "-(-m)" (0 1))
    (apply-macete-with-minor-premises commutative-law-for-addition-pre-reals)
    (apply-macete-with-minor-premises sum-of-exponents-law-lemma-1)
    simplify
    simplify
    (case-split ("n=0"))
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    simplify
    (force-substitution "n" "-(-n)" (0 1))
    (apply-macete-with-minor-premises sum-of-exponents-law-lemma-1)
    simplify
    simplify
    (case-split ("m=0"))
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    simplify
    (case-split ("n=0"))
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    simplify
    (force-substitution "m+n" "-((-m)+(-n))" (0))
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises sum-of-exponents-law-lemma-0)
    (apply-macete-with-minor-premises inverse-of-product)
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises inverse-of-inverse)
    simplify
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    simplify

    )))

(def-theorem sum-of-exponents-first-corollary
  "forall(n,m:zz, x:rr,#(x^m*x^n,rr) implies x^(m+n)=x^m*x^n)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("x=0"))
    (cut-with-single-formula "#(x^m) and #(x^n)")
    (contrapose "with(n,m:zz,x:rr,#(x^m) and #(x^n))")
    (apply-macete-with-minor-premises exponent-domain)
    (contrapose "with(x:rr,x=0)")
    (antecedent-inference "with(n,m:zz,x:rr,(not(x=0) or 1<=m) and (not(x=0) or 1<=n))")
    (antecedent-inference "with(n:zz,x:rr,not(x=0) or 1<=n)")
    (antecedent-inference "with(m:zz,x:rr,not(x=0) or 1<=m)")
    (contrapose "with(n,m:zz,x:rr,not(x^(m+n)=x^m*x^n))")
    (apply-macete-with-minor-premises sum-of-exponents-law-lemma-0)
    simplify
    (apply-macete-with-minor-premises sum-of-exponents-law-pre-reals)

    )))

(def-theorem sum-of-exponents-second-corollary
  "forall(n,m:zz, x:rr,#(x^m*x^n) implies x^(m+n)=x^m*x^n)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises sum-of-exponents-first-corollary)

    )))

(def-theorem iterated-exponentiation-definability
  "forall(n,m:zz, x:rr ,((#(x^m,rr) and #(x^n,rr)) iff #((x^m)^n,rr)))"
  reverse
  (theory ordered-field)
  (proof
   (
    direct-inference
    (cut-with-single-formula "(#(x^m) and #(x^n)) iff #((x^m)^n)")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises exponent-domain)
    direct-and-antecedent-inference-strategy
    (contrapose "with(m:zz,x:rr,x^m=0)")
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (contrapose "with(n:zz,x:rr,#(x^n))")
    (apply-macete-with-minor-premises exponent-domain)
    direct-and-antecedent-inference-strategy
    (contrapose "with(x:rr,x=0)")
    (antecedent-inference "with(n:zz,x:rr,not(x=0) or 1<=n)")
    (apply-macete-with-minor-premises exponent-domain)
    direct-inference
    (contrapose "with(m:zz,x:rr,#(x^m))")
    (apply-macete-with-minor-premises exponent-domain)
    (contrapose "with(n:zz,not(1<=n))")
    (antecedent-inference "with(m:zz,x:rr,not(x=0) or 1<=m)")
    (contrapose "with(n,m:zz,x:rr,#((x^m)^n))")
    (apply-macete-with-minor-premises exponent-domain)
    (contrapose "with(n:zz,not(1<=n))")
    (antecedent-inference "with(n,m:zz,x:rr,not(x^m=0) or 1<=n)")
    (contrapose "with(m:zz,x:rr,not(x^m=0))")
    (unfold-single-defined-constant (0) ^)
    simplify

    )))

(def-theorem iterated-exponentiation-definability-corollary
  "forall(n,m:zz, x:rr ,((#(x^m) and #(x^n)) iff #((x^m)^n)))"
  (theory ordered-field)
  (proof
   (
    (force-substitution "#((x^m)^n)" "#((x^m)^n,rr)" (0))
    (apply-macete-with-minor-premises rev%iterated-exponentiation-definability)
    )))


(def-theorem zz-*-closed
  "forall(x,y:zz,#(x*y,zz))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("0<=y"))
    (induction pre-rr-integer-inductor ())
    beta-reduce-repeatedly
    simplify
    (force-substitution "x*y" "-(x*(-y))" (0))
    (cut-with-single-formula "#(x*(-y),zz)")
    (apply-macete-with-minor-premises zz-minus-closed)
    (cut-with-single-formula "forall(y:zz,0<=y implies #(x*y,zz))")
    (backchain "with(x:zz,forall(y:zz,0<=y implies #(x*y,zz)))")
    simplify
    simplify

    ))
  (usages d-r-convergence))


(def-theorem exponent-distributes-over-product-lemma-0
  "forall(m:zz ,y,x:rr,1<=m implies x^m*y^m=(x*y)^m)"
  (theory ordered-field)
  (proof
   (
    (induction pre-rr-integer-inductor ("m"))
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises one-exponent)
    )))

(def-theorem exponent-distributes-over-product-lemma-1
  "forall(m:zz ,y,x:rr,not(x=0) and not(y=0) implies x^m*y^m=(x*y)^m)"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("1<=m"))
    (apply-macete-with-minor-premises exponent-distributes-over-product-lemma-0)
    simplify
    (case-split ("m=0"))
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    simplify
    (apply-macete-with-minor-premises exponent-domain)
    (apply-macete-with-minor-premises cancel-pre-reals)
    direct-inference
    (antecedent-inference "with(p,q:prop, p or q)")
    (force-substitution "m" "-(-m)" (2))
    (apply-macete-with-minor-premises negative-exponent-law)
    (force-substitution "(x*y)^(-m)" "x^(-m)*y^(-m)" (0))
    (apply-macete-with-minor-premises inverse-of-product)
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises inverse-of-inverse)
    simplify
    (weaken (0 1 3))
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (weaken (0 1 2))
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (weaken (0 1 3))
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (weaken (0 1 2))
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-distributes-over-product-lemma-0)
    (weaken (0 1))
    (apply-macete-with-minor-premises cancel-pre-reals)
    (contrapose "with(x:rr,not(x=0))")
    (antecedent-inference "with(x,y:rr,y=0 or x=0)")
    (weaken (0 1 2 3))
    simplify

    )))


(def-theorem exponent-distributes-over-product
  "forall(m:zz,y,x:rr,
     (#(x^m*y^m,rr) or #((x*y)^m,rr)) implies x^m*y^m=(x*y)^m)"
  (theory ordered-field)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(x^m) and #(y^m)")
    (weaken (1))
    (contrapose "with(y:rr,m:zz,x:rr,#(x^m) and #(y^m))")
    (apply-macete-with-minor-premises exponent-domain)
    (contrapose "with(y:rr,m:zz,x:rr,not(x^m*y^m=(x*y)^m))")
    (antecedent-inference "with(y:rr,m:zz,x:rr,
  (not(x=0) or 1<=m) and (not(y=0) or 1<=m))")
    (antecedent-inference "with(m:zz,y:rr,not(y=0) or 1<=m)")
    (antecedent-inference "with(m:zz,x:rr,not(x=0) or 1<=m)")
    (apply-macete-with-minor-premises exponent-distributes-over-product-lemma-1)
    simplify
    (apply-macete-with-minor-premises exponent-domain)
    (apply-macete-with-minor-premises cancel-pre-reals)
    direct-inference
    (antecedent-inference "with(x,y:rr,y=0 or x=0)")
    (apply-macete-with-minor-premises exponent-distributes-over-product-lemma-0)
    simplify
    (apply-macete-with-minor-premises exponent-distributes-over-product-lemma-0)
    simplify
    simplify
    (cut-with-single-formula "#(x^m) and #(y^m)")
    (weaken (1))
    (apply-macete-with-minor-premises exponent-domain)
    (cut-with-single-formula "#((x*y)^m)")
    (weaken (1))
    (contrapose "with(m:zz,y,x:rr,#((x*y)^m))")
    (apply-macete-with-minor-premises exponent-domain)
    (apply-macete-with-minor-premises cancel-pre-reals)
    (contrapose "with(y:rr,m:zz,x:rr,x=0 and not(1<=m) or y=0 and not(1<=m))")
    (antecedent-inference "with(m:zz,x,y:rr,not(y=0) and not(x=0) or 1<=m)")
    direct-and-antecedent-inference-strategy
    direct-and-antecedent-inference-strategy

    )))


(def-theorem exponent-distributes-over-product-corollary
  "forall(m:zz,y,x:rr, x^m*y^m==(x*y)^m)"
  (theory ordered-field)
  (proof
   (
    insistent-direct-inference-strategy
    (cut-with-single-formula "#(x^m*y^m,rr) or #((x*y)^m,rr)")
    (assume-theorem exponent-distributes-over-product)
    (backchain "with(p:prop, forall(m:zz,y,x:rr,p))")
    )))

(def-theorem iterated-exponentiation-value-lemma-0
  "forall(x:rr,m,n:zz,1<=n and 1<=m implies (x^m)^n=x^(m*n))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("x=0"))
    simplify
    (apply-macete-with-minor-premises exponential-of-0)
    (apply-macete-with-minor-premises exponential-of-0)
    (induction pre-rr-integer-inductor ("n"))
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises one-exponent)
    simplify
    (apply-macete-with-minor-premises sum-of-exponents-law-pre-reals)
    simplify

    )))


(def-theorem iterated-exponentiation-value-lemma-1
  "forall(x:rr,m,n:zz,not(x=0) and 1<=m implies (x^m)^n=x^(m*n))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("1<=n"))
    (apply-macete-with-minor-premises iterated-exponentiation-value-lemma-0)
    simplify
    (case-split ("n=0"))
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    (apply-macete-with-minor-premises exponent-domain)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    direct-and-antecedent-inference-strategy
    (force-substitution "n" "-(-n)" (0))
    (force-substitution "m*n" "-(m*(-n))" (0))
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises iterated-exponentiation-value-lemma-0)
    simplify
    definedness
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    simplify
    simplify

    )))


(def-theorem exponent-of-inverse-lemma
  "forall(x:rr, m:zz, 1<=m and not(x=0) implies (1/x)^m = 1/(x^m))"
  (theory ordered-field)
  (proof
   (
    (induction pre-rr-integer-inductor ("m"))
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises one-exponent)
    simplify
    (apply-macete-with-minor-premises inverse-of-product)
    simplify
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)

    )))

(def-theorem exponent-of-inverse
  "forall(x:rr, m:zz, not(x=0) implies (1/x)^m = 1/(x^m))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("1<=m"))
    (apply-macete-with-minor-premises exponent-of-inverse-lemma)
    simplify
    definedness
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (case-split ("m=0"))
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    (cut-with-single-formula "1*1=1*(1/1)")
    simplify
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    (apply-macete-with-minor-premises exponent-domain)
    (apply-macete-with-minor-premises division-non-zero)
    (force-substitution "m" "-(-m)" (0))
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises exponent-of-inverse-lemma)
    (apply-macete-with-minor-premises inverse-of-inverse)
    (apply-macete-with-minor-premises negative-exponent-law)
    simplify
    definedness
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises division-non-zero)
    simplify

    )))

(def-theorem exponent-of-inverse-corollary
  "forall(x:rr, m:zz, (1/x)^m == 1/(x^m))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("x=0"))
    (cut-with-single-formula "not(#(1/x)) and not#(1/x^m)")
    insistent-direct-inference
    (antecedent-inference "with(m:zz,x:rr,#((1/x)^m) or #(1/x^m))")
    (case-split ("#(x^m)"))
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(m:zz,x:rr,#(x^m))")
    (apply-macete-with-minor-premises exponent-domain)
    simplify
    (apply-macete-with-minor-premises exponential-of-0)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    (incorporate-antecedent "with(m:zz,x:rr,not(#(x^m)))")
    simplify
    (assume-theorem exponent-of-inverse)
    (backchain "forall(x:rr,m:zz,not(x=0) implies (1/x)^m=1/x^m)")

    )))

(def-theorem iterated-exponentiation-value-lemma-2
  "forall(x:rr,m,n:zz,not(x=0) implies (x^m)^n=x^(m*n))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("1<=m"))
    (apply-macete-with-minor-premises iterated-exponentiation-value-lemma-1)
    simplify
    (case-split ("m=0"))
    simplify
    (apply-macete-with-minor-premises zero-exponent)
    (apply-macete-with-minor-premises exponential-of-1-lemma)
    (force-substitution "m" "-(-m)" (0))
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises exponent-of-inverse)
    (apply-macete-with-minor-premises iterated-exponentiation-value-lemma-1)
    (force-substitution "(-m)*n" "-(m*n)" (0))
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises inverse-of-inverse)
    simplify
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    simplify
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    simplify
    )))

(def-theorem iterated-exponentiation-value
  "forall(n,m:zz,x:rr,#((x^m)^n,rr) implies (x^m)^n=x^(m*n))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#((x^m)^n)")
    (weaken (1))
    (case-split ("x=0"))
    (incorporate-antecedent "with(n,m:zz,x:rr,#((x^m)^n))")
    simplify
    (case-split ("1<=m"))
    (apply-macete exponential-of-0)
    (apply-macete-with-minor-premises exponent-domain)
    simplify
    (apply-macete-with-minor-premises exponential-of-0)
    (cut-with-single-formula "not(#(0^m))")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises exponent-domain)
    (apply-macete-with-minor-premises iterated-exponentiation-value-lemma-2)
    simplify

    )))

(def-theorem iterated-exponentiation-value-corollary
  "forall(n,m:zz,x:rr,#((x^m)^n) implies (x^m)^n=x^(m*n))"
  (theory ordered-field)
  (proof
   (
    (assume-theorem iterated-exponentiation-value)
    direct-and-antecedent-inference-strategy
    (backchain "forall(n,m:zz,x:rr,#((x^m)^n,rr) implies (x^m)^n=x^(m*n))")

    )))

(def-theorem ()
  "forall(x:qq,forsome(a,b:zz,x=a/b))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(y:rr, y=x and #(x,qq))")
    (antecedent-inference "with(x:qq,forsome(y:rr,y=x and #(x,qq)))")
    (antecedent-inference "with(x:qq,y:rr,y=x and #(x,qq))")
    (incorporate-antecedent "with(x:qq,#(x,qq))")
    (apply-macete-with-minor-premises zz-quotient-field-pre-reals)
    (instantiate-existential ("x")))))


(def-theorem ()
  "forall(x,y:zz,#(x-y,zz))"
  
  (theory ordered-field)
  (proof
   (
    (unfold-single-defined-constant (0) sub)
    (apply-macete-with-minor-premises zz-+-closed)

    )))




(def-theorem integer-exponent-lemma
  "forall(x,y:zz,1<=y implies #(x^y,zz))"
  (theory ordered-field)
  (proof
   (
    (induction pre-rr-integer-inductor ())
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises one-exponent)

    )))



(def-theorem integer-exponent
  "forall(x,y:ind,
       #(x,zz) and #(y,zz) and (0<y or not(x=0))
          implies 
       #(x^y,qq))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(x^y,zz)")
    (apply-macete-with-minor-premises integer-exponent-lemma)
    simplify
    (case-split ("1<=y"))
    (cut-with-single-formula "#(x^y,zz)")
    (apply-macete-with-minor-premises integer-exponent-lemma)
    (case-split ("y=0"))
    (backchain "with(y:ind,y=0)")
    (apply-macete-with-minor-premises zero-exponent)
    (force-substitution "y" "-(-y)" (0))
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises zz-quotient-field-pre-reals)
    (instantiate-existential ("1" "x^(-y)"))
    (apply-macete-with-minor-premises negative-exponent-law)
    (apply-macete-with-minor-premises inverse-of-inverse)
    simplify
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises integer-exponent-lemma)
    simplify
    definedness
    simplify

    )))


(def-theorem sum-of-fractions-lemma
  "forall(a,b,c,d:rr, a/b+c/d==(a*d+c*b)/(b*d))"
  (theory ordered-field)
  (proof
   (
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (antecedent-inference "with(d,c,b,a:rr,#(a/b+c/d) or #((a*d+c*b)/(b*d)))")
    (cut-with-single-formula "#(a/b) and #(c/d)")
    (antecedent-inference "with(d,c,b,a:rr,#(a/b) and #(c/d))")
    (contrapose "with(d,c:rr,#(c/d))")
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    (contrapose "with(b,a:rr,#(a/b))")
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    (contrapose "with(d,c,b,a:rr,not(a/b+c/d=(a*d+c*b)/(b*d)))")
    (cut-with-single-formula "b*d*(a/b+c/d)=(b*d)*((a*d+c*b)/(b*d))")
    (contrapose "b*d*(a/b+c/d)=(b*d)*((a*d+c*b)/(b*d))")
    (apply-macete-with-minor-premises times-left-cancellation)
    (apply-macete-with-minor-premises cancel-pre-reals)
    (contrapose "with(b:rr,not(b=0))")
    (antecedent-inference "with(b,d:rr,d=0 or b=0)")
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (apply-macete-with-minor-premises left-distributive-law-pre-reals)
    (force-substitution "b*d*(a/b)" "d*(b*(a/b))" (0))
    (force-substitution "b*d*(c/d)" "b*(d*(c/d))" (0))
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    (apply-macete-with-minor-premises associative-law-for-multiplication-pre-reals)
    simplify
    (apply-macete-with-minor-premises cancel-pre-reals)
    (contrapose "with(b:rr,not(b=0))")
    (antecedent-inference "with(b,d:rr,d=0 or b=0)")
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not(b=0) and not(d=0)")
    (cut-with-single-formula "#(a/b+c/d)")
    (weaken (1 2))
    definedness
    (contrapose "with(b,c,d,a:rr,#((a*d+c*b)/(b*d)))")
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    (apply-macete-with-minor-premises cancel-pre-reals)
    direct-inference
    (backchain "with(d,b:rr,not(b=0) implies d=0)")

    )))


(def-theorem qq-+-closed
  "forall(x,y:ind,#(x,qq) and #(y,qq) implies #(x+y,qq))"
  (theory ordered-field)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises zz-quotient-field-pre-reals)
    (cut-with-single-formula "forsome(c,d:zz,x=c/d) and forsome(e,f:zz,y=e/f)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)") (antecedent-inference-strategy (0))
      (backchain "with(d,c:zz,x:ind,x=c/d);") (backchain "with(f,e:zz,y:ind,y=e/f);")
      (apply-macete-with-minor-premises sum-of-fractions-lemma)
      (instantiate-existential ("c*f+e*d" "d*f")) 
      simplify 
      definedness
      (apply-macete-with-minor-premises cancel-pre-reals)
      (cut-with-single-formula "not(d=0) and not( f=0)") 
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(contrapose "with(d,c:zz,x:ind,x=c/d);") (backchain "with(d:zz,d=0);") (weaken (0))
	(cut-with-single-formula "not(#(c/0))") simplify simplify
	)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(contrapose "with(f,e:zz,y:ind,y=e/f);") (backchain "with(f:zz,f=0);") (weaken (0))
	(cut-with-single-formula "not(#(e/0))") simplify simplify
	) )
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (cut-with-single-formula "forsome(x1:rr,x=x1) and forsome(y1:rr,y=y1)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference-strategy (0)) (incorporate-antecedent "with(y:ind,#(y,qq));")
	(incorporate-antecedent "with(x:ind,#(x,qq));") (backchain "with(x1:rr,x:ind,x=x1);")
	(backchain "with(x1:rr,x:ind,x=x1);") (backchain "with(y1:rr,y:ind,y=y1);")
	(backchain "with(y1:rr,y:ind,y=y1);")
	(apply-macete-with-minor-premises zz-quotient-field-pre-reals)
	direct-and-antecedent-inference-strategy
	)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	direct-and-antecedent-inference-strategy (instantiate-existential ("x"))
	(instantiate-existential ("y"))
	) )
    )))


(def-theorem product-of-fractions-lemma
  "forall(a,b,c,d:rr, (a/b)*(c/d)==(a*c)/(b*d))"

  (theory ordered-field)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (case-split ("b=0 "))
    (block 
      (script-comment "`case-split' at (1)") 
      simplify
      (cut-with-single-formula "not(#(a/0)) and not(#((a*c)/0))")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,p and p);") insistent-direct-inference-strategy
	(antecedent-inference "with(p:prop,p or p);")
	)
      (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
      )
    (block 
      (script-comment "`case-split' at (2)") 
      (case-split ("d=0"))
      (block 
	(script-comment "`case-split' at (1)") 
	simplify
	(cut-with-single-formula "not(#(c/0) ) and not(#((a*c)/0))")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  insistent-direct-inference-strategy (antecedent-inference "with(p:prop,p or p);")
	  )
	(apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
	)
      (block 
	(script-comment "`case-split' at (2)") insistent-direct-inference-strategy
	(weaken (0)) (cut-with-single-formula "b*d*(a/b*(c/d))=b*d*((a*c)/(b*d))")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)") 
	  (contrapose "with(r:rr,r=r);")
	  (apply-macete-with-minor-premises times-left-cancellation)
	  (apply-macete-with-minor-premises cancel-pre-reals) (contrapose "with(d:rr,not(d=0));")
	  (antecedent-inference "with(p:prop,p or p);")
	  )
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises division-characterization-pre-reals)
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (0)")
	    (force-substitution "b*d*(a/b*(c/d))" "(b*(a/b))*(d*(c/d))" (0))
	    (apply-macete-with-minor-premises division-characterization-pre-reals) simplify
	    )
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (1)")
	    (apply-macete-with-minor-premises cancel-pre-reals)
	    (contrapose "with(d:rr,not(d=0));") (antecedent-inference "with(p:prop,p or p);")
	    ) ) ) )

    )))

(def-theorem qq-*-closed
  "forall(x,y:ind,#(x,qq) and #(y,qq) implies #(x*y,qq))"
  (theory ordered-field)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises zz-quotient-field-pre-reals)
    (cut-with-single-formula "forsome(c,d:zz,x=c/d) and forsome(e,f:zz,y=e/f)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)") (antecedent-inference-strategy (0))
      (backchain "with(d,c:zz,x:ind,x=c/d);") (backchain "with(f,e:zz,y:ind,y=e/f);")
      (apply-macete-with-minor-premises product-of-fractions-lemma)
      (instantiate-existential ("c*e" "d*f")) simplify definedness
      (apply-macete-with-minor-premises cancel-pre-reals)
      (cut-with-single-formula "not(d=0) and not f=0") direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(contrapose "with(d,c:zz,x:ind,x=c/d);") simplify (cut-with-single-formula "not(#(c/0))")
	simplify (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
	)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(contrapose "with(f,e:zz,y:ind,y=e/f);") simplify (cut-with-single-formula "not(#(e/0))")
	simplify (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
	) )
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (cut-with-single-formula "forsome(x1:rr,x=x1) and forsome(y1:rr,y=y1)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference-strategy (0)) (incorporate-antecedent "with(y:ind,#(y,qq));")
	(incorporate-antecedent "with(x:ind,#(x,qq));") (backchain "with(x1:rr,x:ind,x=x1);")
	(backchain "with(x1:rr,x:ind,x=x1);") (backchain "with(y1:rr,y:ind,y=y1);")
	(backchain "with(y1:rr,y:ind,y=y1);")
	(apply-macete-with-minor-premises zz-quotient-field-pre-reals)
	direct-and-antecedent-inference-strategy
	)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	direct-and-antecedent-inference-strategy (instantiate-existential ("x"))
	(instantiate-existential ("y"))
	) )

    )))


(def-theorem subtraction-of-fractions-lemma
  "forall(a,b,c,d:rr, a/b-c/d==(a*d-c*b)/(b*d))"
  (theory ordered-field)
  (proof
   (
    (unfold-single-defined-constant (0 1) sub)
    simplify
    (apply-macete-with-minor-premises product-division-interchange)
    (apply-macete-with-minor-premises sum-of-fractions-lemma)
    simplify

    )))

(def-theorem qq-sub-closed
  "forall(x,y:ind,#(x,qq) and #(y,qq) implies #(x-y,qq))"
  (theory ordered-field)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises zz-quotient-field-pre-reals)
    (cut-with-single-formula "forsome(c,d:zz,x=c/d) and forsome(e,f:zz,y=e/f)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)") (antecedent-inference-strategy (0))
      (backchain "with(d,c:zz,x:ind,x=c/d);") (backchain "with(f,e:zz,y:ind,y=e/f);")
      (apply-macete-with-minor-premises subtraction-of-fractions-lemma)
      (instantiate-existential ("(c*f-e*d)" "d*f")) simplify definedness
      (apply-macete-with-minor-premises cancel-pre-reals)
      (cut-with-single-formula "not(d=0) and not( f=0)") direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(contrapose "with(d,c:zz,x:ind,x=c/d);") (backchain "with(d:zz,d=0);") (weaken (0))
	(cut-with-single-formula "not(#(c/0))") simplify simplify
	)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(contrapose "with(f,e:zz,y:ind,y=e/f);") (backchain "with(f:zz,f=0);") (weaken (0))
	(cut-with-single-formula "not(#(e/0))") simplify simplify
	) )
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (cut-with-single-formula "forsome(x1:rr,x=x1) and forsome(y1:rr,y=y1)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference-strategy (0)) (incorporate-antecedent "with(y:ind,#(y,qq));")
	(incorporate-antecedent "with(x:ind,#(x,qq));") (backchain "with(x1:rr,x:ind,x=x1);")
	(backchain "with(x1:rr,x:ind,x=x1);") (backchain "with(y1:rr,y:ind,y=y1);")
	(backchain "with(y1:rr,y:ind,y=y1);")
	(apply-macete-with-minor-premises zz-quotient-field-pre-reals)
	direct-and-antecedent-inference-strategy
	)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	direct-and-antecedent-inference-strategy (instantiate-existential ("x"))
	(instantiate-existential ("y"))
	) )

    )))

(def-theorem qq-minus-closed
  "forall(x:ind,#(x,qq) implies #(-x,qq))" 

  (theory ordered-field)
  (proof
   (
    (force-substitution "-x" "0-x" (0))
    (apply-macete-with-minor-premises qq-sub-closed)
    simplify

    )))

(def-theorem exponentiation-of-fractions-lemma
  "forall(a,b:rr, m:zz, (a/b)^m==a^m/b^m)"
  (theory ordered-field)
  (proof
   (
    (force-substitution "a^m/b^m" "a^m*(1/b)^m" (0))
    (apply-macete-with-minor-premises exponent-distributes-over-product-corollary)
    (apply-macete-with-minor-premises product-division-interchange)
    simplify
    (apply-macete-with-minor-premises exponent-of-inverse-corollary)
    (apply-macete-with-minor-premises product-division-interchange)
    simplify

    )))


(def-theorem qq-div-closed
  "forall(x,y:ind,#(x,qq) and #(y,qq) and not(y=0) implies #(x/y,qq))"
  (theory ordered-field)
  (proof
   (
    (force-substitution "x/y" "x*(1/y)" (0))
    (apply-macete-with-minor-premises qq-*-closed)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises zz-quotient-field-pre-reals)
    (cut-with-single-formula "forsome(c,d:zz, y=c/d)")
    (antecedent-inference "with(y:ind,forsome(c,d:zz,y=c/d))")
    (backchain "with(d,c:zz,y:ind,y=c/d)")
    (instantiate-existential ("d" "c"))
    (cut-with-single-formula "(c/d)*(1/(c/d))=(c/d)*(d/c)")
    (contrapose "with(d,c:zz,c/d*(1/(c/d))=c/d*(d/c))")
    (apply-macete-with-minor-premises times-left-cancellation)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (apply-macete-with-minor-premises product-division-interchange)
    (apply-macete-with-minor-premises commutative-law-for-multiplication-pre-reals)
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    (cut-with-single-formula "c*1=c*(c/c)")
    (contrapose "with(c:zz,c*1=c*(c/c))")
    (apply-macete-with-minor-premises times-left-cancellation)
    (contrapose "with(y:ind,not(y=0))")
    (backchain "with(d,c:zz,y:ind,y=c/d)")
    (force-substitution "c/d" "c*(1/d)" (0))
    simplify
    (contrapose "with(d,c:zz,y:ind,y=c/d)")
    (force-substitution "c/d" "c*(1/d)" (0))
    simplify
    (apply-macete-with-minor-premises product-division-interchange)
    simplify
    (apply-macete-with-minor-premises product-division-interchange)
    simplify
    (apply-macete-with-minor-premises division-characterization-pre-reals)
    simplify
    (contrapose "with(y:ind,not(y=0))")
    (backchain "with(d,c:zz,y:ind,y=c/d)")
    (force-substitution "c/d" "c*(1/d)" (0))
    simplify
    (contrapose "with(d,c:zz,y:ind,y=c/d)")
    (force-substitution "c/d" "c*(1/d)" (0))
    simplify
    (apply-macete-with-minor-premises product-division-interchange)
    simplify
    (apply-macete-with-minor-premises product-division-interchange)
    simplify
    (cut-with-single-formula "#(c/d)")
    (contrapose "with(d,c:zz,#(c/d))")
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    (cut-with-single-formula "forsome(y1:rr,y=y1)")
    (antecedent-inference "with(y:ind,forsome(y1:rr,y=y1))")
    (backchain "with(y1:rr,y:ind,y=y1)")
    (incorporate-antecedent "with(y:ind,#(y,qq))")
    (backchain "with(y1:rr,y:ind,y=y1)")
    (apply-macete-with-minor-premises zz-quotient-field-pre-reals)
    (instantiate-existential ("y"))
    (apply-macete-with-minor-premises product-division-interchange)
    simplify

    )))

(def-theorem qq-^-closed
  "forall(x,y:ind,#(x,qq) and #(y,zz) and (0<y or not(x=0)) implies #(x^y,qq))"
  (theory ordered-field)
  (proof
   (
    direct-inference
    direct-inference
    (antecedent-inference "with(y,x:ind,#(x,qq) and #(y,zz) and (0<y or not(x=0)))")
    (cut-with-single-formula "forsome(y1:zz,y=y1) and forsome(x1:qq,x=x1)")
    (antecedent-inference-strategy (0))
    (contrapose "with(x:ind,#(x,qq))")
    (backchain "with(x1:qq,x:ind,x=x1)")
    (apply-macete-with-minor-premises zz-quotient-field-pre-reals)
    (contrapose "with(y,x:ind,not(#(x^y,qq)))")
    (antecedent-inference "with(x1:qq,forsome(a,b:zz,x1=a/b))")
    (backchain "with(x1:qq,x:ind,x=x1)")
    (backchain "with(b,a:zz,x1:qq,x1=a/b)")
    (backchain "with(y1:zz,y:ind,y=y1)")
    (apply-macete-with-minor-premises exponentiation-of-fractions-lemma)
    (apply-macete-with-minor-premises qq-div-closed)
    (cut-with-single-formula "not(b=0) and (0<y or not(a=0))")
    (apply-macete-with-minor-premises integer-exponent)
    direct-and-antecedent-inference-strategy
    (antecedent-inference "with(a:zz,y:ind,b:zz,not(b=0) and (0<y or not(a=0)))")
    (antecedent-inference "with(a:zz,y:ind,0<y or not(a=0))")
    (contrapose "with(y1:zz,not(0<y1))")
    (backchain-backwards "with(y1:zz,y:ind,y=y1)")
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    (apply-macete-with-minor-premises exponent-non-zero-lemma-1)
    direct-inference
    (cut-with-single-formula "#(a/b)")
    (contrapose "with(b,a:zz,#(a/b))")
    (apply-macete-with-minor-premises div-by-zero-undefined-pre-reals)
    (antecedent-inference "with(x,y:ind,0<y or not(x=0))")
    direct-inference
    direct-and-antecedent-inference-strategy
    (contrapose "with(x:ind,not(x=0))")
    (backchain "with(x1:qq,x:ind,x=x1)")
    (backchain "with(b,a:zz,x1:qq,x1=a/b)")
    (force-substitution "a/b" "a*(1/b)" (0))
    simplify
    (apply-macete-with-minor-premises product-division-interchange)
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("y"))
    (instantiate-existential ("x"))

    )))

(def-theorem ()
  "forall(x,y:qq,#(x+y,qq))"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises qq-+-closed)
    )))


(def-theorem ()
  "forall(x,y:qq,#(x*y,qq))"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises qq-*-closed)
    )))


(def-theorem ()
  "forall(x,y:qq,#(x-y,qq))"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises qq-sub-closed)
    )))

(def-theorem ()
  "forall(x:qq,#(-x,qq))"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises qq-minus-closed)
    )))


(def-theorem ()
  "forall(x,y:ind,#(x,zz) and #(y,zz) implies #(x+y,zz))"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises zz-+-closed)
    )))


(def-theorem ()
  "forall(x,y:ind,#(x,zz) and #(y,zz) implies #(x*y,zz))"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises zz-*-closed)
    )))
  

(def-theorem ()
  "forall(x,y:ind,#(x,zz) and #(y,zz) implies #(x-y,zz))"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises zz-sub-closed)
    )))


(def-theorem ()
  "forall(x:ind,#(x,zz) implies #(-x,zz))"
  (theory ordered-field)
  (proof
   (
    (apply-macete-with-minor-premises zz-minus-closed)
    )))

(def-theory complete-ordered-field
  (component-theories ordered-field)
  (axioms
   ("forall(p:[rr,prop], nonvacuous_q{p} and forsome(alpha:rr, 
 forall(theta:rr,p(theta) implies theta<=alpha)) implies
forsome(gamma:rr,forall(theta:rr,p(theta) implies theta<=gamma) and forall(gamma_1:rr, 
 forall(theta:rr,p(theta) implies theta<=gamma_1) implies gamma<=gamma_1)))")))


(def-translation h-o-real-arithmetic-instantiation
  (source h-o-real-arithmetic)
  (target complete-ordered-field)
  (constant-pairs 
   (^ ^)
   (sub sub)
   (<= <=))
  (theory-interpretation-check using-simplification))
