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


(herald criteria-for-convergence)

(include-files
 (files (imps theories/metric-spaces/metric-space-supplements)
	(imps theories/partial-orders/convergence-and-order)))


(def-theorem convergence-test-for-complete-spaces
  "complete
    implies 
   forall(f:[zz,pp],
     forsome(s:[zz,rr],k:zz,
       summable%nonnegative(s)
        and 
       forall(j:zz,k<=j implies dist(f(j),f(j+1))<=s(j)))
      implies 
     #(lim(f)))"
  
  (proof


   (

    (unfold-single-defined-constant (0) complete)
    direct-and-antecedent-inference-strategy
    (backchain "forall(s:[zz,pp],cauchy(s) implies #(lim(s)));")
    (unfold-single-defined-constant (0) cauchy)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(p:zz, forall(j,j_1:zz, p<=j and j<=j_1 implies sum(j,j_1,s)<=eps))")
    (instantiate-existential ("max(k,p)"))
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("sum(max(k,p),q_$0-1,lambda(j:zz,dist(f(j),f(j+1))))"))
    (force-substitution "q_$0" "q_$0-1+1" (0))
    (apply-macete-with-minor-premises generalized-triangle-inequality)
    direct-and-antecedent-inference-strategy
    
    simplify
    (cut-with-single-formula "dist(f(j),f(j+1))<=s(j)")
    (backchain "with(s:[zz,rr],f:[zz,pp],k:zz,
  forall(j:zz,k<=j implies dist(f(j),f(j+1))<=s(j)));")
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("max(k,p)"))
    (apply-macete-with-minor-premises maximum-1st-arg)
    simplify
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("sum(max(k,p),q_$0-1,s)"))
    (apply-macete-with-minor-premises monotonicity-for-sum)
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    (backchain "with(s:[zz,rr],f:[zz,pp],k:zz,
  forall(j:zz,k<=j implies dist(f(j),f(j+1))<=s(j)));")
    (cut-with-single-formula "k<=max(k,p)")
    simplify
    (apply-macete-with-minor-premises maximum-1st-arg)
    (backchain "with(eps:rr,s:[zz,rr],p:zz,
  forall(j,j_1:zz,
    p<=j and j<=j_1 implies sum(j,j_1,s)<=eps));")
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (cut-with-single-formula "sum(max(k,p),[-1]+q_$0,s)<=eps")
    (backchain "with(eps:rr,s:[zz,rr],p:zz,
  forall(j,j_1:zz,
    p<=j and j<=j_1 implies sum(j,j_1,s)<=eps));")
    (apply-macete-with-minor-premises maximum-2nd-arg)
    simplify
    (apply-macete-with-minor-premises sum-definedness)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "dist(f(k_$0),f(1+k_$0))<=s(k_$0)")
    (apply-macete-with-minor-premises commutative-law-for-addition)
    (backchain "with(s:[zz,rr],f:[zz,pp],k:zz,
  forall(j:zz,k<=j implies dist(f(j),f(j+1))<=s(j)));")
    (cut-with-single-formula "k<=max(k,p)")
    simplify
    (apply-macete-with-minor-premises maximum-1st-arg)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises small%tails%of%summable%nonnegative%sequence)
    direct-and-antecedent-inference-strategy
    

    )

   )
  (usages transportable-macete)
  (theory metric-spaces))


;;Examples:

(def-theorem geometric-series-formula
  "forall(a,r:rr,p,q:zz, 
     0<=p and p<=q and not(r=0) and not(r=1) 
      implies 
     sum(p,q,lambda(j:zz,r^j*a))=a*r^p/(1-r)*(1-r^(q-p+1)))"
  lemma
  (theory h-o-real-arithmetic)
  
  (proof
   (

    (apply-macete-with-minor-premises fractional-expression-manipulation)
    (induction integer-inductor ("q"))
    
    )))

(def-theorem geometric-series-upper-estimate-lemma
  "forall(a,r:rr,p,q:zz, 
     1<=p and p<=q and 0<r and r<1 and 0<=a 
      implies 
     a*r^p/(1-r)*(1-r^(q-p+1)) <= a*r^p/(1-r))"
  lemma
  (theory h-o-real-arithmetic)

  (proof

   (

    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (apply-macete-with-minor-premises positivity-for-products)
    direct-and-antecedent-inference-strategy
    (force-substitution "0<=r^(1+q)" "0<r^(1+q)" (0))
    (apply-macete-with-minor-premises positivity-for-r^n)
    simplify
    
    )))

(def-theorem  geometric-series-upper-estimate
  "forall(a,r:rr,p,q:zz, 
     1<=p and p<=q and 0<r and r<1 and 0<=a 
      implies 
     sum(p,q,lambda(j:zz,r^j*a))<=a*r^p/(1-r))"
  (theory h-o-real-arithmetic)
  
  (proof

   (

    (apply-macete-with-minor-premises geometric-series-formula)
    (apply-macete-with-minor-premises  geometric-series-upper-estimate-lemma)

    )))


(def-theorem  geometric-series-is-summable%nonnegative
  "forall(a,r:rr,p,q:zz, 0<r and r<1 and 0<=a 
           implies
           summable%nonnegative(lambda(j:zz,r^j*a)))"
  
  (proof

   (

    (unfold-single-defined-constant (0) summable%nonnegative)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("1"))
    (apply-macete-with-minor-premises positivity-for-products)
    (cut-with-single-formula "0<r^n")
    simplify
    (apply-macete-with-minor-premises positivity-for-r^n)
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    (instantiate-existential ("1"))
    (apply-macete-with-minor-premises sum-definedness)
    beta-reduce-repeatedly
    simplify
    (instantiate-existential ("a*r^1/(1-r)"))
    (unfold-single-defined-constant (0) majorizes)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (backchain "with(a,r:rr,x_$1:zz,x:rr,x=sum(1,x_$1,lambda(j_$0:zz,r^j_$0*a)));")
    (case-split ("1<=x_$1"))
    (apply-macete-with-minor-premises geometric-series-upper-estimate)
    direct-and-antecedent-inference-strategy
    simplify
    (unfold-single-defined-constant (0) sum)
    simplify
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify

    ))


  (theory h-o-real-arithmetic))
   


