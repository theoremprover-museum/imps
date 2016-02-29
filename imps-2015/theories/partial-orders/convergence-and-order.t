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


(herald convergence-and-order)

(include-files
 (files (imps theories/partial-orders/real-order-properties)))


(def-theorem sup-minus-epsilon
  "forall(s:sets[rr],eps:rr,0<eps implies not(sup(s)-eps majorizes s))"
  (theory h-o-real-arithmetic)
  (proof
   (direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(sup(s)) or not(#(sup(s)))")
    (antecedent-inference "with(s:sets[rr],#(sup(s)) or not(#(sup(s))));")
    (cut-with-single-formula "not(sup(s)<=sup(s)-eps)")
    (contrapose "with(eps:rr,s:sets[rr],not(sup(s)<=sup(s)-eps));")
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify)))


(def-theorem sup-minus-epsilon-corollary
  "forall(s:sets[rr],eps:rr, 0<eps and #(sup(s)) implies forsome(x:rr, x in s and sup(s)-eps<x))"
  
  (proof
   (direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not(sup(s)-eps majorizes s)")
    (contrapose "with(eps:rr,s:sets[rr],not(sup(s)-eps majorizes s));")
    (unfold-single-defined-constant (0) majorizes)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p,q:prop,forall(x:rr,p or q))" ("x_$0"))
    simplify
    (apply-macete-with-minor-premises sup-minus-epsilon)))

  (theory h-o-real-arithmetic))


(def-theorem nondecreasing-sequences-converge
  "forall(f:[zz,rr],nondecreasing(f)
   and 
  forsome(n:zz,forall(k:zz,n<=k implies #(f(k))))
   and 
  #(sup(ran{f}))
   implies 
  forall(eps:rr,
    0<eps
     implies 
    forsome(k:zz,
      forall(j:zz,
        k<=j implies sup(ran{f})-f(j)<=eps))))"

  (proof
   (   

    (unfold-single-defined-constant (0) nondecreasing)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x:rr , x in ran{f} and sup(ran{f})-eps<x)")
    (antecedent-inference "with(eps:rr,f:[zz,rr],
  forsome(x:rr,x in ran{f} and sup(ran{f})-eps<x))")
    (antecedent-inference "with(eps,x:rr,f:[zz,rr],x in ran{f} and sup(ran{f})-eps<x)")
    (incorporate-antecedent "with(x:rr,f:[zz,rr],x in ran{f})")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("max(x_$0,n)"))
    (cut-with-single-formula "f(x_$0)<=f(j_$0)")
    simplify
    (backchain "with(f:[zz,rr],
  forall(n,p:zz,
    n<=p and #(f(n)) and #(f(p)) implies f(n)<=f(p)))")
    (cut-with-single-formula "n<=max(x_$0,n) and x_$0<=max(x_$0,n)")
    direct-and-antecedent-inference-strategy
    simplify
    (backchain "with(f:[zz,rr],n:zz,forall(k:zz,n<=k implies #(f(k))))")
    simplify
    (apply-macete-with-minor-premises maximum-1st-arg)
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (apply-macete-with-minor-premises sup-minus-epsilon-corollary)
    direct-and-antecedent-inference-strategy

    ))


  (theory h-o-real-arithmetic))


(def-theorem nondecreasing-sequences-converge-corollary
  "forall(f:[zz,rr],nondecreasing(f)
   and 
  forsome(n:zz,forall(k:zz,n<=k implies #(f(k))))
   and 
  #(sup(ran{f}))
   implies 
  forall(eps:rr,
    0<eps
     implies 
    forsome(k:zz,
      forall(j,j_1:zz,
        k<=j and j<=j_1 implies f(j_1)-f(j)<=eps))))"


  (proof

   (
    
    direct-and-antecedent-inference-strategy
    (instantiate-theorem nondecreasing-sequences-converge ("f"))
    (contrapose "with(f:[zz,rr],forall(n:zz,forsome(k:zz,n<=k and not(#(f(k))))))")
    (instantiate-existential ("n"))
    (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,0<eps implies p))" ("eps"))
    (instantiate-existential ("k"))
    (cut-with-single-formula "f(j_1)<=sup(ran{f}) and sup(ran{f})-f(j)<=eps")
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("f(max(j_1,n))"))
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (instantiate-existential ("max(j_1,n)"))
    (incorporate-antecedent "with(f:[zz,rr],nondecreasing(f));")
    (unfold-single-defined-constant (0) nondecreasing)
    direct-and-antecedent-inference-strategy
    (backchain "with(f:[zz,rr],
  forall(n,p:zz,
    n<=p and #(f(n)) and #(f(p)) implies f(n)<=f(p)));")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises maximum-1st-arg)
    (instantiate-universal-antecedent "with(eps:rr,f:[zz,rr],k:zz,
  forall(j:zz,k<=j implies sup(ran{f})-f(j)<=eps));" ("j_1"))
    (contrapose "with(j_1,k:zz,not(k<=j_1));")
    simplify
    (instantiate-universal-antecedent "with(eps:rr,f:[zz,rr],k:zz,
  forall(j:zz,k<=j implies sup(ran{f})-f(j)<=eps));" ("j_1"))
    (backchain "with(eps:rr,f:[zz,rr],k:zz,
  forall(j:zz,k<=j implies sup(ran{f})-f(j)<=eps));")


    ))
  (theory h-o-real-arithmetic))

;; A general form of the following result is shown in $ALGEBRA/monoids.t 
;; We prove it here independently:

(def-theorem sum-interval-additivity
  "forall(m,n,p:zz, f:[zz,rr], m<=n and n<=p implies 
            sum(m,n,f)+sum(n+1,p,f)==sum(m,p,f))"

  (proof

   (
    
    (induction integer-inductor ("p"))
    direct-inference
    (backchain-backwards "with(p,q:prop, p implies q)")
    direct-and-antecedent-inference-strategy
    simplify


    )

   )
  (theory h-o-real-arithmetic))

(def-theorem sum-nonnegativity
  "forall(f:[zz,rr], a,b:zz, forall(z:zz,a<=z and z<=b implies 0<=f(z)) 
                   implies 0<=sum(a,b,f))"
  (theory h-o-real-arithmetic)
  (proof

   (
    
    direct-and-antecedent-inference-strategy
    (case-split ("a<=b"))
    (induction integer-inductor ())
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "0<=sum(a,t,f) and 0<=f(1+t)")
    simplify
    (prove-by-logic-and-simplification 3)
    (unfold-single-defined-constant (0) sum)
    simplify


    )

   ))

(def-theorem nondecreasing%sums
  "forall(s:[zz,rr], k:zz, forall(n:zz,k<=n implies 0<=s(n))
	      implies
       nondecreasing(lambda(p:zz,sum(k,p,s))))"

  (theory h-o-real-arithmetic)
  (proof

   (

    (unfold-single-defined-constant (0) nondecreasing)
    direct-and-antecedent-inference-strategy
    (case-split ("k<=n_$0"))
    (force-substitution "sum(k,p_$0,s)" "sum(k,n_$0,s)+sum(n_$0+1,p_$0,s)" (0))
    simplify
    (apply-macete-with-minor-premises sum-nonnegativity)
    (prove-by-logic-and-simplification 3)
    (apply-macete-with-minor-premises sum-interval-additivity)
    (unfold-single-defined-constant (0) sum)
    simplify
    (case-split ("k<=p_$0"))
    (apply-macete-with-minor-premises sum-nonnegativity)
    (prove-by-logic-and-simplification 3)
    (unfold-single-defined-constant (0) sum)
    simplify


    )

   )   
				  
  )

(def-constant summable%nonnegative
  "lambda(s:[zz,rr], 
          forsome(k:zz, forall(n:zz,k<=n implies 0<=s(n) and 
                        #(sup(ran{lambda(p:zz,sum(k,p,s))})))))"
  (theory h-o-real-arithmetic))



(def-theorem small%tails%of%summable%nonnegative%sequence
  "forall(s:[zz,rr], summable%nonnegative(s) implies 
             forall(eps:rr,0<eps
                      implies 
                    forsome(p:zz,
                       forall(j,j_1:zz,
                         p<=j and j<=j_1 implies sum(j,j_1,s)<=eps))))"

  (proof

   (

    (unfold-single-defined-constant (0) summable%nonnegative)
    direct-and-antecedent-inference-strategy
    (instantiate-theorem nondecreasing-sequences-converge-corollary ("lambda(j:zz, sum(k,j,s))"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises nondecreasing%sums)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, k:zz,   forall(n:zz,  k<=n implies p))")
    (contrapose "with(s:[zz,rr],k:zz,
  forall(n_$0:zz,
    forsome(k_$0:zz,
      n_$0<=k_$0 and not(#(lambda(j:zz,sum(k,j,s))(k_$0))))));")
    beta-reduce-repeatedly
    (instantiate-existential ("k"))
    (cut-with-single-formula "0<=sum(k,k_$1,s)")
    (apply-macete-with-minor-premises sum-nonnegativity)
    (prove-by-logic-and-simplification 3)
    (contrapose "with(p:prop, not(p))")
    (backchain "with(s:[zz,rr],k:zz,
  forall(n:zz,
    k<=n
     implies 
    0<=s(n) and #(sup(ran{lambda(p:zz,sum(k,p,s))}))));")
    (instantiate-existential ("k"))
    simplify
    (beta-reduce-antecedent "with(p:prop,  forall(eps:rr, 0<eps implies p))")
    (auto-instantiate-universal-antecedent "with(p:prop,  forall(eps:rr, 0<eps implies p))")
    (instantiate-existential ("max(k,k_$0)+1"))
    (instantiate-universal-antecedent "with(eps:rr,s:[zz,rr],k,k_$0:zz,
  forall(j_$0,j_$1:zz,
    k_$0<=j_$0 and j_$0<=j_$1
     implies 
    sum(k,j_$1,s)-sum(k,j_$0,s)<=eps));" ("j-1" "j_1"))
    (contrapose "with(p:prop, not(p))")
    (cut-with-single-formula "k_$0<=max(k,k_$0)")
    simplify
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (simplify-antecedent "with(j_1,j:zz,not(j-1<=j_1));")
    (cut-with-single-formula "sum(k,j_1,s)==sum(k,j-1,s)+ sum((j-1)+1,j_1,s)")
    simplify
    (apply-macete-with-minor-premises sum-interval-additivity)
    (cut-with-single-formula "k<=max(k,k_$0)")
    simplify
    (apply-macete-with-minor-premises maximum-1st-arg)


    )
   )
  (theory h-o-real-arithmetic))


