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


(herald limits)

(def-theorem metric-separation-for-reals 
  "forall(x,y:rr,x=y 
   iff
 forall(r:rr,0<r implies forsome(z:rr, abs(z-x)<=r and abs(z-y)<=r)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (backchain "with(y,x:rr,x=y);")
    (instantiate-existential ("y"))
    (block 
      (script-comment "proving abs(y-y)=0")
      (unfold-single-defined-constant (0) abs)
      (prove-by-logic-and-simplification 3))
    (instantiate-universal-antecedent "with(p:prop,p);" ("abs(x-y)/3"))
    (contrapose "with(p:prop,p);")
    (block 
      (script-comment "prove 0<abs(x-y)/3")
      (unfold-single-defined-constant (0) abs)
      (case-split ("0<=x-y"))
      simplify
      simplify)
    (block 
      (script-comment "the distance from z_$0 to both x and y is less 
                       than a third of the distance between x and y")
      (apply-macete-with-minor-premises point-separation-for-rr-distance)
      beta-reduce-repeatedly
      (cut-with-single-formula "abs(x-y)<=abs(z_$0-y)+abs(z_$0-x)")
      simplify)
    (weaken (0 1))
    (force-substitution "x-y" "(x-z_$0)+(z_$0-y)" (0))
    (force-substitution "abs(z_$0-y)+abs(z_$0-x)" "abs(x-z_$0)+abs(z_$0-y)" (0))
    (apply-macete-with-minor-premises triangle-inequality)
    (block 
      (script-comment "another triviality.")
      (force-substitution "z_$0-x" "[-1]*(x-z_$0)" (0))
      (apply-macete-with-minor-premises absolute-value-product)
      (apply-macete absolute-value-non-positive)
      simplify
      simplify)
    simplify
    )))


(def-constant lim%rr
  "lambda(s:[zz,rr],iota(x:rr, forall(eps:rr,0<eps implies forsome(n:zz, 
        forall(p:zz, n<=p implies abs(x-s(p))<=eps)))))"
  (theory h-o-real-arithmetic))

(def-theorem characterization-of-real-limit
  "forall(s:[zz,rr],x:rr,lim%rr(s)=x iff forall(eps:rr,0<eps implies forsome(n:zz, 
forall(p:zz, n<=p implies abs(x-s(p))<=eps))))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant (0) lim%rr)
    direct-and-antecedent-inference-strategy
    (contrapose "with(x,r:rr,r=x);")
    (block 
      (eliminate-defined-iota-expression 0 w)
      (contrapose "with(p:prop,forall(eps:rr,0<eps implies forsome(n:zz,p)));")
      auto-instantiate-existential
      (backchain "with(x,w:rr,w=x);")
      (backchain "with(p:prop,forall(n:zz,forsome(p:zz,with(p:prop,p))));"))
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "uniqueness.")
      (apply-macete-with-minor-premises metric-separation-for-reals)
      direct-and-antecedent-inference-strategy
       
      (instantiate-universal-antecedent
       "with(p:prop,forall(eps:rr,0<eps implies forsome(n:zz,p)));"
       ("r"))
      (instantiate-universal-antecedent
       "with(p:prop,forall(eps:rr,0<eps implies forsome(n:zz,p)));"
       ("r"))
      (instantiate-existential ("s(max(n,n_$0))"))
      (cut-with-single-formula "forall(x,y:rr,abs(x-y)=abs(y-x))")
      (backchain "with(p:prop,forall(x,y:rr,p));")
      (backchain "with(r:rr,s:[zz,rr],b_$0:rr,n:zz,
  forall(p:zz,n<=p implies abs(b_$0-s(p))<=r));")
      (apply-macete-with-minor-premises maximum-1st-arg)
      (cut-with-single-formula "abs(b_$0-s(max(n,n_$0)))<=r")
      (script-comment "we needed definedness here.")
      (force-substitution "y-x" "[-1]*(x-y)" (0))
      (apply-macete-with-minor-premises absolute-value-product)
      (apply-macete absolute-value-non-positive)
      simplify
      simplify
      (cut-with-single-formula "forall(x,y:rr, abs(x-y)=abs(y-x))")
      (backchain "with(p:prop,forall(x,y:rr,p));")
      (backchain "with(r:rr,s:[zz,rr],x:rr,n_$0:zz,
  forall(p:zz,n_$0<=p implies abs(x-s(p))<=r));")
      (apply-macete-with-minor-premises maximum-2nd-arg)
      (cut-with-single-formula "abs(b_$0-s(max(n,n_$0)))<=r")
      (backchain "with(r:rr,s:[zz,rr],b_$0:rr,n:zz,
  forall(p:zz,n<=p implies abs(b_$0-s(p))<=r));")
      (apply-macete-with-minor-premises maximum-1st-arg))




    )))


(def-theorem abs-free-characterization-of-real-limit
  "forall(s:[zz,rr],x:rr,
     lim%rr(s)=x
      iff 
     forall(eps:rr,
       0<eps
        implies 
       forsome(n:zz,
         forall(p:zz,
           n<=p implies x-eps<=s(p) and s(p)<=x+eps))))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises characterization-of-real-limit)
    (force-substitution "abs(x-s(p))<=eps" "x-eps<=s(p) and s(p)<=x+eps" (0))
    (case-split ("#(s(p))"))
    (unfold-single-defined-constant (0) abs)
    (case-split ("s(p)<=x"))
    simplify
    simplify
    direct-and-antecedent-inference-strategy

    )))

(def-theorem existence-of-real-limit
  "forall(s:[zz,rr],
    #(lim%rr(s))
     iff 
    forsome(x:rr,
      forall(eps:rr,
        0<eps
         implies 
        forsome(n:zz,
          forall(p:zz,n<=p implies abs(x-s(p))<=eps)))))"
  (theory h-o-real-arithmetic)


  (proof


   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lim%rr(s)=lim%rr(s)")
    (incorporate-antecedent "with(s:[zz,rr],lim%rr(s)=lim%rr(s));")
    (apply-macete-with-minor-premises characterization-of-real-limit)
    direct-inference
    (instantiate-existential ("lim%rr(s)"))
    (cut-with-single-formula "lim%rr(s)=x")
    (apply-macete-with-minor-premises characterization-of-real-limit)


    )

   ))

(def-theorem homogeneity-of-real-limit
  "forall(a:[zz,rr], b:rr, #(lim%rr(a)) implies 
          lim%rr(lambda(n:zz,b*a(n)))=b*lim%rr(a))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:rr, lim%rr(a)=s)")
    (antecedent-inference "with(a:[zz,rr],forsome(s:rr,lim%rr(a)=s));")
    (backchain "with(s:rr,a:[zz,rr],lim%rr(a)=s);")
    (apply-macete-with-minor-premises characterization-of-real-limit)
    direct-and-antecedent-inference-strategy
    beta-reduce-with-minor-premises
    (force-substitution "b*s-b*a(p)" "b*(s-a(p))" (0))
    (apply-macete-with-minor-premises absolute-value-product)
    (case-split ("abs(b)=0"))
    simplify
    (incorporate-antecedent "with(a:[zz,rr],#(lim%rr(a)));")
    (apply-macete-with-minor-premises existence-of-real-limit)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
     "with(p:prop, forall(eps:rr, 0<eps implies p))" ("1"))
    (simplify-antecedent "not(0<1);")
    (instantiate-existential ("n"))
    (instantiate-universal-antecedent "with(a:[zz,rr],x:rr,n:zz,
  forall(p:zz,n<=p implies abs(x-a(p))<=1));" ("p"))
    (force-substitution "abs(b)*abs(s-a(p))<=eps" "abs(s-a(p))<=eps/abs(b)" (0))
    (incorporate-antecedent "with(s:rr,a:[zz,rr],lim%rr(a)=s);")
    (apply-macete-with-minor-premises characterization-of-real-limit)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent 
      "with(p:prop, forall(eps:rr, 0<eps implies p))" ("eps/abs(b)"))
    (contrapose "with(b,eps:rr,not(0<eps/abs(b)));")
    simplify
    (cut-with-single-formula "0<abs(b)")
    simplify
    (apply-macete-with-minor-premises positivity-of-inverse)
    simplify
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    simplify
    (instantiate-existential ("lim%rr(a)"))
    )))

(def-theorem lim%rr-negative
  "forall(a:[zz,rr], b:rr,
          lim%rr(lambda(n:zz,[-1]*a(n)))==-lim%rr(a))"  
  (theory h-o-real-arithmetic)
  (proof
   (
    insistent-direct-inference-strategy
    (antecedent-inference "with(a:[zz,rr],
  #(lim%rr(lambda(n:zz,[-1]*a(n)))) or #(-lim%rr(a)));")
    (force-substitution "a" "lambda(n:zz,[-1]*lambda(n:zz,[-1]*a(n))(n))" (1))
    (apply-macete-locally homogeneity-of-real-limit (0) "lim%rr(lambda(n:zz,[-1]*lambda(n:zz,[-1]*a(n))(n)))")
    simplify
    insistent-direct-inference
    extensionality
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    simplify
    (apply-macete-with-minor-premises homogeneity-of-real-limit)
    simplify

    )))

(def-theorem lim%rr-preserves-upper-bound
  "forall(a:[nn,rr], b:rr, forall(i:nn, a(i)<=b) and #(lim%rr(a)) implies lim%rr(a)<=b)"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:rr, lim%rr(a)=s)")
    (antecedent-inference "with(a:[nn,rr],forsome(s:rr,lim%rr(a)=s));")
    (backchain "with(s:rr,a:[nn,rr],lim%rr(a)=s);")
    (incorporate-antecedent "with(s:rr,a:[nn,rr],lim%rr(a)=s);")
    (apply-macete-with-minor-premises abs-free-characterization-of-real-limit)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent
     "with(p:prop,  forall(eps:rr, 0<eps implies p))"
     ("(s-b)/2"))
    simplify
    (instantiate-universal-antecedent "with(a:[nn,rr],b,s:rr,n_$0:zz,
  forall(p_$0:zz,
    n_$0<=p_$0
     implies 
    s-(s-b)/2<=a(p_$0) and a(p_$0)<=s+(s-b)/2));" ("n_$0"))
    (simplify-antecedent "with(n_$0:zz,not(n_$0<=n_$0));")
    (instantiate-universal-antecedent "with(b:rr,a:[nn,rr],forall(i:nn,a(i)<=b));" ("n_$0"))
    simplify
    (instantiate-existential ("lim%rr(a)"))


    )))

(def-theorem lim%rr-preserves-lower-bound
  "forall(a:[nn,rr], b:rr, forall(i:nn, b<=a(i)) and #(lim%rr(a)) 
              implies
         b<=lim%rr(a))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lim%rr(lambda(n:zz,[-1]*a(n)))<=-b")
    (incorporate-antecedent "with(b:rr,a:[nn,rr],lim%rr(lambda(n:zz,[-1]*a(n)))<=-b);")
    (apply-macete-with-minor-premises homogeneity-of-real-limit)
    simplify
    (apply-macete-with-minor-premises lim%rr-preserves-upper-bound)
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises homogeneity-of-real-limit)
    simplify
    (weaken (0 1))
    sort-definedness
    direct-and-antecedent-inference-strategy
    (case-split ("#(xx_0,zz)"))
    (beta-reduce-antecedent "with(xx_0:ind,a:[nn,rr],#(lambda(n:zz,[-1]*a(n))(xx_0)));")

    )))

(def-constant bounded%non%decreasing%seq
  "lambda(a:[nn,rr], forsome(b:rr, forall(n:nn, a(n)<=a(n+1) and a(n)<=b)))"
  (theory h-o-real-arithmetic))

(def-theorem bounded%non%decreasing%seq-convergent
  "forall(a:[nn,rr], bounded%non%decreasing%seq(a) 
                        implies
                     forall(n:nn, a(n)<=lim%rr(a)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant (0) bounded%non%decreasing%seq)
    direct-and-antecedent-inference-strategy
    (instantiate-theorem completeness ("lambda(x:rr, forsome(n:nn, x=a(n)))"))
    (contrapose "with(a:[nn,rr],
  forall(x_0:rr,not(lambda(x:rr,forsome(n:nn,x=a(n)))(x_0))));")
    (instantiate-existential ("a(0)"))
    beta-reduce-with-minor-premises
    (instantiate-existential ("0"))
    simplify
    (instantiate-universal-antecedent "with(b:rr,a:[nn,rr],forall(n:nn,a(n)<=a(n+1) and a(n)<=b));" ("0"))
    (beta-reduce-antecedent "with(a:[nn,rr],
  forall(alpha:rr,
    forsome(theta:rr,
      lambda(x:rr,forsome(n:nn,x=a(n)))(theta)
       and 
      not(theta<=alpha))));")
    (contrapose "with(a:[nn,rr],
  forall(alpha:rr,
    forsome(theta:rr,
      forsome(n:nn,theta=a(n)) and not(theta<=alpha))));")
    (instantiate-existential ("b"))
    (antecedent-inference "with(a:[nn,rr],theta:rr,forsome(n:nn,theta=a(n)));")
    (backchain "with(n_$0:nn,a:[nn,rr],theta:rr,theta=a(n_$0));")
    (beta-reduce-antecedent "with(gamma:rr,a:[nn,rr],
  forall(theta:rr,
    lambda(x:rr,forsome(n:nn,x=a(n)))(theta)
     implies 
    theta<=gamma));")
    (cut-with-single-formula "lim%rr(a)=gamma")
    (backchain "with(gamma:rr,a:[nn,rr],lim%rr(a)=gamma);")
    (backchain "with(gamma:rr,a:[nn,rr],
  forall(theta:rr,
    forsome(n:nn,theta=a(n)) implies theta<=gamma));")
    (instantiate-existential ("n"))
    (apply-macete-with-minor-premises abs-free-characterization-of-real-limit)
    direct-and-antecedent-inference-strategy
    (beta-reduce-antecedent "with(gamma:rr,a:[nn,rr],
  forall(gamma_1:rr,
    forall(theta:rr,
      lambda(x:rr,forsome(n:nn,x=a(n)))(theta)
       implies 
      theta<=gamma_1)
     implies 
    gamma<=gamma_1));")
    (instantiate-universal-antecedent "with(gamma:rr,a:[nn,rr],
  forall(gamma_1:rr,
    forall(theta:rr,
      forsome(n:nn,theta=a(n)) implies theta<=gamma_1)
     implies 
    gamma<=gamma_1));" ("gamma-eps"))
    (contrapose "with(eps,gamma,theta_$0:rr,not(theta_$0<=gamma-eps));")
    (backchain "with(n_$0:nn,a:[nn,rr],theta_$0:rr,theta_$0=a(n_$0));")
    (instantiate-universal-antecedent "with(a:[nn,rr],eps,gamma:rr,
  forall(n:zz,
    forsome(p:zz,
      n<=p
       and 
      (not(gamma-eps<=a(p)) or not(a(p)<=gamma+eps)))));" ("n_$0"))
    (cut-with-single-formula "a(n_$0)<=a(p)")
    simplify
    (weaken (0 2 3 4))
    (induction integer-inductor ("p"))
    (instantiate-universal-antecedent "with(b:rr,a:[nn,rr],forall(n:nn,a(n)<=a(n+1) and a(n)<=b));" ("t"))
    simplify
    (instantiate-universal-antecedent "with(gamma:rr,a:[nn,rr],
  forall(theta:rr,
    forsome(n:nn,theta=a(n)) implies theta<=gamma));" ("a(p)"))
    (instantiate-universal-antecedent "with(p:zz,a:[nn,rr],forall(n_$0:nn,not(a(p)=a(n_$0))));" ("p"))
    (simplify-antecedent "with(p:zz,a:[nn,rr],not(a(p)=a(p)));")
    (instantiate-universal-antecedent "with(b:rr,a:[nn,rr],forall(n:nn,a(n)<=a(n+1) and a(n)<=b));" ("p"))
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    (cut-with-single-formula "0<=n_$0")
    simplify
    (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
    (apply-macete-with-minor-premises nn-defining-axiom_h-o-real-arithmetic)
    simplify
    (cut-with-single-formula "0<=n_$0")
    simplify
    (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
    (simplify-antecedent "with(eps,gamma:rr,p:zz,a:[nn,rr],not(a(p)<=gamma+eps));")
    (cut-with-single-formula "a(n_$0)<=a(p)")
    (weaken (0 2 3 4))
    (simplify-antecedent "with(eps,gamma:rr,gamma<=gamma-eps);")
    )))

(def-constant bounded%non%increasing%seq
  "lambda(a:[nn,rr], forsome(b:rr, forall(n:nn, a(n+1)<=a(n) and b<=a(n))))"
  (theory h-o-real-arithmetic))

(def-theorem bounded%nonincreasing%seq-convergent
  "forall(a:[nn,rr], bounded%non%increasing%seq(a) 
                        implies
                     forall(n:nn, lim%rr(a)<=a(n)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant (0) bounded%non%increasing%seq)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lambda(n:zz,[-1]*a(n))(n)<=lim%rr(lambda(n:zz,[-1]*a(n))) ")
    (cut-with-single-formula "#(lim%rr(lambda(n:zz,[-1]*a(n))))")
    (incorporate-antecedent "with(n:nn,a:[nn,rr],
  lambda(n:zz,[-1]*a(n))(n)<=lim%rr(lambda(n:zz,[-1]*a(n))));")
    (apply-macete-with-minor-premises homogeneity-of-real-limit)
    simplify
    (incorporate-antecedent "with(a:[nn,rr],#(lim%rr(lambda(n:zz,[-1]*a(n)))));")
    (apply-macete-with-minor-premises lim%rr-negative)
    simplify
    (apply-macete-with-minor-premises bounded%non%decreasing%seq-convergent)
    (unfold-single-defined-constant (0) bounded%non%decreasing%seq)
    beta-reduce-with-minor-premises
    (instantiate-existential ("-b"))
    beta-reduce-repeatedly
    simplify
    (instantiate-universal-antecedent "with(b:rr,a:[nn,rr],forall(n:nn,a(n+1)<=a(n) and b<=a(n)));" ("n_$0"))
    simplify
    beta-reduce-repeatedly
    simplify
    (weaken (0))
    sort-definedness
    direct-and-antecedent-inference-strategy
    (case-split ("#(xx_0,zz)"))
    simplify

    )))

;;;(def-constant nested%seq
;;;  "lambda(a,b:[nn,rr], forall(n:nn, a(n)<=a(n+1) and b(n+1)<=b(n) and a(n)<=b(n)))"
;;;  (theory h-o-real-arithmetic))
;;;
;;;(def-constant convergent%nested%seq
;;;  "lambda(a,b:[nn,rr], lim%rr(lambda(n:zz,b(n)-a(n)))=0 and nested%seq(a,b))"
;;;  (theory h-o-real-arithmetic))
;;;

(def-theorem additivity-of-real-limit
  "forall(a,b:[zz,rr],  #(lim%rr(a)) and #(lim%rr(b)) implies 
          lim%rr(lambda(n:zz,a(n)+b(n)))=lim%rr(a)+lim%rr(b))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s,t:rr, lim%rr(a)=s and lim%rr(b)=t)")
    (antecedent-inference "with(b,a:[zz,rr],
  forsome(s,t:rr,lim%rr(a)=s and lim%rr(b)=t));")
    (backchain "with(t:rr,b:[zz,rr],s:rr,a:[zz,rr],
  lim%rr(a)=s and lim%rr(b)=t);")
    (backchain "with(t:rr,b:[zz,rr],s:rr,a:[zz,rr],
  lim%rr(a)=s and lim%rr(b)=t);")
    (apply-macete-with-minor-premises abs-free-characterization-of-real-limit)
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    (incorporate-antecedent "with(t:rr,b:[zz,rr],s:rr,a:[zz,rr],
  lim%rr(a)=s and lim%rr(b)=t);")
    (apply-macete-with-minor-premises abs-free-characterization-of-real-limit)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,  forall(eps:rr, 0<eps  implies p))" ("eps/2"))
    (simplify-antecedent "with(eps:rr,not(0<eps/2));")
    (instantiate-universal-antecedent "with(p:prop,  forall(eps:rr, 0<eps  implies p))" ("eps/2"))
    (simplify-antecedent "with(eps:rr,not(0<eps/2));")
    (cut-with-single-formula "forsome(s:zz, n_$1<=s and n_$0<=s)")
    (antecedent-inference "with(n_$0,n_$1:zz,forsome(s:zz,n_$1<=s and n_$0<=s));")
    (instantiate-existential ("s_$0"))
    (instantiate-universal-antecedent "with(a:[zz,rr],eps,s:rr,n_$1:zz,
  forall(p_$0:zz,
    n_$1<=p_$0 implies 
    s-eps/2<=a(p_$0) and a(p_$0)<=s+eps/2));" ("p"))
    (simplify-antecedent "with(p,n_$1:zz,not(n_$1<=p));")
    (instantiate-universal-antecedent "with(b:[zz,rr],eps,t:rr,n_$0:zz,
  forall(p_$0:zz,
    n_$0<=p_$0 implies 
    t-eps/2<=b(p_$0) and b(p_$0)<=t+eps/2));" ("p"))
    (simplify-antecedent "with(p,n_$0:zz,not(n_$0<=p));")
    simplify
    (instantiate-universal-antecedent "with(a:[zz,rr],eps,s:rr,n_$1:zz,
  forall(p_$0:zz,
    n_$1<=p_$0 implies 
    s-eps/2<=a(p_$0) and a(p_$0)<=s+eps/2));" ("p"))
    (simplify-antecedent "with(p,n_$1:zz,not(n_$1<=p));")
    (instantiate-universal-antecedent "with(b:[zz,rr],eps,t:rr,n_$0:zz,
  forall(p_$0:zz,
    n_$0<=p_$0 implies 
    t-eps/2<=b(p_$0) and b(p_$0)<=t+eps/2));" ("p"))
    (simplify-antecedent "with(p,n_$0:zz,not(n_$0<=p));")
    simplify
    (instantiate-existential ("max(n_$1,n_$0)"))
    simplify
    simplify
    (instantiate-existential ("lim%rr(a)" "lim%rr(b)"))


    )))

(comment
 (def-theorem real-convergent-bounded
  "forall(a:[zz,rr], #(lim%rr(a))  implies forsome(l,u:rr, k:zz, forall(n:zz, k<=n implies l<=a(n) 
   and a(n)<=u)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:rr, lim%rr(a)=s)")
    (antecedent-inference "with(a:[zz,rr],forsome(s:rr,lim%rr(a)=s));")
    (incorporate-antecedent "with(s:rr,a:[zz,rr],lim%rr(a)=s);")
    (apply-macete-with-minor-premises abs-free-characterization-of-real-limit)
    direct-and-antecedent-inference-strategy
    (weaken (1))
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr,
    0<eps  implies p))" ("1"))
    (simplify-antecedent "not(0<1);")
    (instantiate-existential ("s-1" "s+1" "n"))
    (instantiate-existential ("lim%rr(a)"))

    ))))

(def-theorem real-convergent-bounded
  "forall(a:[zz,rr], #(lim%rr(a))  
     implies 
   forsome(u:rr, k:zz, forall(n:zz, k<=n implies  abs(a(n))<=u)))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises existence-of-real-limit)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,
  forall(eps:rr,  0<eps implies p))" ("1"))
    (simplify-antecedent "not(0<1);")
    (instantiate-existential ("abs(x)+1" "n"))
    (cut-with-single-formula "abs(a(n_$0))-abs(x)<=abs(x-a(n_$0))")
    (instantiate-universal-antecedent "with(q:prop,forall(p:zz,q))" ("n_$0"))
    simplify
    (cut-with-single-formula "forall(a,b:rr, abs(a)-abs(b)<=abs(b-a))")
    (backchain "forall(a,b:rr,abs(a)-abs(b)<=abs(b-a));")
    (instantiate-universal-antecedent "with(a:[zz,rr],x:rr,n:zz,
  forall(p:zz,n<=p implies abs(x-a(p))<=1));" ("n_$0"))
    (weaken (0 1))
    unfold-defined-constants
    (prove-by-logic-and-simplification 3)

    )))

(def-theorem limit-of-constants
  "forall(s:rr, lim%rr(lambda(k:zz, s))=s)"
  (theory h-o-real-arithmetic)
  (proof

   (
    (apply-macete-with-minor-premises abs-free-characterization-of-real-limit)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("0"))
    beta-reduce-repeatedly
    simplify
    simplify

    )))

(def-theorem real-limit-square
  "forall(a:[zz,rr],  #(lim%rr(a))  implies 
          lim%rr(lambda(n:zz,a(n)^2))=lim%rr(a)^2)"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(s:rr,lim%rr(a)=s)")
    (move-to-sibling 1)
    (instantiate-existential ("lim%rr(a)"))
    (antecedent-inference "with(a:[zz,rr],forsome(s:rr,lim%rr(a)=s));")
    (backchain-repeatedly ("with(s:rr,a:[zz,rr],lim%rr(a)=s);"))
    (incorporate-antecedent "with(s:rr,a:[zz,rr],lim%rr(a)=s);")
    (apply-macete-with-minor-premises characterization-of-real-limit)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(m:rr,p:zz, forall(k:zz,p<=k implies abs(s+a(k))<=m))")
    (move-to-sibling 1)
    (force-substitution "s+a(k)" "lambda(k:zz,s+a(k))(k)" (0))
    (move-to-sibling 1)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises real-convergent-bounded)
    (force-substitution "s" "lambda(k:zz,s)(k)" (0))
    (apply-macete-with-minor-premises additivity-of-real-limit)
    simplify
    (apply-macete-with-minor-premises limit-of-constants)
    simplify
    beta-reduce-repeatedly
    (antecedent-inference "with(a:[zz,rr],s:rr,
  forsome(m:rr,p:zz,
    forall(k:zz,p<=k implies abs(s+a(k))<=m)));")
    (instantiate-universal-antecedent "with(a:[zz,rr],s:rr,
  forall(eps:rr,
    0<eps
     implies 
    forsome(n:zz,
      forall(p:zz,n<=p implies abs(s-a(p))<=eps))));" ("eps/max(1,m)"))
    (contrapose "with(m,eps:rr,not(0<eps/max(1,m)));")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (instantiate-existential ("max(n_$0,p)"))
    (force-substitution "s^2-a(p_$0)^2" "(s-a(p_$0))*(s+a(p_$0))" (0))
    (move-to-sibling 1)
    (cut-with-single-formula "#(a(p_$0))")
    simplify
    (instantiate-universal-antecedent "with(m:rr,a:[zz,rr],s:rr,p:zz,
  forall(k:zz,p<=k implies abs(s+a(k))<=m));" ("p_$0"))
    (cut-with-single-formula "p<=max(n_$0,p)")
    simplify
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("(eps/max(1,m))*m"))
    (apply-macete-with-minor-premises absolute-value-product)
    (apply-macete-with-minor-premises monotone-product-lemma)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises non-negativity-of-absolute-value)
    (backchain "with(m,eps:rr,a:[zz,rr],s:rr,n_$0:zz,
  forall(p_$0:zz,
    n_$0<=p_$0 implies abs(s-a(p_$0))<=eps/max(1,m)));")
    (cut-with-single-formula "n_$0<=max(n_$0,p)")
    simplify
    (apply-macete-with-minor-premises maximum-1st-arg)
    (apply-macete-with-minor-premises non-negativity-of-absolute-value)
    (backchain "with(m:rr,a:[zz,rr],s:rr,p:zz,
  forall(k:zz,p<=k implies abs(s+a(k))<=m));")
    (cut-with-single-formula "p<=max(n_$0,p)")
    simplify
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify

    )))

(def-theorem product-in-terms-of-squares-lemma
  "forall(a,b:rr, a*b=1/2*((a+b)^2+[-1]*(a^2+b^2)))"
  
  (proof
   (
    simplify
    ))

  (theory h-o-real-arithmetic))

;;;(def-theorem constant-beta-reduction
;;;  "forall(a:rr, x:zz, lambda(z:zz,a)(x)=a)"
;;;   (theory h-o-real-arithmetic)
;;;   (proof
;;;    (
;;;     beta-reduce-repeatedly
;;;     )))
;;;   

(def-schematic-macete abstraction-builder-for-sums-of-sequences
  "with(a,b:rr,
       lim%rr(lambda(x:zz,a+b))=lim%rr(lambda(x:zz,lambda(x:zz,a)(x)+lambda(x:zz,b)(x))))"
  (theory h-o-real-arithmetic)
  null)

(def-schematic-macete abstraction-builder-for-products-of-sequences
  "with(a,b:rr,
       lim%rr(lambda(x:zz,a*b))=lim%rr(lambda(x:zz,lambda(x:zz,a)(x)*lambda(x:zz,b)(x))))"
  (theory h-o-real-arithmetic)
  null)

(def-schematic-macete abstraction-builder-for-squares-of-sequences
  "with(a:rr, lim%rr(lambda(x:zz,a^2))=lim%rr(lambda(x:zz,lambda(x:zz,a)(x)^2)))"
  (theory h-o-real-arithmetic)
  null)

(def-compound-macete abstraction-for-sequences
  (series
   (sound
    abstraction-builder-for-sums-of-sequences
    beta-reduce-repeatedly
    beta-reduce-repeatedly)
   (sound
    abstraction-builder-for-products-of-sequences
    beta-reduce-repeatedly
    beta-reduce-repeatedly)
   (sound
    abstraction-builder-for-squares-of-sequences
    beta-reduce-repeatedly
    beta-reduce-repeatedly)))

(def-theorem homogeneity-of-real-limit-corollary
  "forall(a:[zz,rr], s,b:rr, b*lim%rr(a)=s implies 
                             lim%rr(lambda(n:zz,b*a(n)))=s)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises homogeneity-of-real-limit)


    )))

(def-theorem additivity-of-real-limit-corollary
  "forall(a,b:[zz,rr], s:rr, lim%rr(a)+lim%rr(b)=s
                         implies 
                         lim%rr(lambda(n:zz,a(n)+b(n)))=s)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises additivity-of-real-limit)


    )))

(def-theorem real-limit-square-corollary
  "forall(a:[zz,rr], s:rr, lim%rr(a)^2=s
            implies 
          lim%rr(lambda(n:zz,a(n)^2))=s)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (apply-macete-with-minor-premises real-limit-square)


    )))

(def-theorem equal-arguments-implies-equal
  "forall(op:[rr,rr,rr],a,b,c,d:rr, a=c and b=d and #(op(a,b)) implies op(a,b)=op(c,d))"
  (theory h-o-real-arithmetic)
  (proof
   (
    simplify

    )))

;;;(def-compound-macete apply-limit-theorems
;;;  (repeat
;;;   equal-arguments-implies-equal
;;;   product-in-terms-of-squares-lemma
;;;   abstraction-for-sequences
;;;   constant-beta-reduction
;;;   homogeneity-of-real-limit-corollary
;;;   real-limit-square-corollary
;;;   additivity-of-real-limit-corollary
;;;   limit-of-constants
;;;   beta-reduce-repeatedly))
;;

;;;(def-compound-macete lim-of-sums-of-sequences
;;;  (repeat
;;;   (sound
;;;    abstraction-builder-for-sums-of-sequences
;;;    beta-reduce-repeatedly
;;;    beta-reduce-repeatedly)
;;;   additivity-of-real-limit
;;;   beta-reduce-repeatedly))
;;;
;;;(def-compound-macete lim-of-constant-times-sequence
;;;  (repeat
;;;   (sound
;;;    abstraction-builder-for-constant-times-sequence
;;;    beta-reduce-repeatedly
;;;    beta-reduce-repeatedly)
;;;   homogeneity-of-real-limit
;;;   beta-reduce-repeatedly))
;;;
;;;(def-compound-macete  abstraction-for-products-of-sequences
;;;  (sound
;;;   abstraction-builder-for-products-of-sequences
;;;   beta-reduce-repeatedly
;;;   beta-reduce-repeatedly))
;;;
;;;(def-compound-macete abstraction-for-sums-and-squares-of-sequences
;;;  (sound
;;;   (series
;;;    abstraction-builder-for-sums-of-sequences
;;;    abstraction-builder-for-squares-of-sequences)
;;;   beta-reduce-repeatedly
;;;   beta-reduce-repeatedly))
;;;
;;;(def-compound-macete product-sums-and-squares-of-limits
;;;  (repeat
;;;    product-in-terms-of-squares-lemma
;;;    abstraction-for-products-of-sequences
;;;    limit-of-constants
;;;    homogeneity-of-real-limit
;;;    abstraction-for-sums-and-squares-of-sequences
;;;    real-limit-square
;;;    additivity-of-real-limit
;;;    ))
;;;

(def-theorem real-limit-product
  "forall(a,b:[zz,rr],  #(lim%rr(a))  and  #(lim%rr(b))implies 
          lim%rr(lambda(n:zz,a(n)*b(n)))=lim%rr(a)*lim%rr(b))"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises product-in-terms-of-squares-lemma)
    (force-substitution "((a(n)+b(n))^2+[-1]*(a(n)^2+b(n)^2))" "lambda(n:zz,((a(n)+b(n))^2+[-1]*(a(n)^2+b(n)^2)))(n)" (0))
    (move-to-sibling 1)
    beta-reduce-repeatedly
    (apply-macete homogeneity-of-real-limit-corollary)
    (apply-macete-with-minor-premises equal-arguments-implies-equal)
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises abstraction-for-sequences)
    (apply-macete additivity-of-real-limit-corollary)
    (apply-macete-with-minor-premises equal-arguments-implies-equal)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises abstraction-for-sequences)
    (apply-macete real-limit-square-corollary)
    (apply-macete-with-minor-premises abstraction-for-sequences)
    (apply-macete-with-minor-premises equal-arguments-implies-equal)
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    (weaken (0))
    (apply-macete-with-minor-premises additivity-of-real-limit-corollary)
    simplify
    definedness
    (force-substitution "(a(n)^2+b(n)^2)" "lambda(n:zz,(a(n)^2+b(n)^2))(n)" (0))
    (apply-macete homogeneity-of-real-limit-corollary)
    (apply-macete-with-minor-premises equal-arguments-implies-equal)
    direct-and-antecedent-inference-strategy
    (weaken (2 1 0))
    (apply-macete-with-minor-premises abstraction-for-sequences)
    (apply-macete additivity-of-real-limit-corollary)
    (apply-macete equal-arguments-implies-equal)
    direct-and-antecedent-inference-strategy
    (apply-macete real-limit-square-corollary)
    simplify
    (weaken (0))
    (apply-macete real-limit-square-corollary)
    simplify
    definedness
    definedness
    beta-reduce-repeatedly
    definedness
    definedness


    )))

(comment
 (def-theorem convergent%nested%seq-implies-convergent
  "forall(a,b:[nn,rr], convergent%nested%seq(a,b) implies
                        forall(n:nn, a(n)<=lim%rr(a) and lim%rr(a)<=b(n)))"
  (theory h-o-real-arithmetic)
  (proof
   (
   
    ))))
