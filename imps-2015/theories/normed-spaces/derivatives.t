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


(herald derivatives)

(include-files
 (files (imps theories/normed-spaces/one-sided-limits)))

(def-constant deriv
  "lambda(f:[ii,uu],x:ii, rlim(lambda(z:ii,(z-x)^[-1]*(f(z)-f(x))),x))"
  (theory mappings-from-an-interval-to-a-normed-space))

;;;(def-constant deriv
;;;  "lambda(f:[ii,uu],x:ii, iota(y:uu, forall(eps:rr, 0<eps implies forsome(z_0:ii, x<z_0 and 
;;;          forall(z:ii,x<z and z<=z_0 implies norm((z-x)^[-1]*(f(z)-f(x))-y)<=eps)))))"
;;;  (theory mappings-from-an-interval-to-a-normed-space))

;;The proof of the following theorem is identical to the proof of the 
;;existence-of-limit theorem in metric-space-supplements with appopriate
;;(and completely obvious) changes.

(def-theorem characterization-of-derivative
  "forall(x:ii,f:[ii,uu],v:uu,
     deriv(f,x)=v
      iff 
     forall(eps:rr,
         0<eps
          implies 
         forsome(z_0:ii,
           x<z_0
            and 
           forall(z:ii,
             x<z and z<=z_0
              implies 
             norm((z-x)^[-1]*(f(z)-f(x))-v)<=eps))))"

  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (
    
    (unfold-single-defined-constant (0) deriv)
    (apply-macete-with-minor-premises iota-free-characterization-of-rlim)
    beta-reduce-repeatedly
    )))


(def-theorem existence-of-derivative
   "forall(x:ii,f:[ii,uu],
     #(deriv(f,x))
      iff 
     forsome(v:uu,
       forall(eps:rr,
         0<eps
          implies 
         forsome(z_0:ii,
           x<z_0
            and 
           forall(z:ii,
             x<z and z<=z_0
              implies 
             norm((z-x)^[-1]*(f(z)-f(x))-v)<=eps)))))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "deriv(f,x)=deriv(f,x)")
    (incorporate-antecedent "deriv(f,x)=deriv(f,x)")
    (apply-macete-with-minor-premises characterization-of-derivative)
    direct-inference
    (instantiate-existential ("deriv(f,x)"))
    (cut-with-single-formula "deriv(f,x)=v")
    (apply-macete-with-minor-premises characterization-of-derivative)

    )))

(def-theorem derivative-at-point-bound-lemma
  "forall(x:ii,f:[ii,uu],m:rr,
     norm(deriv(f,x))<=m
      implies 
     forall(m_0:rr,z_0:ii,
       m<m_0 and x<z_0
        implies 
       forsome(z:ii,
         x<z and z<=z_0 and norm(f(z)-f(x))<=m_0*(z-x))))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "deriv(f,x)=deriv(f,x)")
    (incorporate-antecedent "deriv(f,x)=deriv(f,x)")
    (apply-macete-with-minor-premises characterization-of-derivative)
    (force-substitution "(z-x)^[-1]*(f(z)-f(x))-deriv(f,x)" 
			"1/(z-x)*((f(z)-f(x))-(z-x)*deriv(f,x))" (0))
    (apply-macete-with-minor-premises norm-scalar-multiplication)
    (apply-macete-with-minor-premises absolute-value-quotient)
    (force-substitution "abs(1)/abs(z-x)*norm(f(z)-f(x)-(z-x)*deriv(f,x))<=eps" 
			"norm(f(z)-f(x)-(z-x)*deriv(f,x))<=eps*(z-x)" (0))
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,  forall(eps:rr, 0<eps implies p))" 
				      ("m_0-m"))
    simplify
    (cut-with-single-formula "forsome(w:ii,x<w and w<=z_$0 and w<=z_0)")
    (antecedent-inference "with(z_0,z_$0,x:ii,forsome(w:ii,x<w and w<=z_$0 and w<=z_0));")
    (instantiate-existential ("w"))
    (instantiate-universal-antecedent "with(m,m_0:rr,f:[ii,uu],z_$0,x:ii,
  forall(z:ii,
    x<z and z<=z_$0
     implies 
    norm(f(z)-f(x)-(z-x)*deriv(f,x))<=(m_0-m)*(z-x)));" ("w"))
    (cut-with-single-formula 
     "norm(f(w)-f(x))-norm((w-x)*deriv(f,x))<=norm(f(w)-f(x)-(w-x)*deriv(f,x))")
    (cut-with-single-formula "norm((w-x)*deriv(f,x))<=m*(w-x)")
    simplify
    (apply-macete-with-minor-premises norm-scalar-multiplication)
    (apply-macete-with-minor-premises absolute-value-non-negative)
    simplify
    (apply-macete-with-minor-premises norm-continuity-lemma)
    (instantiate-existential ("min(z_0,z_$0)"))
    (unfold-single-defined-constant (0) min)
    (case-split ("z_0<=z_$0"))
    simplify
    simplify
    (apply-macete-with-minor-premises minimum-2nd-arg)
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("z_0" "x"))
    simplify
    (apply-macete-with-minor-premises absolute-value-non-negative)
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    (apply-macete-with-minor-premises ns-fractional-expression-manipulation)
    simplify

    )))
  
(def-transported-symbols ii%locally%lipschitz%bound
  (translation mapint-to-mapint-normed-space)
  (renamer identity))

(def-theorem derivative-bound-lemma
  "forall(f:[ii,uu], m:rr, 
      0<m and forall(x:ii,forsome(y:ii,x<y) implies norm(deriv(f,x))<=m)
          implies
      forall(m_0:rr,m<m_0 implies ii%locally%lipschitz%bound(f,m_0)))"
  
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (
    (unfold-single-defined-constant (0) ii%locally%lipschitz%bound)
    (apply-macete-with-minor-premises derivative-at-point-bound-lemma)
    direct-and-antecedent-inference-strategy
    simplify
    (instantiate-existential ("m"))
    (backchain "with(p:prop,  forall(x:ii,p))")
    (instantiate-existential ("z"))

    )))

(def-theorem mean-value-theorem
  "forall(f:[ii,uu], m:rr, total_q{f,[ii,uu]} and continuous(f)
      and 0<m and forall(x:ii,forsome(y:ii,x<y) implies norm(deriv(f,x))<=m)
        implies
      lipschitz%bound(f,m))"

  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises tr%locally-lipschitz-implies-lipschitz-plus)
    (apply-macete-with-minor-premises derivative-bound-lemma)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("m"))

    )))

(def-theorem constant-function-lipschitz-characterization
  "forall(f:[pp_0,pp_1], total_q{f,[pp_0,pp_1]} and 
     forall(m:rr, 0<m implies lipschitz%bound(f,m)) implies
     forall(x,y:pp_0,f(x)=f(y)))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)
  (proof
   (

    unfold-defined-constants
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (case-split ("0<dist_0(x,y)"))
    (apply-macete-with-minor-premises tr%point-separation-for-distance)
    (case-split ("0<dist_1(f(x),f(y))"))
    (cut-with-single-formula
     "dist_1(f(x),f(y))<=[1/2]*(dist_1(f(x),f(y))/dist_0(x,y))*dist_0(x,y)")
    (cut-with-single-formula
     "[1/2]*(dist_1(f(x),f(y))/dist_0(x,y))*dist_0(x,y)=[1/2]*dist_1(f(x),f(y))")
    (contrapose "with(y,x:pp_0,f:[pp_0,pp_1],0<dist_1(f(x),f(y)));")
    simplify
    simplify
    (backchain "with(p:prop, forall(m:rr, 0<m implies p))")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    simplify-insistently
    simplify-insistently
    (cut-with-single-formula "0<=dist_1(f(x),f(y))")
    simplify
    (apply-macete-with-minor-premises tr%positivity-of-distance)
    (cut-with-single-formula "x=y")
    simplify
    (apply-macete-with-minor-premises tr%point-separation-for-distance)
    (cut-with-single-formula "0<=dist_0(x,y)")
    simplify
    (apply-macete-with-minor-premises tr%positivity-of-distance)

    )))

(def-theorem ms-constant-continuous
  "forall(y:pp_1,x:pp_0, continuous%at%point(lambda(x:pp_0,y),x))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)
  (proof
   (
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("1"))
    simplify
    (apply-macete-with-minor-premises tr%zero-self-distance)
    simplify

    )))

(def-theorem mean-value-theorem-corollary-0
  "forall(f:[ii,uu],
     total_q{f,[ii,uu]}
      and 
     continuous(f)
      and 
     forall(x:ii,forsome(y:ii,x<y) implies deriv(f,x)=v0)
      implies 
     forall(x,y:ii,f(x)=f(y)))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises tr%constant-function-lipschitz-characterization)
    (apply-macete-with-minor-premises mean-value-theorem)
    direct-and-antecedent-inference-strategy
    (backchain "with(f:[ii,uu], forall(x:ii,forsome(y:ii,x<y) implies deriv(f,x)=v0))")
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    simplify

    )))

(def-theorem additivity-of-deriv
  "forall(f,g:[ii,uu],x:ii,
     #(deriv(f,x)) and #(deriv(g,x))
      implies 
     deriv(lambda(x:ii,f(x)+g(x)),x)=deriv(f,x)+deriv(g,x))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (

    
    (unfold-single-defined-constant-globally deriv)
    (force-substitution
     "(z_$0-x)^[-1]*((f(z_$0)+g(z_$0))-(f(x)+g(x)))"
     "lambda(z_$0:ii,(z_$0-x)^[-1]*(f(z_$0)-f(x)))(z_$0)+
      lambda(z_$0:ii,(z_$0-x)^[-1]*(g(z_$0)-g(x)))(z_$0)"
     (0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises rlim-additivity)
    simplify

    )))


(def-theorem deriv-of-constant
  "forall(c:uu,x:ii, forsome(y:ii,x<y) implies deriv(lambda(x:ii,c),x)=v0)"
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (
    (apply-macete-with-minor-premises characterization-of-derivative)
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    simplify
    (instantiate-existential ("y"))

    )))

(def-theorem homogeneity-of-deriv
  "forall(f:[ii,uu],a:rr,x:ii,
     #(deriv(f,x))
      implies 
     deriv(lambda(x:ii,a*f(x)),x)=a*deriv(f,x))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (

    
    (unfold-single-defined-constant-globally deriv)
    (force-substitution "(z_$0-x)^[-1]*(a*f(z_$0)-a*f(x))"
			"a*lambda(z_$0:ii,(z_$0-x)^[-1]*(f(z_$0)-f(x)))(z_$0)"
			(0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises rlim-homogeneity)
    simplify
    )))

(def-theorem ns-sum-of-continuous-is-continuous
  "forall(f,g:[ii,uu], x:ii, 
     continuous%at%point(f,x) and continuous%at%point(g,x) 
      implies 
     continuous%at%point(lambda(x:ii,f(x)+g(x)),x))"

  (proof

   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("eps_$0/2"))
    (simplify-antecedent "with(p:prop, not(p))")
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("eps_$0/2"))
    (simplify-antecedent "with(p:prop, not(p))")
    (cut-with-single-formula "min(delta,delta_$0)<=delta and min(delta,delta_$0)<=delta_$0")
    (instantiate-existential ("min(delta,delta_$0)"))
    unfold-defined-constants
    (case-split ("delta<=delta_$0"))
    simplify
    simplify
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("norm(f(x)-f(y_$1))+norm(g(x)-g(y_$1))"))
    (force-substitution "(f(x)+g(x))-(f(y_$1)+g(y_$1))" "(f(x)-f(y_$1))+(g(x)-g(y_$1))" (0))
    (apply-macete-with-minor-premises norm-triangle-inequality)
    (cut-with-single-formula "norm(g(x)-g(y_$1))<=eps_$0/2")
    simplify
    (backchain "with(eps_$0:rr,g:[ii,uu],delta:rr,x:ii,
  forall(y:ii,
    abs(x-y)<=delta implies norm(g(x)-g(y))<=eps_$0/2));")
    simplify
    (cut-with-single-formula "norm(f(x)-f(y_$1))<=eps_$0/2")
    simplify
    (backchain "with(eps_$0:rr,f:[ii,uu],delta_$0:rr,x:ii,
  forall(y:ii,
    abs(x-y)<=delta_$0 implies norm(f(x)-f(y))<=eps_$0/2));")
    simplify
    simplify
    (cut-with-single-formula "norm(g(x)-g(y_$1))<=eps_$0/2 and norm(f(x)-f(y_$1))<=eps_$0/2")
    simplify
    direct-inference
    direct-and-antecedent-inference-strategy
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises minimum-2nd-arg)

    )
   )
  (usages transportable-macete)
  (theory mappings-from-an-interval-to-a-normed-space))

(comment;; modified proof
 

 unfold-defined-constants
 direct-and-antecedent-inference-strategy
 (instantiate-universal-antecedent "with(g:[ii,uu],x:ii,
  forall(eps:rr,
    0<eps
     implies 
    forsome(delta:rr,
      0<delta
       and 
      forall(y:ii,
        abs(x-y)<=delta implies norm(g(x)-g(y))<=eps))));"
				   ("eps_$0/2"))
 (simplify-antecedent "with(p:prop,not(p));")
 (instantiate-universal-antecedent "with(p:prop,
  forall(eps:rr,0<eps implies forsome(delta:rr,p)));"
				   ("eps_$0/2"))
 (simplify-antecedent "with(p:prop,not(p));")
 (cut-with-single-formula "min(delta,delta_$0)<=delta and min(delta,delta_$0)<=delta_$0")
 (instantiate-existential ("min(delta,delta_$0)"))
 unfold-defined-constants
 (case-split ("delta<=delta_$0"))
 simplify
 simplify
 (apply-macete-with-minor-premises transitivity-of-<=)
 (instantiate-existential ("norm(f(x)-f(y_$1))+norm(g(x)-g(y_$1))"))
 (force-substitution "(f(x)+g(x))-(f(y_$1)+g(y_$1))"
		     "(f(x)-f(y_$1))+(g(x)-g(y_$1))"
		     (0))
 (apply-macete-with-minor-premises norm-triangle-inequality)
 (cut-with-single-formula "norm(g(x)-g(y_$1))<=eps_$0/2")
 (backchain "with(eps_$0:rr,g:[ii,uu],delta:rr,x:ii,
  forall(y:ii,
    abs(x-y)<=delta implies norm(g(x)-g(y))<=eps_$0/2));")
 simplify
 (cut-with-single-formula "norm(f(x)-f(y_$1))<=eps_$0/2")
 (backchain "with(eps_$0:rr,f:[ii,uu],delta_$0:rr,x:ii,
  forall(y:ii,
    abs(x-y)<=delta_$0 implies norm(f(x)-f(y))<=eps_$0/2));")
 simplify
 simplify
 (cut-with-single-formula "norm(g(x)-g(y_$1))<=eps_$0/2 and norm(f(x)-f(y_$1))<=eps_$0/2")
 simplify
 direct-and-antecedent-inference-strategy
 direct-and-antecedent-inference-strategy
 (apply-macete-with-minor-premises minimum-1st-arg)
 (apply-macete-with-minor-premises minimum-2nd-arg)
 )


(def-theorem ns-multiple-of-continuous-is-continuous
  "forall(f:[ii,uu], x:ii, a:rr,
     continuous%at%point(f,x)
      implies 
     continuous%at%point(lambda(x:ii,a*f(x)),x))"

  (proof

   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (case-split ("a=0"))
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("1"))
    (simplify-antecedent "not(0<1);")
    (instantiate-existential ("delta"))
    simplify
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" 
				      ("eps_$0/abs(a)"))
    (contrapose "with(a,eps_$0:rr,not(0<eps_$0/abs(a)));")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (weaken (0 2))
    (unfold-single-defined-constant (0) abs)
    (case-split ("0<=a"))
    simplify
    simplify
    (instantiate-existential ("delta"))
    (force-substitution "a*f(x)-a*f(y_$0)" "a*(f(x)-f(y_$0))" (0))
    (apply-macete-with-minor-premises norm-scalar-multiplication)
    (instantiate-universal-antecedent "with(a,eps_$0:rr,f:[ii,uu],delta:rr,x:ii,
  forall(y:ii,
    abs(x-y)<=delta implies norm(f(x)-f(y))<=eps_$0/abs(a)));" ("y_$0"))
    (incorporate-antecedent "with(a,eps_$0:rr,y_$0,x:ii,f:[ii,uu],
  norm(f(x)-f(y_$0))<=eps_$0/abs(a));")
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (weaken (0 1 3))
    simplify
    (weaken (1 2))
    simplify

    ))

  (usages transportable-macete)
  (theory mappings-from-an-interval-to-a-normed-space))
  

(def-theorem mean-value-theorem-corollary-1
  "forall(f,g:[ii,uu],
     total_q{f,[ii,uu]}
      and 
     total_q{g,[ii,uu]}
      and
     continuous(f)
      and 
     continuous(g)
      and
     forall(x:ii,forsome(y:ii,x<y) implies deriv(f,x)=deriv(g,x))
      and
     forsome(x,y:ii,f(x)=g(x) and x<y)
      implies 
     forall(x:ii,f(x)=g(x)))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forall(x,y:ii,lambda(x:ii,f(x)-g(x))(x)=lambda(x:ii,f(x)-g(x))(y))")
    (incorporate-antecedent "with(g,f:[ii,uu],
  forall(x,y:ii,
    lambda(x:ii,f(x)-g(x))(x)=lambda(x:ii,f(x)-g(x))(y)));")
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(g,f:[ii,uu],forall(x,y:ii,f(x)+g(y)=f(y)+g(x)));" 
				      ("x_$0" "x"))
    (incorporate-antecedent "with(x:ii,g:[ii,uu],x_$0:ii,f:[ii,uu],
  f(x_$0)+g(x)=f(x)+g(x_$0));")
    simplify
    (apply-macete-with-minor-premises mean-value-theorem-corollary-0)
    simplify
    insistent-direct-inference-strategy
    beta-reduce-repeatedly
    simplify
    (force-substitution "[-1]*g(x)" "lambda(x:ii,[-1]*g(x))(x)" (0))
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    (apply-macete-with-minor-premises ns-sum-of-continuous-is-continuous)
    (apply-macete-with-minor-premises ns-multiple-of-continuous-is-continuous)
    (incorporate-antecedent "with(f:[ii,uu],continuous(f));")
    (incorporate-antecedent "with(g:[ii,uu],continuous(g));")
    (apply-macete-with-minor-premises tr%eps-delta-characterization-of-continuity)
    direct-and-antecedent-inference-strategy
    (weaken (7 6 5 3 2 1 0))
    beta-reduce-repeatedly
    (force-substitution "[-1]*g(x)" "lambda(x:ii,[-1]*g(x))(x)" (0))
    (apply-macete-with-minor-premises additivity-of-deriv)
    (apply-macete-with-minor-premises homogeneity-of-deriv)
    simplify
    simplify
    simplify
    simplify
    (weaken (0 1 2 3 4 6 7 8))


    )))


(def-theorem locality-of-derivative
  "forall(f,g:[ii,uu],x:ii, 
     forsome(y:ii, x<y and forall(t:ii, x<=t and t<y implies f(t)=g(t)))
       implies deriv(f,x)==deriv(g,x))"
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (

    direct-and-antecedent-inference-strategy
    insistent-direct-inference-strategy
    (antecedent-inference "with(p,q:prop, p or q)")
    (cut-with-single-formula "forsome(v:uu, deriv(f,x)=v)")
    (antecedent-inference "with(x:ii,f:[ii,uu],forsome(v:uu,deriv(f,x)=v));")
    (backchain "with(v:uu,x:ii,f:[ii,uu],deriv(f,x)=v);")
    (force-substitution "v=deriv(g,x)" "deriv(g,x)=v" (0))
    (incorporate-antecedent "with(v:uu,x:ii,f:[ii,uu],deriv(f,x)=v);")
    (apply-macete-with-minor-premises characterization-of-derivative)
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))")
    (cut-with-single-formula "forsome(z:ii,x<z and z<=z_0 and z<y)")
    (antecedent-inference-strategy (0))
    (instantiate-existential ("z"))
    (backchain-backwards "with(g,f:[ii,uu],y,x:ii,
  forall(t:ii,x<=t and t<y implies f(t)=g(t)));")
    (backchain-backwards "with(g,f:[ii,uu],y,x:ii,
  forall(t:ii,x<=t and t<y implies f(t)=g(t)));")
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify
    (backchain "with(eps:rr,v:uu,f:[ii,uu],z_0,x:ii,
  forall(z:ii,
    x<z and z<=z_0
     implies 
    norm((z-x)^[-1]*(f(z)-f(x))-v)<=eps));")
    simplify
    (cut-with-single-formula "forsome(z:ii,x<z and z<y)")
    (antecedent-inference "with(y,x:ii,forsome(z:ii,x<z and z<y));")
    (instantiate-existential ("min(z,z_0)"))
    (unfold-single-defined-constant (0) min)
    (case-split ("z<=z_0"))
    simplify
    simplify
    (apply-macete-with-minor-premises minimum-2nd-arg)
    (cut-with-single-formula "min(z,z_0)<=z")
    simplify
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("z_0" "x"))
    simplify
    (instantiate-existential ("(x+y)/2"))
    simplify
    simplify
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("y" "x"))
    simplify
    simplify
    simplify
    (instantiate-existential ("deriv(f,x)"))
    (cut-with-single-formula "forall(f,g:[ii,uu], #(deriv(f,x)) and forall(t:ii,x<=t and t<y implies f(t)=g(t)) and x<y implies deriv(f,x)=deriv(g,x) )")
    (force-substitution "deriv(f,x)=deriv(g,x)" "deriv(g,x)=deriv(f,x)" (0))
    (backchain "with(y,x:ii,
  forall(f,g:[ii,uu],
    #(deriv(f,x))
     and 
    forall(t:ii,x<=t and t<y implies f(t)=g(t))
     and 
    x<y
     implies 
    deriv(f,x)=deriv(g,x)));")
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(g,f:[ii,uu],y,x:ii,
  forall(t:ii,x<=t and t<y implies f(t)=g(t)));" ("t"))
    simplify
    (weaken (1 2 0))
    direct-and-antecedent-inference-strategy

    )))

(def-theorem derivative-of-a-linear-map
  "forall(a,b:uu,x:ii,
    forsome(y:ii,x<y) implies deriv(lambda(t:ii,t*a+b),x)=a)"
  (theory mappings-from-an-interval-to-a-normed-space)
  (proof
   (

    (force-substitution "t*a+b" "lambda(t:ii,t*a)(t)+lambda(t:ii,b)(t)" (0))
    (apply-macete-with-minor-premises additivity-of-deriv)
    (apply-macete-with-minor-premises deriv-of-constant)
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises characterization-of-derivative)
    beta-reduce-repeatedly
    (force-substitution "(z*a-x*a)" "(z-x)*a" (0))
    simplify
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    simplify
    (apply-macete-with-minor-premises deriv-of-constant)
    simplify
    simplify

    )))
