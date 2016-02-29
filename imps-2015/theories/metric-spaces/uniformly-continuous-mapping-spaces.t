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


(herald uniformly-continuous-mapping-spaces)

(include-files
 (files (imps theories/metric-spaces/continuous-mapping-spaces)))


(def-theorem uniform-continuity-is-closed-under-uniform-limits
  "forall(s:[zz,ms%bfun],x:pp_0,
     forsome(m:zz,
       forall(n:zz,
         m<=n
          implies 
          uniformly%continuous(s(n))))
      and 
     #(lim(s))
      implies 
     uniformly%continuous(lim(s)))"
  (usages transportable-macete)
  (theory pointed-ms-2-tuples)
  (proof

   (
    
    ;;This is very similar to the proof of the similar assertion for ptwise limits:

    (force-substitution "uniformly%continuous(s(n))" "total_q{s(n),[pp_0,pp_1]} and uniformly%continuous(s(n))" (0))

    (unfold-single-defined-constant (0 1) uniformly%continuous)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lim(s)=lim(s)")
    (incorporate-antecedent "with(s:[zz,ms%bfun],lim(s)=lim(s));")
    (apply-macete-with-minor-premises tr%characterization-of-limit)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr,0<eps implies p))" ("eps/3"))
    (simplify-antecedent "with(p:prop, not(p))")
    (instantiate-universal-antecedent "with(eps:rr,s:[zz,ms%bfun],n_$0:zz,
  forall(p_$0:zz,
    n_$0<=p_$0 implies dist(lim(s),s(p_$0))<=eps/3));" ("max(n_$0,m)"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises maximum-1st-arg)
    (instantiate-universal-antecedent "with(m:zz, p:prop,  forall(n:zz,  m<=n implies p))" ("max(n_$0,m)"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr,  0<eps implies p))" ("eps/3"))
    (simplify-antecedent "with(p:prop, not(p))")
    (instantiate-existential ("delta_$0"))
    (instantiate-universal-antecedent "with(p:prop, forall(x,y:pp_0, p))" ("x" "y"))
    (contrapose "with(x:pp_0,m,n_$0:zz,s:[zz,ms%bfun],
  not(#(s(max(n_$0,m))(x))));")
    (contrapose "with(y:pp_0,m,n_$0:zz,s:[zz,ms%bfun],
  not(#(s(max(n_$0,m))(y))));")
    (cut-with-single-formula "dist_1(lim(s)(x),lim(s)(y))<=dist_1(lim(s)(x),s(max(n_$0,m))(x))
+dist_1(s(max(n_$0,m))(x),s(max(n_$0,m))(y))+dist_1(lim(s)(y),s(max(n_$0,m))(y)) and forall(x:
pp_0, dist_1(lim(s)(x),s(max(n_$0,m))(x))<=dist(lim(s),s(max(n_$0,m))))")
    (antecedent-inference "with(p,q:prop, p and q)")
    (instantiate-universal-antecedent-multiply 
     "with(r:rr,forall(x:pp_0,r<=r));"
     (("x") ("y")))
    simplify
    direct-and-antecedent-inference-strategy
    (weaken (0 2 4 6))
    (cut-with-single-formula "total_q{dist_1,[pp_1,pp_1,rr]} and forall(x,y,z,u:pp_1, dist_1(x,u)
<=dist_1(x,y)+dist_1(y,z)+dist_1(u,z))")
    (backchain "with(q,p:prop,q and p)")
    (weaken (0 1 2))
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (cut-with-single-formula "0<=dist_1(x_0,x_1)")
    (apply-macete-with-minor-premises tr%positivity-of-distance)
    (apply-macete-with-minor-premises tr%triangle-inequality-alternate-form)
    (instantiate-existential ("y"))
    simplify
    (apply-macete-with-minor-premises tr%triangle-inequality-alternate-form)
    (instantiate-existential ("z"))
    simplify
    (apply-macete-locally tr%symmetry-of-distance (0) " dist_1(z,u) ")
    simplify
    (apply-macete-with-minor-premises tr%bounded-bfun%dist)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (apply-macete-with-minor-premises tr%bfun-values-defined-lemma)

    )

   ))

(def-theorem ()
  "lambda(s:ms%bfun, uniformly%continuous(s))(lambda(x:pp_0,a_0))"
  (proof

   (

    (unfold-single-defined-constant (0) uniformly%continuous)
    beta-reduce-with-minor-premises
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%zero-self-distance)
    simplify
    (instantiate-existential ("1"))
    simplify
    (apply-macete-with-minor-premises ms%bfun-defining-axiom_pointed-ms-2-tuples)
    insistent-direct-inference-strategy
    simplify

    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    (instantiate-existential ("x_$0"))
    simplify-insistently
    (apply-macete-with-minor-premises tr%zero-self-distance)
    (instantiate-existential ("0"))
    (unfold-single-defined-constant (0) majorizes)
    simplify-insistently
    (apply-macete-with-minor-premises tr%zero-self-distance)
    simplify



    )

   )


  (theory pointed-ms-2-tuples))

(def-atomic-sort unif%continuous%bfun
  "lambda(s:ms%bfun, uniformly%continuous(s))"
  (theory pointed-ms-2-tuples)
  (witness "lambda(x:pp_0,a_0)"))


(include-files
 (files (imps theories/metric-spaces/subspaces)))


;;Now view the sort unif%continuous%bfun as a metric space in its own right.
;;Again, we prefer to do this by making it an instance of the metric-space ensemble.
(def-theorem ()
  "forall(x,y,z:unif%continuous%bfun, dist(x,z)<=dist(y,z)+dist(x,y))"
  (theory pointed-ms-2-tuples)
  (proof
   (


    (apply-macete-with-minor-premises commutative-law-for-addition)
    (apply-macete-with-minor-premises tr%triangle-inequality-for-distance)
    )))

(def-theory-ensemble-instances
  metric-spaces 
  force-under-quick-load
  (target-theories pointed-ms-2-tuples)
  (multiples 1)
  (theory-interpretation-check using-simplification)
  (sorts (pp unif%continuous%bfun))
  (constants (dist "lambda(f,g: unif%continuous%bfun, ms%bfun%dist(f,g))"))
  (special-renamings 
   (ball ucbfun%ball)
   (open%ball ucbfun%open%ball)
   (lipschitz%bound ucbfun%lipschitz%bound)
   (lipschitz%bound%on ucbfun%lipschitz%bound%on)
   (complete ucbfun%complete)
   (cauchy ucbfun%cauchy)
   (lim ucbfun%lim)))

(def-translation subspaces-to-uc-function-subspace
  force-under-quick-load
  (source ms-subspace)
  (target pointed-ms-2-tuples)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (aa unif%continuous%bfun) (pp ms%bfun))
  (constant-pairs (dist ms%bfun%dist))
  (theory-interpretation-check using-simplification))


;;; We now prove completeness of the space of bounded continuous functions in the
;;; case pp_1 is complete:

(def-theorem uniformly%continuous%bfun%complete
  "complete_1 implies ucbfun%complete"
  
  (proof
   (

    (apply-macete-with-minor-premises tr%rev%completeness-extends)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%limit-definedness-extends)
    (apply-macete-with-minor-premises unif%continuous%bfun-defining-axiom_pointed-ms-2-tuples)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises tr%rev%limit-definedness-extends)
    (apply-macete-with-minor-premises uniform-continuity-is-closed-under-uniform-limits)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(t:unif%continuous%bfun,#(t))")
    (apply-macete-with-minor-premises tr%existence-of-limit)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("1"))
    (simplify-antecedent "with(p:prop,not(p))")
    (instantiate-existential ("n_$0"))
    insistent-direct-inference-strategy
    (cut-with-single-formula "forsome(f:ms%bfun,f=s(n))")
    (antecedent-inference "with(p:prop, forsome(f:ms%bfun,p))")
    (backchain-backwards "with(f,g: ms%bfun, f=g)")
    (apply-macete-with-minor-premises unif%continuous%bfun-in-quasi-sort_pointed-ms-2-tuples)
    (instantiate-existential ("s(n)"))
    (instantiate-universal-antecedent "with(p:prop, forall(n:zz,p))" ("n"))
    (instantiate-universal-antecedent "with(p:prop, forall(n:zz,p))" ("n"))
    (apply-macete-with-minor-premises tr%limit-definedness-extends)
    (apply-macete-with-minor-premises tr%bfun-completeness)

    ))
  (usages transportable-macete)
  (theory pointed-ms-2-tuples))



