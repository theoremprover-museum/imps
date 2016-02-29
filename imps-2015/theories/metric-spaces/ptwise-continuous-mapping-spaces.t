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


(herald ptwise-continuous-mapping-spaces)

(include-files
 (files (imps theories/metric-spaces/continuous-mapping-spaces)))


(def-theorem ptwise-continuity-is-closed-under-uniform-limits
  "forall(s:[zz,ms%bfun], x:pp_0, forsome(m:zz, forall(n:zz, m<=n implies
              continuous%at%point(s(n),x))) and #(lim(s)) implies continuous%at%point(lim(s),x))"

  (proof

   (

    (unfold-single-defined-constant (0 1) continuous%at%point)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lim(s)=lim(s)")
    (incorporate-antecedent "with(s:[zz,ms%bfun],lim(s)=lim(s));")
    (apply-macete-with-minor-premises tr%characterization-of-limit)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr,  0<eps implies p))" ("eps/3"))
    (simplify-antecedent "with(p:prop, not(p))")
    (instantiate-universal-antecedent "with(eps:rr,s:[zz,ms%bfun],n_$0:zz,
  forall(p_$0:zz,
    n_$0<=p_$0 implies dist(lim(s),s(p_$0))<=eps/3));" ("max(n_$0,m)"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises maximum-1st-arg)
    (instantiate-universal-antecedent "with(m:zz, p:prop,  forall(n:zz,  m<=n implies p))" ("max(n_$0,m)"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (beta-reduce-antecedent "with(f:[ms%bfun,pp_0,prop], a:ms%bfun,x:pp_0, f(a,x))")
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr,  0<eps implies p))" ("eps/3"))
    (simplify-antecedent "with(p:prop, not(p))")
    (instantiate-existential ("delta_$0"))
    (instantiate-universal-antecedent "with(p:prop, forall(y:pp_0, p))" ("y"))

    ;;3-epsilon argument:

    (cut-with-single-formula "dist_1(lim(s)(x),lim(s)(y))<=dist_1(lim(s)(x),s(max(n_$0,m))(x))
+dist_1(s(max(n_$0,m))(x),s(max(n_$0,m))(y))+dist_1(lim(s)(y),s(max(n_$0,m))(y)) and forall(x:
pp_0, dist_1(lim(s)(x),s(max(n_$0,m))(x))<=dist(lim(s),s(max(n_$0,m))))")
    (antecedent-inference "with(p,q:prop, p and q)")
    (instantiate-universal-antecedent-multiply 
     "with(p:prop,forall(x:pp_0,p));"
     (("x") ("y")))
    simplify

    direct-and-antecedent-inference-strategy
    (weaken (1 2 4 5))
    (cut-with-single-formula "total_q{dist_1,[pp_1,pp_1,rr]} and forall(x,y,z,u:pp_1, dist_1(x,u)
<=dist_1(x,y)+dist_1(y,z)+dist_1(u,z))")
    (backchain "with(q,p:prop,q and p)")
    (weaken (0 2))
    (apply-macete-with-minor-premises tr%bfun-values-defined-lemma)
    (weaken (0 2))
    (weaken (0 1))
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

    )

   )
  (theory pointed-ms-2-tuples))

(def-theorem continuity-is-closed-under-uniform-limits
  "forall(s:[zz,ms%bfun],x:pp_0,
     forsome(m:zz,
       forall(n:zz,
         m<=n
          implies 
         total_q{s(n),[pp_0,pp_1]} and continuous(s(n))))
      and 
     #(lim(s))
      implies 
     continuous(lim(s)))"
  (usages transportable-macete)
  (theory pointed-ms-2-tuples)
  (proof

   (
    
    (apply-macete-with-minor-premises eps-delta-characterization-of-continuity)
    (apply-macete-with-minor-premises ptwise-continuity-is-closed-under-uniform-limits)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("m"))
    (backchain "with(p:prop, m:zz, forall(n:zz, m<=n implies p))")
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises tr%bfun-values-defined-lemma)


    )

   ))

(def-theorem ()
  "lambda(s:ms%bfun, continuous(s))(lambda(x:pp_0,a_0))"

  (proof

   (

    (apply-macete-with-minor-premises eps-delta-characterization-of-continuity)
    (unfold-single-defined-constant (0) continuous%at%point)
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
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises tr%bfun-values-defined-lemma)


    )

   )


  (theory pointed-ms-2-tuples))






(def-atomic-sort continuous%bfun
  "lambda(s:ms%bfun, continuous(s))"
  (theory pointed-ms-2-tuples)
  (witness "lambda(x:pp_0,a_0)"))


(include-files
 (files (imps theories/metric-spaces/subspaces)))


;;Now view the sort continuous%bfun as a metric space in its own right.
;;Again, we prefer to do this by making it an instance of the metric-space ensemble.

(def-theorem metric-spaces-to-pointed-ms-2-tuples_1
  "forall(x,y,z:continuous%bfun, 
     ms%bfun%dist(x,z) <= ms%bfun%dist(y,z) + ms%bfun%dist(x,y))"
  (theory pointed-ms-2-tuples)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-transported-theorem 
      triangle-inequality-for-distance
      metric-spaces-to-pointed-ms-2-tuples ("x" "y" "z"))
    simplify
    )))

(def-theory-ensemble-instances
  metric-spaces 
  (target-theories pointed-ms-2-tuples)
  (multiples 1)
  (theory-interpretation-check using-simplification)
  (sorts (pp continuous%bfun))
  (constants (dist "lambda(f,g: continuous%bfun, ms%bfun%dist(f,g))"))
  (special-renamings 
   (ball cbfun%ball)
   (open%ball cbfun%open%ball)
   (lipschitz%bound cbfun%lipschitz%bound)
   (lipschitz%bound%on cbfun%lipschitz%bound%on)
   (complete cbfun%complete)
   (cauchy cbfun%cauchy)
   (lim cbfun%lim)))

(def-translation subspaces-to-function-subspace
  (source ms-subspace)
  (target pointed-ms-2-tuples)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (aa continuous%bfun) (pp ms%bfun))
  (constant-pairs (dist ms%bfun%dist))
  (theory-interpretation-check using-simplification))

;;;We now prove completeness in case pp_1 is complete:

(def-theorem continuous%bfun%complete
  "complete_1 implies cbfun%complete"
  (theory pointed-ms-2-tuples)
  (proof
   (
    (apply-macete-with-minor-premises tr%rev%completeness-extends)
    (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
      direct-and-antecedent-inference-strategy
      (apply-macete-with-minor-premises
       continuous%bfun-defining-axiom_pointed-ms-2-tuples)
      beta-reduce-repeatedly
      (apply-macete-with-minor-premises continuity-is-closed-under-uniform-limits)
      direct-and-antecedent-inference-strategy
      (incorporate-antecedent "with(f:ms%bfun,#(f));")
      (apply-macete-with-minor-premises tr%existence-of-limit)
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(eps_$0:rr,p));" ("1"))
      (simplify-antecedent "with(p:prop,not(p));")
      (block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
	(instantiate-existential ("n_$0"))
	(block 
	    (script-comment "`instantiate-existential' at (0 0 0 0)")
	  insistent-direct-inference-strategy
	  (cut-with-single-formula "forsome(f:ms%bfun,f=s(n))")
	  (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	    (antecedent-inference "with(p:prop,forsome(f:ms%bfun,p));")
	    (backchain-backwards "with(f:ms%bfun,f)=with(f:continuous%bfun,f);")
	    (apply-macete-with-minor-premises tr%bfun-values-defined-lemma))
	  (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	    (instantiate-existential ("s(n)"))
	    (instantiate-universal-antecedent "with(p:prop,forall(p_$0:zz,p));" ("n"))
	    (instantiate-universal-antecedent "with(p:prop,forall(p_$0:zz,p));"
					      ("n"))))
	(apply-macete-with-minor-premises
	 continuous%bfun-in-quasi-sort_pointed-ms-2-tuples)))
    (apply-macete-with-minor-premises tr%bfun-completeness)
    )))


