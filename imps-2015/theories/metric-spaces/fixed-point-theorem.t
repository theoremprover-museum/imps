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


(herald fixed-point-theorem)

(load-section foundation)


(include-files
 (files (imps theories/generic-theories/iterate)))

(comment
 (def-recursive-constant iterate
   "lambda(iter:[zz,ind_1], f:[ind_1,ind_1],x:ind_1,
     lambda(n:zz, if(n=0,x,f(iter(n-1)))))"
   (theory generic-theory-1)
   (definition-name iterate))

 (def-theorem iterate-definedness
   "forall(f:[ind_1,ind_1],x:ind_1,z:zz, 
     total_q{f,[ind_1,ind_1]} and 0<=z implies #(iterate(f,x)(z)))"
   (theory generic-theory-1)
   (usages transportable-macete)
   (proof 

    (
     (induction integer-inductor ())

     )))

 (def-theorem undefined-for-negative
   "forall(n:zz,x:ind_1,f:[ind_1,ind_1],n<0 implies not(#(iterate(f,x)(n))))"
   (theory generic-theory-1)
   (usages transportable-macete)

   (proof

    (

     (instantiate-theorem iterate-minimality_generic-theory-1 ("f" "x"))
     (instantiate-universal-antecedent "with(f:[ind_1,ind_1],x:ind_1,
  forall(h_0:[zz,ind_1],
    h_0=lambda(n:zz,if(n=0, x, f(h_0(n-1))))
     implies 
    forall(u_0:zz,
      #(iterate(f,x)(u_0))
       implies 
      iterate(f,x)(u_0)=h_0(u_0))));" ("lambda(n:zz,if(n<0,?ind_1,iterate(f,x)(n)))"))
     (contrapose "with(p:prop, not(p))")
     extensionality
     direct-inference
     (unfold-single-defined-constant (0) iterate)
     (case-split ("x_0<0"))
     simplify
     simplify
     direct-inference
     (backchain "with(p:prop, t:ind_1,  forall(u:zz, #(t) implies p))")
     simplify


     )))


 (def-theorem iterate-translate
   "forall(n:zz,x:ind_1,f:[ind_1,ind_1],
     f oo (iterate(f,x))=lambda(n:zz,if(n=[-1],?ind_1,iterate(f,x)(n+1))))"
   (theory generic-theory-1)
   (usages transportable-macete)

   (proof


    (

    
     direct-inference
     (unfold-single-defined-constant (1) iterate)
     extensionality
     direct-inference
     simplify-insistently
     (instantiate-theorem undefined-for-negative ("x_0" "x" "f"))
     simplify
     simplify

     ))

   )

 (def-theorem iterate-totality
   "total_q{iterate,[[ind_1,ind_1],ind_1,[zz,ind_1]]}"
   (theory generic-theory-1)
   (usages d-r-convergence transportable-macete)

   (proof 

    (

     insistent-direct-inference
     (unfold-single-defined-constant (0) iterate)


     )))
 )

; Iteration of Functions satisfying Lipschitz%bound

(include-files
 (files (imps theories/metric-spaces/metric-spaces)
	(imps theories/metric-spaces/metric-space-pairs)))


(def-translation ind_1->pp
  force-under-quick-load
  (source generic-theory-1)
  (target metric-spaces)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 "pp")))

; The recursively defined constant "iterate" is transported to the
; theory metric-spaces. Eventually, we want to include generic-theory-1 and 
; metric-spaces in the same theory, so that it is advisable to use a different
; name for it.

(def-renamer iterate-renamer
  (pairs (iterate ms%iterate)))

(def-transported-symbols iterate
  (renamer iterate-renamer)
  (translation ind_1->pp))

(def-overloading iterate
  (generic-theory-1 iterate) (metric-spaces ms%iterate))

; The theorem "iterate-totality" is also transported to metric-spaces.

(def-theorem ()
  iterate-totality
  ;; "total_q{iterate,[[pp,pp],pp,[zz,pp]]}"
  (theory metric-spaces)
  (translation ind_1->pp)
  (usages d-r-convergence)
  (proof existing-theorem))

; We need to consider the theory of metric spaces as an instance of a
; theory of metric space pairs so we can use constants naturally
; defined in that theory such as "continuous" and "lipschitz%bound."

;;(set (current-theory) (name->theory 'metric-spaces))

(ensemble-dont-translate-constant metric-spaces "ms%iterate")

;;(dont-translate-constant ms-ensemble (qr "ms%iterate"))

(include-files
 (files (imps theories/metric-spaces/metric-space-self-mappings)))


;;;(def-theory-ensemble-instances
;;;  metric-spaces
;;;  force-under-quick-load
;;;  (permutations (0 1))
;;;  (sorts (pp pp pp))
;;;  (constants (dist dist dist))
;;;  (target-theories metric-spaces metric-spaces))
;;;
;;;(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-theorem iterated-distance-bound
  "forall(f:[pp,pp],x:pp,p:zz,r:rr, 
     lipschitz%bound(f,r) and  0<=p 
      implies 
     dist(iterate(f,x)(p),iterate(f,x)(p+1))<=r^p*dist(x,f(x)))"
  (theory metric-spaces)

  
  (proof

   (

    (unfold-single-defined-constant (0) lipschitz%bound)
    (unfold-single-defined-constant (0) lipschitz%bound%on)
    direct-and-antecedent-inference-strategy
    (induction integer-inductor ("p"))
    (unfold-single-defined-constant (1) ms%iterate)
    simplify
    (instantiate-universal-antecedent "with(r:rr,f:[pp,pp],
  forall(x_$0,y_$0:pp,
    x_$0 in sort_to_indic{pp} and y_$0 in sort_to_indic{pp}
     implies 
    dist(f(x_$0),f(y_$0))<=r*dist(x_$0,y_$0)));" ("iterate(f,x)(t)" "iterate(f,x)(1+t)"))
    (simplify-antecedent "with(p:prop, not(p))")
    (simplify-antecedent "with(p:prop, not(p))")
    (apply-macete-with-minor-premises transitivity-of-<=)
    auto-instantiate-existential
    (apply-macete-with-minor-premises transitivity-of-<=)
    direct-inference
    (instantiate-existential ("dist(x,f(x))*r^t*r"))
    simplify
    simplify



    )))


(include-files
 (files (imps theories/metric-spaces/criteria-for-convergence)
	(imps theories/metric-spaces/metric-space-pairs-supplements)))


(def-theorem iterate-sequence-converges
  "complete implies forall(f:[pp,pp],x:pp ,r:rr,
     lipschitz%bound(f,r) and r<1 
      implies 
     #(lim(iterate(f,x))))"
  (theory metric-spaces)

  (proof

   (

    (apply-macete-with-minor-premises convergence-test-for-complete-spaces)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("lambda(j:zz,r^j*dist(x,f(x)))" "0"))
    (apply-macete-with-minor-premises geometric-series-is-summable%nonnegative)
    (cut-with-single-formula "total_q{f,[pp,pp]} and 0<r")
    simplify
    (apply-macete-with-minor-premises tr%lipschitz-bound-is-total)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("r"))
    (incorporate-antecedent "with(r:rr,f:[pp,pp],lipschitz%bound(f,r));")
    (unfold-single-defined-constant (0) lipschitz%bound)
    (unfold-single-defined-constant (0) lipschitz%bound%on)
    simplify
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises iterated-distance-bound)
    simplify

    ))
  )


(def-theorem contractive-mapping-fixed-point-theorem
  "forall(f:[pp,pp],r:rr, 
     complete and lipschitz%bound(f,r) and r<1 
      implies 
     forsome(x:pp,f(x)=x))"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof

   (


    direct-and-antecedent-inference-strategy
    (instantiate-existential ("lim(iterate(f,x))"))
    (apply-macete-with-minor-premises tr%rev%lim-preservation)
    (apply-macete-with-minor-premises tr%iterate-translate)
    (force-substitution 
     "lambda(n:zz,if(n=[-1], ?pp, iterate(f,x)(n+1)))" 
     "lambda(m:zz, lambda(n:zz,if(n=0, ?pp, iterate(f,x)(n)))(1*m+1))" (0))
    (apply-macete-with-minor-premises limit-translation-invariance)
    (apply-macete-with-minor-premises limit-depends-on-tail)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("1"))
    simplify
    (apply-macete-with-minor-premises tr%iterate-definedness)
    simplify
    (apply-macete-with-minor-premises tr%lipschitz-bound-is-total)
    (instantiate-existential ("r"))
    (weaken (0))
    (apply-macete-with-minor-premises iterate-sequence-converges)
    (instantiate-existential ("r"))
    (force-substitution "lim(lambda(n:zz,if(n=0, ?pp, iterate(f,x)(n))))" "lim(iterate(f,x))" (0))
    simplify
    (apply-macete-with-minor-premises tr%lipschitz-bound-is-continuous)
    (instantiate-existential ("r"))


    )

   ))

(include-files
 (files (imps theories/metric-spaces/subspaces)))


(def-language language-for-ms-closed-ball
  (embedded-languages metric-spaces-language)
  (constants 
   (a pp)
   (r rr)))
      
(def-theory ms-closed-ball
  (component-theories metric-spaces)
  (language language-for-ms-closed-ball)
  (axioms
   (positivity-of-r "0<=r")))

(def-theorem ()
  "nonempty_indic_q{ball(a,r)}"

  (proof

   (

    (instantiate-existential ("a"))
    (apply-macete-with-minor-premises ball-membership-condition)
    simplify

    ))
  (theory ms-closed-ball))

(def-atomic-sort bb
  "lambda(x:pp, x in ball(a,r))"
  (theory ms-closed-ball))

(def-theorem bb-sort-characterization
  "forall(x:bb, dist(a,x)<=r)"


  (proof

   (

    direct-inference
    (instantiate-theorem bb-defining-axiom_ms-closed-ball ("x"))
    (contrapose "with(x:bb,x in ball(a,r));")
    (apply-macete-with-minor-premises ball-membership-condition)
    (contrapose "with(x:bb,not(#(x,bb)));")

    ))
  (usages rewrite)
  (theory ms-closed-ball))

(def-translation ms-subspace-to-ms-closed-ball
  force-under-quick-load
  (source ms-subspace)
  (target ms-closed-ball)
  (sort-pairs (aa bb))
  (fixed-theories h-o-real-arithmetic)
  (theory-interpretation-check using-simplification))

(def-transported-symbols
  (sub%ball
   sub%open%ball
   sub%lipschitz%bound
   sub%lipschitz%bound%on
   sub%complete
   sub%cauchy
   sub%lim)
  (translation  ms-subspace-to-ms-closed-ball))


(def-theorem () 
  "forall(x,y,z:bb,dist(x,z)<=dist(y,z)+dist(x,y))" 
  lemma
  (theory ms-closed-ball)
  (proof

   (
    (apply-macete-with-minor-premises commutative-law-for-addition)
    (apply-macete-with-minor-premises triangle-inequality-for-distance)
    )))

(def-translation ms-to-ms-closed-ball
  force-under-quick-load
  (source metric-spaces)
  (target ms-closed-ball)
  (sort-pairs (pp bb))
  (constant-pairs (dist "lambda(x,y:bb, dist(x,y))"))
  (fixed-theories h-o-real-arithmetic)
  (theory-interpretation-check using-simplification))

(def-theorem invariance-of-ball
  "forall(f:[pp,pp],c:rr,x:pp,
     lipschitz%bound%on(f,c,ball(a,r))
      and 
     dist(a,f(a))<r*(1-c)
      and 
     x in ball(a,r)
      implies 
     f(x) in ball(a,r))"
  (theory ms-closed-ball)
  (proof
   (

    (unfold-single-defined-constant (0) lipschitz%bound%on)
    beta-reduce-with-minor-premises
    (apply-macete-with-minor-premises ball-membership-condition)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,  forall(x,y:pp, p))" ("a" "x"))
    (simplify-antecedent "with(p:prop, not(p))")
    (cut-with-single-formula "dist(a,x)*c<=r*c")
    (apply-macete-with-minor-premises triangle-inequality-alternate-form)
    (instantiate-existential ("f(a)"))
    simplify
    simplify
    (unfold-single-defined-constant (0) ball)

    )

   ))  


(def-theorem lipschitz%bound%on-extends
  "forall(f:[pp,pp],c:rr, 
     lipschitz%bound%on(f,c,ball(a,r)) and dist(a,f(a))<r*(1-c) 
      implies
     sub%lipschitz%bound(restrict{f,ball(a,r)},c))"
  (theory ms-closed-ball)
  (proof
   (

    (unfold-single-defined-constant (0) sub%lipschitz%bound)
    (unfold-single-defined-constant (0) lipschitz%bound%on)
    (unfold-single-defined-constant (0) sub%lipschitz%bound%on)
    beta-reduce-with-minor-premises
    (apply-macete-with-minor-premises ball-membership-condition)
    direct-and-antecedent-inference-strategy
    simplify-insistently
    (apply-macete-with-minor-premises ball-membership-condition)
    simplify
    (instantiate-universal-antecedent "with(p:prop, forall(x,y:pp,p))" ("x_$2" "y_$1"))
    (simplify-antecedent "with(x_$1:bb,not(dist(a,x_$1)<=r));")
    (simplify-antecedent "with(y_$1:bb,not(dist(a,y_$1)<=r));")
    simplify
    (unfold-single-defined-constant (0) ball)
    sort-definedness
    simplify-insistently
    (apply-macete-with-minor-premises bb-defining-axiom_ms-closed-ball)
    (apply-macete-with-minor-premises invariance-of-ball)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("c"))
    (unfold-single-defined-constant (0) lipschitz%bound%on)

    )))



;; We prove this theorem in the special theory ms-closed-ball, although we
;; are only interested in it in the theory metric-spaces.

(def-theorem restricted-fixed-point-theorem
  "forall(f:[pp,pp],c:rr, 
     complete and lipschitz%bound%on(f,c,ball(a,r)) and c<1 and dist(a,f(a))<r*(1-c) 
      implies
     forsome(x:bb, f(x)=x))"

  (proof

   (

    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x:bb,restrict{f,ball(a,r)}(x)=x)")
    (block 
     (script-comment "node added by `cut-with-single-formula' at (0)")
     (instantiate-existential ("with(x:bb,x)"))
     (incorporate-antecedent "with(x:bb,p:pp,p=x);")
     simplify-insistently
     (apply-macete-with-minor-premises ball-membership-condition)
     simplify)
    (block 
     (script-comment "node added by `cut-with-single-formula' at (1)")
     (cut-with-single-formula "forsome(h:[bb,bb],restrict{f,ball(a,r)}=h)")
     (block 
      (script-comment "node added by `cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(h:[bb,bb],p));")
      (backchain "with(h:[bb,bb],f:[pp,pp],f=h);")
      (apply-macete-with-minor-premises tr%contractive-mapping-fixed-point-theorem)
      (instantiate-existential ("c"))
      (block 
       (script-comment "node added by `instantiate-existential' at (0 0)")
       (apply-macete-with-minor-premises tr%rev%completeness-extends)
       direct-and-antecedent-inference-strategy
       (apply-macete-with-minor-premises bb-defining-axiom_ms-closed-ball)
       (apply-macete-with-minor-premises closed-balls-are-closed)
       direct-inference
       simplify-insistently
       direct-and-antecedent-inference-strategy
       (backchain "with(b:bb,x_$0:pp,x_$0=b);")
       (apply-macete-with-minor-premises ball-membership-condition)
       simplify)
      (block 
       (script-comment "node added by `instantiate-existential' at (0 1)")
       (backchain-backwards "with(h:[bb,bb],f:[pp,pp],f=h);")
       (apply-macete-with-minor-premises lipschitz%bound%on-extends)
       direct-and-antecedent-inference-strategy))
     (block 
      (script-comment "node added by `cut-with-single-formula' at (1)")
      (instantiate-existential ("restrict{f,ball(a,r)}"))
      sort-definedness
      (apply-macete-with-minor-premises bb-defining-axiom_ms-closed-ball)
      direct-and-antecedent-inference-strategy
      (block 
       (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
       (incorporate-antecedent "with(p:pp,#(p));")
       simplify-insistently)
      (block 
       (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 1)")
       (force-substitution "restrict{f,ball(a,r)}(xx_0)"
			   "f(xx_0)"
			   (0))
       (block 
	(script-comment "node added by `force-substitution' at (0)")
	(apply-macete-with-minor-premises invariance-of-ball)
	(instantiate-existential ("c")))
       simplify)))

    )

   )



  (home-theory ms-closed-ball)
  (theory metric-spaces)
  (usages transportable-macete))

