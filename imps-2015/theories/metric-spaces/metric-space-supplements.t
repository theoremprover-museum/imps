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


(herald metric-space-supplements)

(include-files
 (files (imps theories/metric-spaces/metric-spaces)))


;;; Basic lemmas

(def-theorem ()
  "forall(x,y:pp,#(dist(x,y)))"
  (theory metric-spaces)
  (usages d-r-convergence transportable-macete)
  (proof (insistent-direct-inference-strategy
	  (instantiate-theorem positivity-of-distance ("x" "y")))))

(def-theorem ()
 "forall(x,y:pp,dist(x,y)<=dist(y,x))"
 (theory metric-spaces)
 (proof ((instantiate-theorem symmetry-of-distance ("x" "y"))
	 simplify)))

(def-theorem ()
 "forall(x:pp,dist(x,x)<=0)"
 (theory metric-spaces)
 (proof ((instantiate-theorem point-separation-for-distance ("x" "x"))
	 simplify)))

(def-theorem triangle-inequality-alternate-form
  "forall(x,y,z:pp,r:rr, dist(x,z)+dist(z,y)<=r implies dist(x,y)<=r)"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof (direct-inference-strategy
	  (cut-with-single-formula "dist(x,y)<=dist(x,z)+dist(z,y)")
	   simplify
	   (apply-macete-with-minor-premises triangle-inequality-for-distance)
	   )))

(def-theorem zero-self-distance
  "forall(x,y:pp,dist(x,x)=0)"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof

   (

    direct-inference
    (instantiate-theorem point-separation-for-distance ("x" "x"))


    )


   ))

(def-theorem metric-separation
  "forall(x,y:pp,x=y 
   iff
 forall(r:rr,0<r implies forsome(z:pp,
dist(z,x)<=r and dist(z,y)<=r)))"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x"))
    simplify
    simplify
    (apply-macete-with-minor-premises point-separation-for-distance)
    (instantiate-universal-antecedent
     "with(p:prop, forall(r:rr, 0<r implies p))"
     ("dist(x,y)/3"))
    simplify
    (cut-with-single-formula "dist(x,y)<=dist(z_$0,x)+dist(z_$0,y)")
    simplify
    (cut-with-single-formula "dist(x,y)<=dist(x,z_$0)+dist(z_$0,y)")
    simplify
    (apply-macete-with-minor-premises triangle-inequality-for-distance)

    )))

(def-theorem ball-definedness
 "forall(a:pp,r:rr,#(ball(a,r)))"
 (theory metric-spaces)
 (usages transportable-macete)
 (proof (unfold-defined-constants insistent-direct-inference-strategy simplify)))

(def-theorem open-ball-definedness
  "forall(a:pp,r:rr,#(open%ball(a,r)))"
 (theory metric-spaces)
 (usages transportable-macete)
 (proof (unfold-defined-constants insistent-direct-inference-strategy simplify)))

(def-theorem ball-membership-condition
   ;;expand definitions and insistently simplify
  "forall(a,x:pp,r:rr,x in ball(a,r) iff dist(a,x)<=r)"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof (unfold-defined-constants direct-inference simplify-insistently)))

(def-theorem open-ball-membership-condition
  ;;expand definitions and insistently simplify
  "forall(a,x:pp,r:rr,x in open%ball(a,r) iff dist(a,x)<r)"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof (unfold-defined-constants direct-inference simplify-insistently)))

(def-theorem open-balls-are-open
  "forall(a:pp,r:rr,open(open%ball(a,r)))"
  (theory metric-spaces)
  (usages transportable-macete)

  (proof


   (

    unfold-defined-constants-repeatedly
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("(r-dist(a,x_$2))/2"))
    simplify
    (cut-with-single-formula "dist(a,x_$0)<=dist(a,x_$2)+dist(x_$2,x_$0)")
    simplify
    (apply-macete-with-minor-premises triangle-inequality-for-distance)


    )))

(def-constant LIM
   "lambda(s:[zz,pp],iota(x:pp, forall(eps:rr,0<eps implies forsome(n:zz, 
        forall(p:zz, n<=p implies dist(x,s(p))<=eps)))))"
  (theory metric-spaces))

(def-theorem characterization-of-limit
  "forall(s:[zz,pp],x:pp,lim(s)=x iff forall(eps:rr,0<eps implies forsome(n:zz, 
forall(p:zz, n<=p implies dist(x,s(p))<=eps))))"
  (theory metric-spaces)
  (usages transportable-macete)

  (proof
   (
    (unfold-single-defined-constant (0) lim)
    direct-and-antecedent-inference-strategy
    (contrapose "with(a:pp,p:prop, iota(x:pp, p)=a)")
    (eliminate-defined-iota-expression 0 w)
    (contrapose "with(eps:rr,s:[zz,pp],x:pp,
  forall(n:zz,
    forsome(p:zz,n<=p and not(dist(x,s(p))<=eps))));")
    (backchain-backwards "with(x,w:pp,w=x);")
    (backchain "with(p:prop,forall(eps:rr,0<eps implies p))")
    (apply-macete-with-minor-premises eliminate-iota-macete)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises metric-separation)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(s:[zz,pp],b_$0:pp,
  forall(eps:rr,
    0<eps
     implies 
    forsome(n:zz,
      forall(p:zz,n<=p implies dist(b_$0,s(p))<=eps))));" ("r"))
    (instantiate-universal-antecedent "with(s:[zz,pp],x:pp,
  forall(eps:rr,
    0<eps
     implies 
    forsome(n:zz,
      forall(p:zz,n<=p implies dist(x,s(p))<=eps))));" ("r"))
    (instantiate-existential ("s(max(n,n_$0))"))
    (apply-macete-with-minor-premises symmetry-of-distance)
    (backchain "with(r:rr,s:[zz,pp],b_$0:pp,n:zz,
  forall(p:zz,n<=p implies dist(b_$0,s(p))<=r));")
    (apply-macete-with-minor-premises maximum-1st-arg)
    (apply-macete-with-minor-premises symmetry-of-distance)
    (backchain "with(r:rr,s:[zz,pp],x:pp,n_$0:zz,
  forall(p:zz,n_$0<=p implies dist(x,s(p))<=r));")
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (instantiate-universal-antecedent "with(r:rr,s:[zz,pp],x:pp,n_$0:zz,
  forall(p:zz,n_$0<=p implies dist(x,s(p))<=r));" ("max(n,n_$0)"))

    )))


(def-theorem existence-of-limit
  "forall(s:[zz,pp], #(lim(s)) iff forsome(x:pp,forall(eps:rr,0<eps implies forsome(n:zz,forall(p:zz, n<=p implies dist(x,s(p))<=eps)))))"
  (theory metric-spaces)
  (usages transportable-macete)


  (proof


   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lim(s)=lim(s)")
    (incorporate-antecedent "with(s:[zz,pp],lim(s)=lim(s));")
    (apply-macete-with-minor-premises characterization-of-limit)
    direct-inference
    (instantiate-existential ("lim(s)"))
    (cut-with-single-formula "lim(s)=x")
    (apply-macete-with-minor-premises characterization-of-limit)


    )

   ))



 
(def-constant CAUCHY
  "lambda(s:[zz,pp],forall(eps:rr,0<eps implies
forsome(p:zz,forall(q:zz,p<q implies dist(s(p),s(q))<=eps))))"
  (theory metric-spaces))

(def-constant COMPLETE
 "forall(s:[zz,pp],cauchy(s) implies #(lim(s)))"
 (theory metric-spaces))

(def-theorem cauchy-double-index-characterization
  "forall(s:[zz,pp], cauchy(s) iff forall(eps:rr,0<eps implies 
forsome(n:zz,forall(p,q:zz,n<=p and n<=q implies dist(s(p),s(q))<=eps))))"

  (proof
   
   (
    
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,  forall(eps:rr,  0<eps implies p))" ("eps/2"))
    (contrapose "with(p:prop,not(p))")
    simplify
    (instantiate-existential ("p_$0+1"))
    (apply-macete-with-minor-premises triangle-inequality-alternate-form)
    (instantiate-existential ("s(p_$0)"))
    (cut-with-single-formula "dist(s(p_$0),s(p))<=eps/2 and dist(s(p_$0),s(q))<=eps/2")
    simplify
    direct-and-antecedent-inference-strategy
    (backchain "with(r:prop, forall(q_$0:zz,p_$0<q_$0 implies r))")
    simplify
    (backchain "with(r:prop, forall(q_$0:zz,p_$0<q_$0 implies r))")
    simplify
    (instantiate-universal-antecedent "with(r:prop, forall(q_$0:zz,p_$0<q_$0 implies r))" ("q"))
    (instantiate-universal-antecedent "with(r:prop, forall(q_$0:zz,p_$0<q_$0 implies r))" ("q"))
    (instantiate-universal-antecedent "with(r:prop, forall(q_$0:zz,p_$0<q_$0 implies r))" ("q"))
    (auto-instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))")
    (instantiate-existential ("n"))
    (backchain "with(eps:rr,s:[zz,pp],n:zz,forall(p,q:zz,n<=p and n<=q implies dist(s(p),s(q))<=eps))")
    simplify

    )

   )

  (usages transportable-macete)
  (theory metric-spaces))

(def-theorem convergent-implies-cauchy
  "forall(s:[zz,pp], #(lim(s)) implies cauchy(s))"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof

   (
    (apply-macete-with-minor-premises existence-of-limit)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) cauchy)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,0<eps implies p))" ("eps/2"))
    (simplify-antecedent "with(p:prop, not(p))")
    (instantiate-existential ("n_$0"))
    (cut-with-single-formula "dist(s(n_$0),s(q))<=dist(s(n_$0),x)+dist(x,s(q)) and dist(s(n_$0),x)<=eps/2 and dist(x,s(q))<=eps/2")
    (antecedent-inference "with(p,q,r:prop, p and q and r)")
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises triangle-inequality-for-distance)
    (instantiate-universal-antecedent
     "with(q:prop,n:zz,forall(p:zz,n<=p implies q))" ("q"))
    (simplify-antecedent "with(q,n_$0:zz,not(n_$0<=q));")
    (instantiate-universal-antecedent
     "with(q:prop,n:zz,forall(p:zz,n<=p implies q))" ("n_$0"))
    (simplify-antecedent "with(n_$0:zz,not(n_$0<=n_$0));")
    (apply-macete-with-minor-premises symmetry-of-distance)
    (backchain "with(q:prop,n:zz,forall(p:zz,n<=p implies q))")
    simplify
    (backchain "with(q:prop,n:zz,forall(p:zz,n<=p implies q))")
    simplify


    ))
  (usages transportable-macete))

(def-theorem closed-balls-are-closed
  "forall(x:pp,r:rr,s:[zz,pp], ran{s} subseteq ball(x,r) and #(lim(s)) implies lim(s) in ball(x,r))"
  (theory metric-spaces)
  (usages transportable-macete)

  
  (proof

   ((force-substitution "#(lim(s))" "#(lim(s)) and lim(s)=lim(s)" (0))
    (apply-macete-with-minor-premises characterization-of-limit)
    simplify-insistently
    (unfold-single-defined-constant (0 1) ball)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "dist(x_$1,lim(s))<=r or r<dist(x_$1,lim(s))")
    (antecedent-inference "with(p,q:prop, p or q)")
    (instantiate-universal-antecedent
     "with(s:[zz,pp],
  forall(eps:rr,
    0<eps
     implies 
    forsome(n:zz,
      forall(p:zz,n<=p implies dist(lim(s),s(p))<=eps))));" ("(dist(x_$1,lim(s))-r)/3"))
    (contrapose "with(p:prop, not(p))")
    simplify

    (instantiate-universal-antecedent "with(p:prop,n:zz,forall(q:zz,n<=q implies p))" ("n_$0"))

    (contrapose "with(p:prop, not(p))")
    simplify
    (instantiate-universal-antecedent "with(p:prop, forall(x:pp,p))" ("s(n_$0)"))
    (contrapose "with(p:prop, forall(x:zz, not(p)))")
    (instantiate-existential ("n_$0"))
    (apply-macete-with-minor-premises transitivity-of-<=) 
    (apply-macete-with-minor-premises symmetry-of-distance) 
    (instantiate-existential ("dist(lim(s),s(n_$0))+dist(s(n_$0),x_$1)"))
    (apply-macete-with-minor-premises triangle-inequality-for-distance)
    (incorporate-antecedent "with(a,b:pp,dist(a,b)<=(dist(b,a)-r)/3);") 
    (force-substitution "dist(x_$1,lim(s))" "dist(lim(s),x_$1)" (0)) 
    simplify
    simplify
    simplify)))

;;"$METRIC_SPACES/proofs/closed-balls-are-closed.t"

(def-theorem ball-subset-larger-radius-open-ball
  ;;expand definitions and insistently simplify
  "forall(a:pp,r,r_1:rr,r<r_1 implies ball(a,r) subseteq open%ball(a,r_1))"
  (theory  metric-spaces)
  (usages transportable-macete)
  (proof (unfold-defined-constants simplify-insistently)))

;;;(def-compound-macete properties-of-balls
;;;  (repeat
;;;   tr%open-ball-definedness
;;;   tr%ball-definedness
;;;   tr%open-ball-membership-condition
;;;   tr%ball-membership-condition
;;;   tr%open-balls-are-open
;;;   tr%zero-self-distance
;;;   tr%meaning-of-inverse-image-membership))

(def-theorem limit-of-subsequence
  "forall(s:[zz,pp],phi:[zz,zz],#(lim(s)) and convergent%to%infinity(phi) implies lim(s)=lim(s oo phi))"
  (theory metric-spaces)
  (usages transportable-macete)

  (proof
   (

    (unfold-single-defined-constant (0) convergent%to%infinity)
    (force-substitution "lim(s)=lim(s oo phi)" "lim(s oo phi)=lim(s)" (0))
    direct-inference-strategy
    (antecedent-inference "with(p,q:prop, p and q)")
    (cut-with-single-formula "lim(s)=lim(s)")
    (incorporate-antecedent "with(s:[zz,pp],lim(s)=lim(s));")
    (apply-macete-with-minor-premises characterization-of-limit)
    direct-inference-strategy
    (auto-instantiate-universal-antecedent "with(p:prop, forall(eps:rr,
    0<eps
     implies p))")
    (instantiate-universal-antecedent "with(p:prop,forall(m:rr,forsome(x:zz,p)))" ("n"))
    (instantiate-existential ("x"))
    beta-reduce-insistently
    (backchain "with(eps:rr,s:[zz,pp],n:zz,
  forall(p:zz,n<=p implies dist(lim(s),s(p))<=eps));")
    simplify
    simplify
    simplify
    )))

(def-theorem limit-of-subsequence-corollary
  "forall(s:[zz,pp],n:zz, #(lim(s)) implies lim(s)=lim(s oo lambda(i:zz,(if (n<=i,i,?zz)))))"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof
   
   ((apply-macete-with-minor-premises limit-of-subsequence)
    (unfold-single-defined-constant (0) convergent%to%infinity)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(m_1:zz,max(n,m)<m_1)")
    (instantiate-existential ("m_1"))
    (cut-with-single-formula "n<=max(n,m) and m<=max(n,m)")
    simplify
    (apply-macete-with-minor-premises maximum-1st-arg)
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (apply-macete-with-minor-premises archimedean))

   ))


(def-theorem limit-depends-on-tail
  "forall(s,s_1:[zz,pp],n:zz,
  forsome(m:zz,forall(p:zz,m<=p implies s_1(p)=s(p)))
   and 
  #(lim(s))
   implies 
  lim(s_1)=lim(s))"
  (theory metric-spaces)
  (usages transportable-macete)

  (proof
   (
    (apply-macete-with-minor-premises characterization-of-limit)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "lim(s)=lim(s)")
    (incorporate-antecedent "with(s:[zz,pp],lim(s)=lim(s))")
    (apply-macete-with-minor-premises characterization-of-limit)
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent "with(s:[zz,pp],forall(eps:rr,
    0<eps
     implies 
    forsome(n:zz,
      forall(p:zz,n<=p implies dist(lim(s),s(p))<=eps))))")
    (instantiate-existential ("max(n,m)"))
    (backchain "with(s,s_1:[zz,pp],m:zz,forall(p:zz,m<=p implies s_1(p)=s(p)))")
    direct-inference
    (cut-with-single-formula "m<=max(n,m)")
    simplify
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (backchain "with(eps:rr,s:[zz,pp],n:zz,
  forall(p:zz,n<=p implies dist(lim(s),s(p))<=eps))")
    (cut-with-single-formula "n<=max(n,m)")
    simplify
    (apply-macete-with-minor-premises maximum-1st-arg)


    )))
  
(def-theorem limit-translation-invariance
  "forall(s:[zz,pp],a,b:zz,#(lim(s)) and 0<a implies lim(s)=lim(lambda(j:zz,s(a*j+b))))"
  (theory metric-spaces)

  (proof
 
   (

    (force-substitution "lambda(j:zz,s(a*j+b))" "s oo lambda(j:zz,a*j+b)" (0))
    (apply-macete-with-minor-premises limit-of-subsequence)
    simplify
    (force-substitution "b+j*a" "a*j+b" (0))
    (apply-macete-with-minor-premises convergent%to%infinity-linear-form)
    sort-definedness
    simplify
    simplify-insistently

    )))

(def-constant CLOSURE
  "lambda(a:sets[pp],indic{y:pp,forall(r:rr,0<r implies nonempty_indic_q{open%ball(y,r) inters a})})"
  (theory metric-spaces))

(def-theorem characterization-of-closure-lemma-1
  "forall(x:pp,a:sets[pp], forsome(s:[zz,pp],ran{s} subseteq a and lim(s)=x) implies x in closure(a))"
  lemma
  (proof
   ((force-substitution "ran{s} subseteq a " "forall(x:zz, #(s(x)) implies s(x) in a)" (0))
    (apply-macete-with-minor-premises characterization-of-limit)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) closure) simplify-insistently
    (apply-macete-with-minor-premises open-ball-membership-condition)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,  forall(eps:rr, 0<eps implies p))" ("r_$0/2"))
    (contrapose "with(p:prop, not(p))")
    simplify
    (instantiate-existential ("s(n)"))
    (instantiate-universal-antecedent "with(r_$0:rr,s:[zz,pp],x_$0:pp,n:zz,
  forall(p:zz,n<=p implies dist(x_$0,s(p))<=r_$0/2));" ("n"))
    (contrapose "with(p:prop, not(p))")
    simplify
    simplify
    (backchain "with(a:sets[pp],s:[zz,pp],forall(x:zz,#(s(x)) implies s(x) in a));")
    simplify
    direct-and-antecedent-inference-strategy
    (backchain "with(a,b:sets[pp],s:[zz,pp],b subseteq a);")
    simplify-insistently
    (instantiate-existential ("x"))))
  (theory metric-spaces))

(def-theorem characterization-of-closure-lemma-2
  "forall(x:pp,a:sets[pp], x in closure(a) implies forsome(s:[zz,pp], forall(n:zz,1<=n implies s(n) in a and dist(s(n),x)<=1/n)))"
  lemma
  (theory metric-spaces)
  (proof
   (


    (unfold-single-defined-constant (0) closure)
    simplify-insistently
    (apply-macete-with-minor-premises open-ball-membership-condition)
    direct-and-antecedent-inference-strategy
    choice-principle
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,p);" ("max(1,n)^[-1]"))
    (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 0)")
      (contrapose "with(p:prop,p);")
      (apply-macete-with-minor-premises fractional-expression-manipulation)
      simplify)
    (block 
      (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0)")
      (cut-with-single-formula
       "forsome(z:pp, z in a and dist(x,z)<max(1,n)^[-1])")
      (move-to-sibling 1)
      auto-instantiate-existential
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(z:pp,p));")
	(instantiate-existential ("z"))
	(force-substitution "n" "max(1,n)" (0))
	simplify
	(block 
	  (script-comment "`force-substitution' at (1)")
	  (unfold-single-defined-constant (0) max)
	  simplify)))


    )))

;;;   (proof
;;;    ((unfold-single-defined-constant (0) closure)
;;;     simplify-insistently
;;;     (apply-macete-with-minor-premises open-ball-membership-condition)
;;;     direct-and-antecedent-inference-strategy
;;;     choice-principle
;;;     direct-and-antecedent-inference-strategy
;;;     (instantiate-universal-antecedent
;;;      "with(p:prop,forall(r:rr,0<r implies p))"
;;;      ("max(1,n)^[-1]"))
;;;     (contrapose "with(p:prop,not(p))")
;;;     (apply-macete-with-minor-premises fractional-expression-manipulation)
;;;     simplify
;;;     (instantiate-existential ("x_$2"))
;;;     (force-substitution "n" "max(1,n)" (0))
;;;     simplify
;;;     (unfold-single-defined-constant (0) max)
;;;     simplify))



(def-theorem characterization-of-closure
  "forall(x:pp,a:sets[pp], x in closure(a) iff forsome(s:[zz,pp],ran{s} subseteq a and lim(s)=x))"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0)")
     (cut-with-single-formula "forsome(s:[zz,pp], forall(n:zz,1<=n implies s(n) in a and dist(s(n),x_$1)<=1/n))")
     (block 
      (script-comment "node added by `cut-with-single-formula' at (0)")
      (instantiate-existential ("lambda(n:zz, if(1<=n,s(n),?pp))"))
      (block 
       (script-comment "node added by `instantiate-existential' at (0 0 0)")
       simplify-insistently
       direct-and-antecedent-inference-strategy
       (backchain "with(p,x_$3:pp,x_$3=p);")
       (backchain "with(p:prop,forall(n:zz,p));"))
      (block 
       (script-comment "node added by `instantiate-existential' at (0 0 1)")
       (apply-macete-with-minor-premises characterization-of-limit)
       beta-reduce-repeatedly
       direct-and-antecedent-inference-strategy
       (cut-with-single-formula "forsome(n:zz,1<=n and 1/n<=eps)")
       (block 
	(script-comment "node added by `cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(n:zz,p));")
	(instantiate-existential ("n"))
	simplify
	(instantiate-universal-antecedent "with(p:prop,forall(n:zz,p));"
					  ("p"))
	(block 
	 (script-comment "node added by `instantiate-universal-antecedent' at (0 0 0)")
	 (contrapose "with(p:prop,not(p));")
	 simplify)
	(block 
	 (script-comment "node added by `instantiate-universal-antecedent' at (0 0 1 0)")
	 (cut-with-single-formula "1/p<=1/n")
	 simplify
	 (block 
	  (script-comment "node added by `cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises fractional-expression-manipulation)
	  simplify)))
       (block 
	(script-comment "node added by `cut-with-single-formula' at (1)")
	(force-substitution "1/n<=eps" "eps^[-1]<=n" (0))
	(block 
	 (script-comment "node added by `force-substitution' at (0)")
	 (cut-with-single-formula "forsome(n:zz, eps^[-1]+1<=n)")
	 (block 
	  (script-comment "node added by `cut-with-single-formula' at (0)")
	  (instantiate-existential ("n"))
	  (block 
	   (script-comment "node added by `instantiate-existential' at (0 0 0)")
	   (cut-with-single-formula "0<eps^[-1]")
	   simplify
	   (block 
	    (script-comment "node added by `cut-with-single-formula' at (1)")
	    (apply-macete-with-minor-premises fractional-expression-manipulation)
	    simplify))
	  simplify)
	 (block 
	  (script-comment "node added by `cut-with-single-formula' at (1)")
	  (cut-with-single-formula "forsome(n:zz,eps^[-1]+1<n)")
	  (block 
	   (script-comment "node added by `cut-with-single-formula' at (0)")
	   (instantiate-existential ("n"))
	   simplify)
	  (apply-macete-with-minor-premises archimedean)))
	(block 
	 (script-comment "node added by `force-substitution' at (1)")
	 (apply-macete-with-minor-premises fractional-expression-manipulation)
	 simplify))))
     (apply-macete-with-minor-premises characterization-of-closure-lemma-2))
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 1 0
0)")
     (apply-macete-with-minor-premises characterization-of-closure-lemma-1)
     (instantiate-existential ("s")))

    )

   ))



(def-theorem closure-contains-set
  "forall(s:sets[pp], s subseteq closure(s))"
  (theory metric-spaces)
  (proof
   (
    (unfold-single-defined-constant (0) closure)
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify-insistently
    (apply-macete-with-minor-premises open-ball-membership-condition)
    (instantiate-existential ("x"))
    simplify
    ))
  (usages transportable-macete))

(def-theorem  generalized-triangle-inequality
  "forall(s:[zz,pp],p,q:zz, 
     p<=q and forall(j:zz,p<=j and j<=q+1 implies #(s(j))) 
      implies 
    dist(s(p),s(q+1))<=sum(p,q,lambda(j:zz,dist(s(j),s(j+1)))))"
  (theory metric-spaces)
  (proof 
   (
    (induction integer-inductor common-lisp:nil)
    (prove-by-logic-and-simplification 3)
    (block 
	(script-comment "`induction' at (0 0 0 0 0 0 0 1 0 0 0 0 0 0 0)")
      (antecedent-inference-strategy (1))
      (block 
	  (script-comment "`antecedent-inference-strategy' at (0 0 0)")
	(contrapose "with(p:prop,not(p));") 
	simplify)
      (block 
	  (script-comment "`antecedent-inference-strategy' at (1)")
	(apply-macete-with-minor-premises triangle-inequality-alternate-form)
	(block 
	    (script-comment "`apply-macete-with-minor-premises' at (0)")
	  (instantiate-existential ("s(1+t)")) 
	  simplify)
	simplify))
    )))


(def-theorem dist-continuity-lemma
  "forall(x,y,z:pp, abs(dist(x,z)-dist(y,z))<=dist(x,y))"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof		
 
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) abs)
    (cut-with-single-formula "dist(x,z)<=dist(x,y)+dist(y,z) 
     and dist(y,z)<=dist(y,x)+dist(x,z)")
    (prove-by-logic-and-simplification 3)
    (apply-macete-with-minor-premises triangle-inequality-for-distance)


    )))
