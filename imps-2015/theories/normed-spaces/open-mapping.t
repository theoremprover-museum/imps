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


(herald open-mapping)

(include-files 
 (files (imps theories/normed-spaces/normed-spaces)
	(imps theories/metric-spaces/fixed-point-theorem)))


(def-theorem LIPSCHITZ%BOUND-TRANSLATION-INVERSION
  "forall(phi:[uu,uu],s:sets[uu],y:uu,c:rr,
     lipschitz%bound%on(phi,c,s) 
      implies 
     lipschitz%bound%on(lambda(x:uu,[-1]*phi(x)+y),c,s))"
  lemma
  (theory normed-linear-spaces)
  (proof

   (

    unfold-defined-constants
    (force-substitution "norm(phi(x)-phi(y))" "norm([-1]*(phi(x)-phi(y)))" (0))
    simplify
    (apply-macete-with-minor-premises norm-scalar-multiplication)
    (apply-macete-with-minor-premises absolute-value-non-positive)
    simplify

    )))

(def-theorem OPEN-MAPPING-LEMMA
  "forall(phi:[uu,uu],b:uu,r,c:rr,
     complete and lipschitz%bound%on(phi,c,ball(b,r))  and c<1 and 0<=r 
      implies
     open%ball(lambda(z:uu,phi(z) + z)(b),(1-c)*r)
      subseteq
     image(lambda(z:uu,phi(z) + z),ball(b,r)))"
  lemma
  (theory normed-linear-spaces)

  ;; This results says that if x is sufficiently near phi(b)+b,
  ;; then x=phi(z)+z for some z near b.
  ;; Prove this by reducing x=phi(z)+z to a fixed point problem x-phi(z)=z.
  ;;
  
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(phi(b))")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (unfold-single-defined-constant (0) open%ball) simplify-insistently
     direct-and-antecedent-inference-strategy
     (force-substitution "x_$0=x+phi(x)" "lambda(x:uu, x_$0+[-1]*phi(x))(x)=x" (0))
     (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises tr%restricted-fixed-point-theorem)
      (instantiate-existential ("c"))
      (block 
       (script-comment "`instantiate-existential' at (0 2)")
       (apply-macete-with-minor-premises %vector-plus-commutativity)
       (apply-macete-with-minor-premises lipschitz%bound-translation-inversion)
       )
      simplify
      )
     simplify
     )
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (incorporate-antecedent
      "with(f:sets[uu],c:rr,phi:[uu,uu],
  lipschitz%bound%on(phi,c,f));"
      )
     unfold-defined-constants simplify-insistently direct-and-antecedent-inference-strategy
     (instantiate-universal-antecedent "with(p:prop,forall(x_$0,y_$0:uu,p));" ("b" "b"))
     (contrapose "with(p:prop,not(p));") 
     simplify
     )

    )))

(def-theorem IMAGE-CONTAINED-IN-RANGE
  "forall(s:sets[ind_1],f:[ind_1,ind_2], image(f,s) subseteq ran(f))"
  lemma
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof (simplify-insistently 
	  direct-and-antecedent-inference-strategy 
	  auto-instantiate-existential)))

(def-theorem lipschitz%bound%on%subsets
  "forall(phi:[pp_0,pp_1],s,s_1:sets[pp_0],r:rr,s subseteq s_1 and 
 lipschitz%bound%on(phi,r,s_1) implies lipschitz%bound%on(phi,r,s))"
  lemma
  (theory metric-spaces-2-tuples)
  (proof
   (
    
    (unfold-single-defined-constant (0 1) lipschitz%bound%on)
    (prove-by-logic-and-simplification 3)


    ))
  (usages transportable-macete))


(def-theorem OPEN-MAPPING
  "forall(phi:[uu,uu],b:uu,c:rr,
     complete and lipschitz%bound%on(phi,c,dom{phi})  and c<1 
      implies 
     (open(dom{phi}) implies open(ran{lambda(z:uu,phi(z)+z)})))"

  (theory normed-linear-spaces)
  (proof

   (
    (unfold-single-defined-constant (0 1) open)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(x_$2:uu,phi:[uu,uu],x_$2 in ran{lambda(z:uu,phi(z)+z)});")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(phi:[uu,uu],
  forall(x_$2:uu,
    x_$2 in dom{phi}
     implies 
    forsome(delta_$0:rr,
      0<delta_$0 and ball(x_$2,delta_$0) subseteq dom{phi})));" ("x"))
    (contrapose "with(x:uu,phi:[uu,uu],not(x in dom{phi}));")
    simplify
    (instantiate-existential ("(1-c)*delta_$1/2"))
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (apply-macete-with-minor-premises tr%subseteq-transitivity)
    (instantiate-existential ("image(lambda(z:uu,phi(z)+z),ball(x,delta_$1))"))
    (apply-macete-with-minor-premises tr%subseteq-transitivity)
    (instantiate-existential ("open%ball(lambda(x:uu,phi(x)+x)(x),(1-c)*delta_$1)"))
    simplify
    (apply-macete-with-minor-premises tr%ball-subset-larger-radius-open-ball)
    simplify
    (apply-macete-with-minor-premises open-mapping-lemma)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%lipschitz%bound%on%subsets)
    auto-instantiate-existential
    simplify
    (apply-macete-with-minor-premises tr%image-contained-in-range)

    )))






