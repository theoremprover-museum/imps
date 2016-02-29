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


(herald examples-of-continuity)

(include-files
 (files (imps theories/metric-spaces/metric-space-pairs)
	(imps theories/metric-spaces/metric-space-supplements)))


(def-constant quadratic%bound%at%point
  "lambda(f:[pp_0,pp_1], x:pp_0, 
             forsome(a:rr, 0<=a and forall(y:pp_0,dist_1(f(x),f(y))<=dist_0(x,y)*(a+dist_0(x,y)))))"
  (theory metric-spaces-2-tuples))

(comment
 (def-theorem monotone-product-lemma
   "forall(x,y,z,u:rr, 0<=x and x<=y and 0<=u and u<=z implies x*u<=y*z)"

   (proof

    (

     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises transitivity-of-<=)
     (instantiate-existential ("x*z"))
     (cut-with-single-formula "0<=x*(z-u)")
     simplify
     (apply-macete-with-minor-premises positivity-for-products)
     simplify
     (cut-with-single-formula "0<=(y-x)*z")
     simplify
     (apply-macete-with-minor-premises positivity-for-products)
     simplify


     )


    )
   (theory h-o-real-arithmetic)))

(def-theorem quadratic-is-continuous
  "forall(f:[pp_0,pp_1], x:pp_0, quadratic%bound%at%point(f,x) implies continuous%at%point(f,x))"

  (proof


   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("min(1,eps/(1+a))"))
    (weaken (0))
    (unfold-single-defined-constant (0) min)
    (case-split ("1<=eps/(1+a)"))
    simplify
    simplify
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("dist_0(x,y_$0)*(a+dist_0(x,y_$0))"))
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("(eps/(1+a))*(a+1)"))
    (apply-macete-with-minor-premises monotone-product-lemma)
    (cut-with-single-formula "min(1,eps/(1+a))<=1 and min(1,eps/(1+a))<=eps/(1+a)")
    simplify
    (apply-macete-with-minor-premises minimum-2nd-arg)
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify


    ))
  
  (usages transportable-macete)
  (theory metric-spaces-2-tuples))

(def-theory-ensemble-instances metric-spaces
  force-under-quick-load
  (target-theories metric-spaces h-o-real-arithmetic h-o-real-arithmetic)
  (sorts (pp pp rr rr))
  (constants (dist dist "lambda(x,y:rr, abs(x-y))" "lambda(x,y:rr, abs(x-y))"))
  (permutations (1) (0 1) (1 2)))


(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-theorem square-is-quadratic
  "forall(x:rr,quadratic%bound%at%point(lambda(x:rr, x^2),x))"
  (theory h-o-real-arithmetic)
  (proof
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("2*abs(x)"))
    simplify
    (force-substitution "x^2-y_$1^2" "(x-y_$1)*(x+y_$1)" (0))
    (force-substitution "x+y_$1" "(x+x)+(y_$1-x)" (0))
    (apply-macete-with-minor-premises absolute-value-product)
    (apply-macete-with-minor-premises monotone-product-lemma)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify
    unfold-defined-constants
    (weaken (0 1 2 3))
    (prove-by-logic-and-simplification 3)
    simplify
    simplify


    ))


  (theory h-o-real-arithmetic))

(def-theorem multiplication-by-a-constant-is-quadratic
  "forall(a,x:rr,quadratic%bound%at%point(lambda(x:rr, a*x),x))"
  
  (proof

   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("abs(a)"))
    simplify
    (force-substitution "a*x-a*y_$1" "a*(x-y_$1)" (0))
    (apply-macete-with-minor-premises absolute-value-product)
    simplify
    simplify


    
    ))


  (theory h-o-real-arithmetic))

(def-theorem square-is-continuous
  "forall(x:rr, continuous%at%point(lambda(x:rr,x^2),x))"

  (proof

   (

    (apply-macete-with-minor-premises tr%quadratic-is-continuous)
    (apply-macete-with-minor-premises square-is-quadratic)


    )


   )

  (theory h-o-real-arithmetic))

(def-theorem multiplication-by-a-constant-is-continuous
  "forall(a,x:rr,continuous%at%point(lambda(x:rr, a*x),x))"

  (proof

   (


    (apply-macete-with-minor-premises tr%quadratic-is-continuous)
    (apply-macete-with-minor-premises multiplication-by-a-constant-is-quadratic)


    ))


  (theory h-o-real-arithmetic))



(def-theorem composition-of-continuous-is-continuous
  "forall(f:[pp,rr],g:[rr,rr],x:pp,
     continuous%at%point(f,x) and continuous%at%point(g,f(x))
      implies 
     continuous%at%point(g oo f,x))"
  

  (proof


   (

    
    unfold-defined-constants
    beta-reduce-with-minor-premises
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent "with(g:[rr,rr],x:pp,f:[pp,rr],
  forall(eps_$0:rr,
    0<eps_$0
     implies 
    forsome(delta_$0:rr,
      0<delta_$0
       and 
      forall(y_$0:rr,
        abs(f(x)-y_$0)<=delta_$0
         implies 
        abs(g(f(x))-g(y_$0))<=eps_$0))));")
    (instantiate-universal-antecedent "with(f:[pp,rr],x:pp,
  forall(eps:rr,
    0<eps
     implies 
    forsome(delta:rr,
      0<delta
       and 
      forall(y:pp,
        dist(x,y)<=delta implies abs(f(x)-f(y))<=eps))));" ("delta_$0"))
    (instantiate-existential ("delta"))
    (backchain "with(eps_$0:rr,g:[rr,rr],delta_$0:rr,x:pp,f:[pp,rr],
  forall(y_$0:rr,
    abs(f(x)-y_$0)<=delta_$0
     implies 
    abs(g(f(x))-g(y_$0))<=eps_$0));")
    (backchain "with(delta_$0:rr,f:[pp,rr],delta:rr,x:pp,
  forall(y:pp,
    dist(x,y)<=delta implies abs(f(x)-f(y))<=delta_$0));")
    (cut-with-single-formula "abs(f(x)-f(y_$0))<=delta_$0")
    (instantiate-universal-antecedent "with(f:[pp,rr],x:pp,
  forall(eps:rr,
    0<eps
     implies 
    forsome(delta:rr,
      0<delta
       and 
      forall(y:pp,
        dist(x,y)<=delta implies abs(f(x)-f(y))<=eps))));" ("1"))
    (simplify-antecedent "not(0<1);")
    (cut-with-single-formula "abs(f(x)-f(x))<=1")
    (backchain "with(f:[pp,rr],delta:rr,x:pp,
  forall(y:pp,dist(x,y)<=delta implies abs(f(x)-f(y))<=1));")
    simplify



    ))


  (theory metric-spaces))


(def-theorem sum-of-continuous-is-continuous
  "forall(f,g:[pp,rr], x:pp, 
     continuous%at%point(f,x) and continuous%at%point(g,x) 
      implies 
     continuous%at%point(lambda(x:pp,f(x)+g(x)),x))"

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
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("abs(f(x)-f(y_$1))+abs(g(x)-g(y_$1))"))
    (cut-with-single-formula "#(f(x)) and #(g(x)) and #(f(y_$1)) and #(g(y_$1))")
    unfold-defined-constants
    (weaken (1 2 3 4 5 6 7))
    (prove-by-logic-and-simplification 3)
    simplify
    (instantiate-universal-antecedent "with(eps_$0:rr,f:[pp,rr],delta_$0:rr,x:pp,
  forall(y:pp,
    dist(x,y)<=delta_$0 implies abs(f(x)-f(y))<=eps_$0/2));" ("y_$1"))
    (contrapose "with(p:prop, not(p))")
    simplify
    (instantiate-universal-antecedent "with(eps_$0:rr,g:[pp,rr],delta:rr,x:pp,
  forall(y:pp,
    dist(x,y)<=delta implies abs(g(x)-g(y))<=eps_$0/2));" ("y_$1"))
    (contrapose "with(p:prop, not(p))")
    simplify
    simplify
    (cut-with-single-formula "abs(f(x)-f(y_$1))<=eps_$0/2 and abs(g(x)-g(y_$1))<=eps_$0/2")
    simplify
    direct-inference
    (backchain "with(eps_$0:rr,f:[pp,rr],delta_$0:rr,x:pp,
  forall(y:pp,
    dist(x,y)<=delta_$0 implies abs(f(x)-f(y))<=eps_$0/2));")
    simplify
    (backchain "with(eps_$0:rr,g:[pp,rr],delta:rr,x:pp,
  forall(y:pp,
    dist(x,y)<=delta implies abs(g(x)-g(y))<=eps_$0/2));")
    simplify
    (instantiate-universal-antecedent "with(eps_$0:rr,f:[pp,rr],delta_$0:rr,x:pp,
  forall(y:pp,
    dist(x,y)<=delta_$0 implies abs(f(x)-f(y))<=eps_$0/2));" ("y_$1"))
    (instantiate-universal-antecedent "with(eps_$0:rr,g:[pp,rr],delta:rr,x:pp,
  forall(y:pp,
    dist(x,y)<=delta implies abs(g(x)-g(y))<=eps_$0/2));" ("y_$1"))
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises minimum-2nd-arg)


    )


   )

  (usages transportable-macete)
  (theory metric-spaces))


(def-schematic-macete abstraction-for-sum
  "with(a,b:rr, lambda(x:pp,a+b)=lambda(x:pp,lambda(x:pp,a)(x)+lambda(x:pp,b)(x)))"
  (theory metric-spaces)
  null)
 
(def-schematic-macete abstraction-for-square
  "with(a:rr, lambda(x:pp,a^2)=lambda(x:rr,x^2) oo lambda(x:pp,a))"
  (theory metric-spaces)
  null)

(def-schematic-macete abstraction-for-scalar-product
  "with(a,c:rr, lambda(x:pp,a * c)=lambda(x:rr,a * x) oo lambda(x:pp, c))"
  (theory metric-spaces)
  null)

(def-compound-macete abstraction
  (sound
   (series abstraction-for-sum
	   abstraction-for-scalar-product
	   abstraction-for-square)
   beta-reduce-unstoppably
   beta-reduce-unstoppably))

(def-compound-macete composite-continuity-macete
  (series
   (repeat
   abstraction
   sum-of-continuous-is-continuous
   composition-of-continuous-is-continuous
   square-is-continuous
   multiplication-by-a-constant-is-continuous)
  tr%unary-eta-reduction))

(def-theorem product-in-terms-of-squares-lemma
  "forall(a,b:rr, a*b=1/2*((a+b)^2+[-1]*(a^2+b^2)))"
  
  (proof
   (
    simplify
    ))

  (theory h-o-real-arithmetic))

(def-theorem continuous-at-point-defined
  "forall(f:[pp_0,pp_1], x:pp_0, continuous%at%point(f,x) implies #(f(x)))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)
  (proof
   
   (

    (unfold-single-defined-constant (0) continuous%at%point)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("1"))
    (simplify-antecedent "not(0<1);")
    (cut-with-single-formula "dist_1(f(x),f(x))<=1")
    (backchain "with(f:[pp_0,pp_1],delta:rr,x:pp_0,
  forall(y:pp_0,
    dist_0(x,y)<=delta implies dist_1(f(x),f(y))<=1));")
    (apply-macete-with-minor-premises tr%zero-self-distance)
    simplify


    )

   ))

(def-theorem product-of-continous-is-continuous
  "forall(f,g:[pp,rr], x:pp, continuous%at%point(f,x) and continuous%at%point(g,x) implies
                       continuous%at%point(lambda(x:pp, f(x)*g(x)),x))"
  (theory metric-spaces)
  (usages transportable-macete)
  (proof
   (

    (apply-macete-with-minor-premises product-in-terms-of-squares-lemma)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(f(x)) and #(g(x))")
    (apply-macete-with-minor-premises composite-continuity-macete)
    simplify
    (apply-macete-with-minor-premises tr%continuous-at-point-defined)
    simplify


    )))


;;This properly should go in the file on uniform continuity, but this
;;is the easiest way to show there are continuous functions on a metric 
;;space.

(def-theorem dist-uniformly-continuous
  "forall(y:pp,uniformly%continuous(lambda(x:pp,dist(x,y))))"
  (usages transportable-macete)
  (proof

   (
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (cut-with-single-formula "abs(dist(x_$1,y)-dist(y_$1,y))<=dist(x_$1,y_$1)")
    simplify
    (apply-macete-with-minor-premises dist-continuity-lemma)


    ))

  (theory metric-spaces))


(def-theorem constant-uniformly-continuous
  "forall(r:rr,uniformly%continuous(lambda(x:pp,r)))"
  (usages transportable-macete)
  (theory metric-spaces)
  (proof
   
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (unfold-single-defined-constant (0) abs)
    simplify


    )))

(def-theorem constant-is-continuous
  "forall(r:rr,x:pp, continuous%at%point(lambda(x:pp,r),x))"
  (usages transportable-macete)
  (theory metric-spaces)
  (proof
   
   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (unfold-single-defined-constant (0) abs)
    simplify


    )))

(include-files
 (files (imps theories/metric-spaces/metric-space-self-mappings)))


(def-theorem identity-uniformly-continuous
  "uniformly%continuous(lambda(x:pp,x))"
  (usages transportable-macete)
  (theory metric-spaces)
  (proof


   (

    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential


    )))
   
;; This is a special case of the theorem for metric-space triples. Notice the proof 
;; is identical.

(def-theorem composition-of-continuous-special-case
  "forall(f:[pp,pp],g:[pp,rr],x:pp,
     continuous%at%point(f,x) and continuous%at%point(g,f(x))
      implies 
     continuous%at%point(g oo f,x))"


  (proof


   (

    
    unfold-defined-constants
    beta-reduce-with-minor-premises
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent "with(p:prop,forall(eps:rr,  0<eps implies p))")
    (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,  0<eps implies p))" ("delta_$0"))
    (instantiate-existential ("delta"))
    (backchain "with(eps_$0:rr,g:[pp,rr],delta_$0:rr,x:pp,f:[pp,pp],
  forall(y_$0:pp,
    dist(f(x),y_$0)<=delta_$0
     implies 
    abs(g(f(x))-g(y_$0))<=eps_$0));")
    (backchain "with(delta_$0:rr,f:[pp,pp],delta:rr,x:pp,
  forall(y:pp,
    dist(x,y)<=delta implies dist(f(x),f(y))<=delta_$0));")
    (cut-with-single-formula "dist(f(x),f(y_$0))<=delta_$0")
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("1"))
    (simplify-antecedent "not(0<1);")
    (cut-with-single-formula "dist(f(x),f(x))<=1")
    (backchain "with(f:[pp,pp],delta:rr,x:pp,
  forall(y:pp,dist(x,y)<=delta implies dist(f(x),f(y))<=1));")
    simplify


    ))

  (usages transportable-macete)
  (theory metric-spaces))


(def-schematic-macete transportable-abstraction-for-sum
  "with(a,b:rr, lambda(x:ind_1,a+b)=lambda(x:ind_1,lambda(x:ind_1,a)(x)+lambda(x:ind_1,b)(x)))"
  (theory generic-theory-1)
  transportable
  null)
 
(def-schematic-macete transportable-abstraction-for-product
  "with(a,c:rr, lambda(x:ind_1,a * c)=lambda(x:ind_1,lambda(x:ind_1,a)(x) * lambda(x:ind_1, c)(x)))"
  (theory generic-theory-1)
  transportable
  null)

(def-compound-macete real-fn-abstraction
  (sound
   (series transportable-abstraction-for-sum
	   transportable-abstraction-for-product)
   beta-reduce-unstoppably
   beta-reduce-unstoppably))

(def-compound-macete polynomial-continuity-macete
  (series
   (repeat
    (without-minor-premises exp-out)
    real-fn-abstraction
    tr%sum-of-continuous-is-continuous
    tr%product-of-continous-is-continuous
    tr%constant-is-continuous
    beta-reduce)
   tr%unary-eta-reduction))
