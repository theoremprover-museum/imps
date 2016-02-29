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


(herald mappings-from-an-interval)

(load-section foundation)

(def-language language-for-interval-theory
  (embedded-languages h-o-real-arithmetic)
  (sorts (ii rr)))

(def-theory fixed-interval-theory
  (component-theories h-o-real-arithmetic)
  (language language-for-interval-theory)
  (axioms
   (interval-characterization
    "forall(a,b:ii,x:rr, a<=x and x<=b implies #(x,ii))")
   (non-degeneracy
    "forsome(x,y:ii, x<y)")))

(def-theorem interval-bounding-lemma
  "forall(x,y:rr, c,d :ii, not(#(x,ii)) and not(#(y,ii)) and x<=c and c<=y implies 
          x<d  and d<y)"
         
  ;; If reals not in the interval surround one element of the interval then they surround them
  ;; all.

  (proof

   (

    direct-and-antecedent-inference-strategy
    (contrapose "with(x:rr,not(#(x,ii)));")
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("c" "d"))
    simplify
    (contrapose "with(y:rr,not(#(y,ii)));")
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-existential ("d" "c"))
    simplify


    ))

  (theory fixed-interval-theory))


(def-constant dseq
  "lambda(delta:rr, lambda(x:rr, delta*(floor(x/delta))))"
  (theory h-o-real-arithmetic))

(def-theorem dseq-definedness
  "forall(delta,x:rr, 0<delta implies #(dseq(delta)(x)))"
  (theory fixed-interval-theory)
  (proof
   (

    (unfold-single-defined-constant (0) dseq)
    direct-and-antecedent-inference-strategy
    (instantiate-theorem floor-definedness ("x/delta"))
    simplify

    )))

(def-theorem dseq-distance-bound
  "forall(x,delta:rr, 0<delta implies dseq(delta)(x)<=x and x<dseq(delta)(x)+delta)"
  (theory fixed-interval-theory)
  (proof



   (


    direct-inference
    direct-inference
    unfold-defined-constants
    (cut-with-single-formula "forsome(n:zz, floor(x/delta)=n)")
    (antecedent-inference "with(p:prop,forsome(n:zz,p));")
    (backchain-repeatedly ("with(n,z:zz,z=n);"))
    (incorporate-antecedent "with(n,z:zz,z=n);")
    (apply-macete-with-minor-premises floor-characterization)
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    simplify
    (cut-with-single-formula "total_q{floor,[rr,zz]}")
    (instantiate-existential ("floor(x/delta)"))
    simplify
    (apply-macete-with-minor-premises floor-definedness)

    )))

(def-constant delta%width
  "lambda(delta:rr, 0<delta and forsome(x,y:ii, delta<=y-x))"
  (theory fixed-interval-theory))

(def-theorem dseq-quasi-invariance
  "forall(delta:rr,
     delta%width(delta)
       implies 
     forall(x:ii,
       #(dseq(delta)(x),ii) or #(dseq(delta)(x)+delta,ii)))"

  (proof

   (

    (unfold-single-defined-constant (0) delta%width)
    direct-and-antecedent-inference-strategy
    (contrapose "with(x_$0,y:ii,delta:rr,delta<=y-x_$0);")
    (cut-with-single-formula "(dseq(delta)(x)<x_$0 and x_$0<dseq(delta)(x)+delta) and 
                              (dseq(delta)(x)<y and y<dseq(delta)(x)+delta)")
    simplify
    (apply-macete-with-minor-premises interval-bounding-lemma)
    (cut-with-single-formula "dseq(delta)(x)<=x and x<dseq(delta)(x)+delta")
    direct-inference
    (instantiate-existential ("x"))
    simplify
    (apply-macete-with-minor-premises dseq-distance-bound)
    (apply-macete-with-minor-premises dseq-definedness)
    (apply-macete-with-minor-premises dseq-definedness)


    ))

  (theory fixed-interval-theory))


(def-theorem dseq-distance-bound-corollary
  "forall(delta:rr,
     delta%width(delta)
       implies 
     forall(x:ii,#(if(#(dseq(delta)(x),ii), dseq(delta)(x),dseq(delta)(x)+delta),ii)))"

  (proof
   (

    direct-and-antecedent-inference-strategy
    sort-definedness
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula " #(dseq(delta)(x),ii) or #(dseq(delta)(x)+delta,ii)")
    (antecedent-inference "with(p,q:prop, p or q)")
    (apply-macete-with-minor-premises dseq-quasi-invariance)


    ))


  (theory fixed-interval-theory))


(def-theorem ()
  "forall(x,y,z:ii,abs(x+[-1]*z)<=abs(x+[-1]*y)+abs(y+[-1]*z))"
  (theory fixed-interval-theory)
  (proof

   (

    (force-substitution "x+[-1]*z" "(x+[-1]*y)+(y+[-1]*z)" (0))
    (apply-macete-with-minor-premises triangle-inequality)
    simplify

    ))

  )


(def-theorem ()
  "forall(x,y:ii,abs(x+[-1]*y)=abs([-1]*x+y))"
  (theory fixed-interval-theory)
  (proof

   (

    (force-substitution "([-1]*x+y)" "[-1]*(x+[-1]*y)" (0))
    (apply-macete-with-minor-premises absolute-value-product)
    (apply-macete absolute-value-non-positive)
    simplify
    simplify



    )))


(def-theorem ()
  "forall(x,y:ii,x=y iff abs(x+[-1]*y)=0)"
  (theory fixed-interval-theory)
  (proof

   (
    (apply-macete-with-minor-premises absolute-value-zero)
    simplify
    
    )))

(include-files
 (files (imps theories/metric-spaces/uniformly-continuous-mapping-spaces)))


;;consider the pair (ii pp) as an instance of the metric space ensemble.

(def-theory mappings-from-an-interval
  (component-theories fixed-interval-theory metric-spaces))

;; Build the union theory first so that the interpretation will map 
;; metric-spaces-2-tuples into it.

(def-theorem ()
  "forall(x,y,z:ii,abs([-1]*z+x)<=abs([-1]*z+y)+abs(x+[-1]*y))"
  (theory  fixed-interval-theory)
  (proof
   (


    (force-substitution "[-1]*z+x" "([-1]*z+y)+(x+[-1]*y)" (0))
    (apply-macete-with-minor-premises triangle-inequality)
    simplify

    )))


;;Had to add this in for CLISP IMPS.

'(def-theorem ()
  "forall(x,y:ii,0<=abs(x+[-1]*y))"
  (theory  fixed-interval-theory)
  (proof
   (
    (apply-macete-with-minor-premises non-negativity-of-absolute-value)
    )))


(def-theory-ensemble-instances metric-spaces 
  force-under-quick-load
  (target-theories fixed-interval-theory metric-spaces)
  (permutations  (0) (0 1))
  (theory-interpretation-check using-simplification)
  (sorts (pp ii pp))
  (constants (dist "lambda(x,y:ii, abs(x-y))" dist))
  (special-renamings
   (ball ii%ball)
   (open%ball ii%open%ball)
   (lim ii%lim)
   (closure ii%closure)
   (uniformly%continuous uniformly%continuous%ii%pp)
   (lipschitz%bound ii%lipschitz%bound)
   (lipschitz%bound%on ii%lipschitz%bound%on)))

;;;(def-translation pointed-ms-tuples-to-mappings-from-an-interval
;;;  dont-enrich
;;;  force-under-quick-load
;;;  (source pointed-ms-2-tuples)
;;;  (target mappings-from-an-interval)
;;;  (fixed-theories h-o-real-arithmetic)
;;;  (sort-pairs (pp_0 ii) (pp_1 pp))
;;;  (constant-pairs (dist_0 "lambda(x,y:ii, abs(x-y))") (dist_1 dist) (a_0 a_0))
;;;  (theory-interpretation-check using-simplification))
;;;
;;;(def-renamer mappings-from-an-interval-renamer
;;;  (pairs 
;;;   (unif%continuous%bfun unif%continuous%bfun%ii%pp)
;;;   (ms%bfun%dist bfun%dist%ii%pp)
;;;   (ms%bfun bfun%ii%pp)))
;;;
;;;(def-transported-symbols (ms%bfun%dist ms%bfun unif%continuous%bfun)
;;;  (renamer mappings-from-an-interval-renamer)
;;;  (translation pointed-ms-tuples-to-mappings-from-an-interval)
;;;  )

(def-theory-ensemble-overloadings metric-spaces (1 2))

;;;(def-overloading dist
;;;  (mappings-from-an-interval bfun%dist%ii%pp))


(def-constant step%fn
  "lambda(f:[ii,pp],
     forsome(delta:rr,
       0<delta
        and 
       forall(x,y:ii,
         dseq(delta)(x)=dseq(delta)(y) implies f(x)=f(y))))"
  (theory mappings-from-an-interval))

(def-constant delta%step%approximant
  "lambda(delta:rr,f:[ii,pp],
      lambda(x:ii,
        f(if(#(dseq(delta)(x),ii), dseq(delta)(x),dseq(delta)(x)+delta))))"
   (theory mappings-from-an-interval))


(def-theorem delta-step-is-a-step-fn
  "forall(delta:rr,f:[ii,pp],
       delta%width(delta) and total_q{f,[ii,pp]}
                        implies 
                      step%fn(delta%step%approximant(delta,f)))"

  (proof


   (


    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (backchain-repeatedly ("with(a,b:rr,a=b)"))
    (cut-with-single-formula "#(if(#(dseq(delta)(y_$1),ii), 
              dseq(delta)(y_$1), dseq(delta)(y_$1)+delta),ii)")
    (apply-macete-with-minor-premises dseq-distance-bound-corollary)
    (unfold-single-defined-constant-globally delta%width)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential



    ))
  (theory mappings-from-an-interval))

(def-theorem step-functions-approximate
  "forall(f:[ii,pp], eps:rr, 
     0<eps and uniformly%continuous(f) and total_q{f,[ii,pp]}
      implies 
     forsome(g:[ii,pp],
      step%fn(g) and forall(x:ii, dist(f(x),g(x))<=eps)))"
  (theory mappings-from-an-interval)

  (proof


   (


    (unfold-single-defined-constant (0) uniformly%continuous%ii%pp)
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent "with(f:[ii,pp],
  forall(eps:rr,
    0<eps
     implies 
    forsome(delta:rr,
      0<delta
       and 
      forall(x,y:ii,
        #(f(x)) and #(f(y)) and abs(x-y)<=delta
         implies 
        dist(f(x),f(y))<=eps))));")
    (cut-with-single-formula "forsome(delta_1:rr, delta%width(delta_1) and delta_1<=delta)")
    (antecedent-inference "with(p:prop,forsome(delta_1:rr,p));")
    (instantiate-existential ("delta%step%approximant(delta_1,f)"))
    (apply-macete-with-minor-premises delta-step-is-a-step-fn)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) delta%step%approximant)
    (backchain "with(p:prop,forall(x,y:ii,p));")
    direct-and-antecedent-inference-strategy
    (backchain "with(f:[ii,pp],total_q{f,[ii,pp]});")
    (apply-macete-with-minor-premises commutative-law-for-addition)
    (apply-macete-with-minor-premises dseq-distance-bound-corollary)
    (unfold-single-defined-constant (0) abs)
    (cut-with-single-formula
     "dseq(delta_1)(x_$0)<=x_$0 and x_$0<dseq(delta_1)(x_$0)+delta_1")
    (prove-by-logic-and-simplification 3)
    (apply-macete-with-minor-premises dseq-distance-bound)
    (incorporate-antecedent "with(p:prop,p and p);")
    (unfold-single-defined-constant (0) delta%width)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises commutative-law-for-addition)
    (apply-macete-with-minor-premises dseq-distance-bound-corollary)
    (unfold-single-defined-constant-globally delta%step%approximant)
    (unfold-single-defined-constant (0) delta%width)
    (cut-with-single-formula "forsome(x,y:ii, x<y)")
    (instantiate-existential ("min(y-x,delta)"))
    (unfold-single-defined-constant (0) min)
    (prove-by-logic-and-simplification 3)
    (instantiate-existential ("x" "y"))
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises minimum-2nd-arg)
    (apply-macete-with-minor-premises non-degeneracy)


    )))
