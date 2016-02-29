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

;;; In this exercise we define the limit operator on sequences of real
;;; numbers and prove a few facts about limits.  lim%rr is defined 
;;; using the iota constructor. Notice that a separate definition
;;; of the domain of limit is not needed.

(def-constant lim%rr
   "lambda(s:[zz,rr],
     iota(x:rr,
       forall(eps:rr,
         0<eps
          implies 
         forsome(n:zz,
           forall(p:zz,n<=p implies abs(x-s(p))<=eps)))))"
  (theory h-o-real-arithmetic))

(def-theorem ()
  "forall(x:rr, abs(0)=0)"
  (usages rewrite)
  (proof
   (
    (unfold-single-defined-constant (0) abs)
    (prove-by-logic-and-simplification 3)
    ))
  (theory h-o-real-arithmetic))

;;; The first thing we need is an iota-free characterization of lim%rr. We first
;;; prove the following lemma:

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
    simplify
    (instantiate-universal-antecedent "with(p:prop,p);" ("abs(x-y)/3"))
    (contrapose "with(p:prop,p);")
    (block 
      (script-comment "prove 0<abs(x-y)/3 provided x is different from y.")
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
       
      (while 
       (matches? "with(p:prop,p)" "with(p:prop,forall(eps:rr,0<eps implies p))")
       (instantiate-universal-antecedent 
	"with(p:prop,forall(eps:rr,0<eps implies forsome(n:zz,p)));" ("r")))
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

;;; Prove the following. Use the fact #(lim%rr(s)) is equivalent to 
;;; lim%rr(s)=lim%rr(s) and the iota-free characterization of lim%rr.

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


    )))

;;; In the following proof replace the block by an appropriate script taking arguments.
;;; Each argument can be a string.

(def-theorem homogeneity-of-real-limit
  "forall(a:[zz,rr], b:rr, #(lim%rr(a)) implies 
          lim%rr(lambda(n:zz,b*a(n)))=b*lim%rr(a))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy

    (block
      (cut-with-single-formula "forsome(s:rr, lim%rr(a)=s)")
      (antecedent-inference "with(a:[zz,rr],forsome(s:rr,lim%rr(a)=s));")
      (backchain "with(s:rr,a:[zz,rr],lim%rr(a)=s);")
      (apply-macete-with-minor-premises characterization-of-real-limit)
      direct-and-antecedent-inference-strategy)

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

