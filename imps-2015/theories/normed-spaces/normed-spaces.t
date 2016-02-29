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


(herald normed-spaces)

(include-files 
 (files (imps theories/metric-spaces/metric-space-supplements)
	(imps theories/vector-spaces/vector-spaces)))


;;; Vector and normed spaces.

(def-renamer VS-RENAMER
  (pairs (vv uu)))

(def-theory-instance VECTOR-SPACES-OVER-RR
  (source vector-spaces)
  (target h-o-real-arithmetic)
  (translation fields-to-rr)
  (renamer vs-renamer))

(def-overloading +  (h-o-real-arithmetic +) (vector-spaces-over-rr ++))

(def-overloading *  (h-o-real-arithmetic *) (vector-spaces-over-rr **))

(def-constant sub_vv
  "lambda(x,y:uu,x+[-1]*y)"
  (theory vector-spaces-over-rr))

(def-algebraic-processor VECTOR-SPACE-ALGEBRAIC-PROCESSOR
  (language vector-spaces-over-rr)
  (base ((operations
	   (+ ++)
	   (* **)
	   (sub sub_vv)
	   (zero v0))))
  (coefficient rr-algebraic-processor))

(def-overloading sub (h-o-real-arithmetic sub) (vector-spaces-over-rr sub_vv))

(def-theorem sub-lemma-for-processor
  "forall(y,x:uu,x-y=x+v0-y)"
  (theory vector-spaces-over-rr)
  (proof
   (
    direct-inference-strategy
    unfold-defined-constants
    (force-substitution "x+(v0+[-1]*y)" "x+v0+[-1]*y" (0))
    (apply-macete-with-minor-premises %vector-zero-identity)
    (apply-macete-with-minor-premises %vector-plus-associativity)

    )))

(def-theorem ()
  "forall(x:uu,x+v0-x=v0)"
  (theory vector-spaces-over-rr)
  (proof
   (
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    (force-substitution "x+(v0+[-1]*x)" "x+v0+[-1]*x" (0))
    (apply-macete-with-minor-premises %vector-zero-identity)
    (force-substitution "x+[-1]*x" "(1+[-1])*x" (0))
    (force-substitution "(1+[-1])" "0" (0))
    (apply-macete-with-minor-premises tr%scalar-multiplication-by-zero)
    simplify
    (apply-macete-with-minor-premises %vector-times-right-distributivity)
    (apply-macete-with-minor-premises %scalar-multiplication-by-one)
    (apply-macete-with-minor-premises %vector-plus-associativity)

    )))



(def-theory-processors vector-spaces-over-rr
 (algebraic-simplifier (vector-space-algebraic-processor ** ++ sub_vv))
 (algebraic-term-comparator vector-space-algebraic-processor))

(def-language NORMED-LINEAR-SPACE-LANGUAGE
  (embedded-language vector-spaces-over-rr-language)
  (constants
   (norm "[uu,rr]")))

(def-theory NORMED-LINEAR-SPACES
  (language normed-linear-space-language)
  (component-theories vector-spaces-over-rr)
  (axioms
   (norm-totality
    "total_q{norm,[uu, rr]}" d-r-convergence transportable-macete)
   (positivity-of-norm
    "forall(x:uu, 0<=norm(x))" transportable-macete)
   (norm-zero
    "forall(x:uu, norm(x)=0 iff x = v0)" transportable-macete)
   (norm-scalar-multiplication
    "forall(x:uu, a:rr, norm(a**x) = abs(a) * norm(x))" transportable-macete)
   (norm-triangle-inequality
    "forall(x,y:uu, norm(x++y) <= norm(x) + norm(y))" transportable-macete)))

;; Add syntax to print "norm(x)" in TeX as "|| x ||."

(def-print-syntax norm ; An IMPS symbol name.
  tex
  (token (" \\| " " \\| "))
  (method present-tex-delimited-expression)
  (binding 80))

(def-theorem ()
  "forall(x,y,z:uu,norm(x+[-1]*z)<=norm(x+[-1]*y)+norm(y+[-1]*z))"
  (theory normed-linear-spaces)

  (proof

   (
   
    (force-substitution "x+[-1]*z" "(x+[-1]*y)+(y+[-1]*z)" (0))
    (apply-macete-with-minor-premises norm-triangle-inequality)
    simplify

    )))

(def-theorem ()
  "forall(x,y,z:uu, norm([-1]*z+x)<=norm([-1]*z+y)+norm(x+[-1]*y))"
  (theory normed-linear-spaces)
  (proof
   (


    (force-substitution "[-1]*z+x" "([-1]*z+y)+(x+[-1]*y)" (0))
    (apply-macete-with-minor-premises norm-triangle-inequality)
    simplify

    )))

(def-theorem ()
  "forall(x,y:uu,norm(x+[-1]*y)=norm([-1]*x+y))"
  (theory normed-linear-spaces)
  (proof
   (
    (force-substitution "x+[-1]*y" "[-1]*([-1]*x+y)" (0))
    (apply-macete-with-minor-premises norm-scalar-multiplication)
    (apply-macete-with-minor-premises absolute-value-non-positive)
    simplify
    simplify

    )))

(def-theorem ()
  "forall(x,y:uu,x=y iff norm(x+[-1]*y)=0)"
  (theory normed-linear-spaces)
  (proof 

   (
    (apply-macete-with-minor-premises norm-zero)
    simplify
    )))

;;;(def-theorem ()
;;;  "forall(x,y:uu,0<=norm(x+[-1]*y))"
;;;  lemma
;;;  (theory normed-linear-spaces)
;;;  (proof 
;;;
;;;   (
;;;    simplify
;;;    )))

(def-theory-ensemble-instances
 metric-spaces 
 force-under-quick-load
 (target-theories normed-linear-spaces normed-linear-spaces)
 (multiples 1 2)
 (theory-interpretation-check using-simplification)
 (sorts (pp uu uu))
 (constants (dist "lambda(x,y:uu, norm(x-y))" "lambda(x,y:uu, norm(x-y))")))

(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-theorem CLOSED-BALLS-ARE-DEFINED
 "forall(b:uu,r:rr,#(ball(b,r)))"
 (theory normed-linear-spaces)
 (usages d-r-convergence)
 (proof 

  (
   unfold-defined-constants
   simplify-insistently

   )))

(def-theorem OPEN-BALLS-ARE-DEFINED
 "forall(b:uu,r:rr,#(open%ball(b,r)))"
 (theory normed-linear-spaces)
 (usages d-r-convergence)
 (proof 
  (
   
   unfold-defined-constants
   simplify-insistently
   
   )))

(def-theorem ()
  "norm(v0)=0"
  (usages rewrite)
  (theory normed-linear-spaces)
  (proof

   (

    (apply-macete-with-minor-premises norm-zero)

    )))

(def-theorem norm-continuity-lemma
  "forall(x,y,z:uu, norm(x)-norm(y)<=norm(x-y))"
  (theory normed-linear-spaces)
  (proof
   (
    (force-substitution "norm(x)-norm(y)<=norm(x-y)" "norm((x-y)+y)<=norm(x-y)+norm(y)" (0))
    (apply-macete-with-minor-premises norm-triangle-inequality)
    simplify

    )))
;; Macetes:


(def-theorem vs-addition-of-fractions-left 
  "forall(a,b:rr,u,y:uu,a/b*u + y == (1/b)*(a*u+b*y))"
  (proof
   (

    (apply-macete-with-minor-premises %vector-times-left-distributivity)
    (force-substitution "1/b*(b*y)" "(1/b*b)*y" (0))
    direct-and-antecedent-inference-strategy
    (case-split ("b=0"))
    simplify
    simplify
    (apply-macete-with-minor-premises %vector-times-associativity)


    ))

  (theory vector-spaces-over-rr))

(def-theorem vs-addition-of-fractions-right 
 "forall(a,b:rr,u,y:uu, y+a/b*u == (1/b)*(a*u+b*y))"

 (proof
   (

    (apply-macete-with-minor-premises %vector-times-left-distributivity)
    (force-substitution "1/b*(b*y)" "(1/b*b)*y" (0))
    direct-and-antecedent-inference-strategy
    (case-split ("b=0"))
    simplify
    simplify
    (apply-macete-with-minor-premises %vector-times-associativity)


    ))

 (theory vector-spaces-over-rr))

(def-theorem sub-replacement
  "forall(x,y:uu,x-y=x+[-1]*y)"
  (proof
   (
    simplify
    ))
  (theory vector-spaces-over-rr))


(def-theorem vector-times-associativity-left
  "forall(a,b:rr,x:uu,a*(b*x)=(a*b)*x)"
  (proof
   (
    simplify
    ))
  (theory vector-spaces-over-rr))
;;;
(def-compound-macete ns-fractional-expression-manipulation
  (repeat
    vs-addition-of-fractions-right
    vs-addition-of-fractions-left
    sub-replacement
    vector-times-associativity-left
    norm-scalar-multiplication))
