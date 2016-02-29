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


(herald more-convergence-and-order)

(include-files
 (files (imps theories/partial-orders/misc-convergence-and-order)))


(def-theorem ()
  "<= = lambda(a,b:rr,a<=b)"
  (theory h-o-real-arithmetic)
  (proof

   (

    extensionality
    simplify

    )))

(def-theorem ()
  "forall(a,c:rr,forsome(b:rr,b<=a and c<=b) implies c<=a)"
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-and-antecedent-inference-strategy
    simplify


    )))

(def-theorem ()
  "forall(p:[rr,prop],
      nonvacuous_q{p}
       and 
     forsome(alpha:rr,
       forall(theta:rr,p(theta) implies alpha<=theta))
      implies 
     forsome(gamma:rr,
       forall(theta:rr,p(theta) implies gamma<=theta)
        and 
       forall(gamma_1:rr,
         forall(theta:rr,p(theta) implies gamma_1<=theta)
          implies 
         gamma_1<=gamma)))"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (
    (apply-macete-with-minor-premises tr%unfolded-completeness-from-below-condition)
    )))

(def-translation complete-partial-order-to-h-o-real-arithmetic-reverse
  force-under-quick-load
  (source complete-partial-order)
  (target h-o-real-arithmetic)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs
   (prec ">=")
   (prec%sup inf)
   (prec%majorizes minorizes)
   (rev%prec <=))
  (sort-pairs (uu rr))
  (theory-interpretation-check using-simplification))
   

(def-theorem inf-plus-epsilon
  "forall(s:sets[rr],eps:rr,0<eps implies not(inf(s)+eps minorizes s))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(inf(s)) or not(#(inf(s)))")
    (antecedent-inference "with(s:sets[rr],#(inf(s)) or not(#(inf(s))));")
    (cut-with-single-formula "not(inf(s)>=inf(s)+eps)")
    (contrapose "with(eps:rr,s:sets[rr],not(inf(s)>=inf(s)+eps));")
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    simplify)))


(def-theorem inf-plus-epsilon-corollary
  "forall(s:sets[rr],eps:rr, 0<eps and #(inf(s)) implies forsome(x:rr, x in s and x < inf(s)+eps))"
  
  (proof
   
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not(inf(s)+eps minorizes s)")
    (contrapose "with(eps:rr,s:sets[rr],not(inf(s)+eps minorizes s));")
    (unfold-single-defined-constant (0) minorizes)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p,q:prop,forall(x:rr,p or q))" ("x_$0"))
    simplify
    (apply-macete-with-minor-premises inf-plus-epsilon)


    )   

   )

  (theory h-o-real-arithmetic))

(def-theorem inf-defined-implies-non-empty
  "forall(s:sets[rr],#(inf(s)) implies forsome(x:rr, x in s))"
  
  (theory h-o-real-arithmetic)
  (proof

   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(s:sets[rr],#(inf(s)));")
    (cut-with-single-formula "#(inf(s)) implies inf(s)>=inf(s)+1")
    (antecedent-inference "with(p,q:prop, p implies q)")
    (simplify-antecedent "with(s:sets[rr],inf(s)>=inf(s)+1);")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) minorizes)
    direct-and-antecedent-inference-strategy
    )))



(def-theorem discrete-sets-contain-inf
  "forall(s:sets[rr], discrete%set(s) and #(inf(s)) implies inf(s) in s)"
  (theory h-o-real-arithmetic)

  (proof

   (

    (unfold-single-defined-constant (0) discrete%set)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(x:rr, x in s and x<inf(s)+a)")
    (antecedent-inference "with(a:rr,s:sets[rr],forsome(x:rr,x in s and x<inf(s)+a));")
    (cut-with-single-formula "x=inf(s) or inf(s)<x")
    (antecedent-inference "with(s:sets[rr],x:rr,x=inf(s) or inf(s)<x);")
    simplify
    (cut-with-single-formula "with(x:rr,s:sets[rr],forsome(y:rr,y in s and y<x));")
    (antecedent-inference "with(x:rr,s:sets[rr],forsome(y:rr,y in s and y<x));")
    (instantiate-universal-antecedent "with(a:rr,forall(x,y:rr,x<y implies a<=y-x));" ("y" "x"))
    (cut-with-single-formula "y>=inf(s)")
    (simplify-antecedent "with(s:sets[rr],y:rr,y>=inf(s));")
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("y"))
    simplify
    (force-substitution "x" "inf(s)+(x-inf(s))" (0))
    (apply-macete-with-minor-premises inf-plus-epsilon-corollary)
    direct-and-antecedent-inference-strategy
    simplify
    simplify
    (cut-with-single-formula "inf(s)<=x")
    simplify
    (force-substitution "inf(s)<=x" "x>=inf(s)" (0))
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x"))
    simplify
    (unfold-single-defined-constant (0) >=)
    (apply-macete-with-minor-premises inf-plus-epsilon-corollary)
    direct-and-antecedent-inference-strategy

    )))

(def-constant next
  "lambda(s:sets[rr],a:rr, inf(indic{x:rr,x in s and a<x}))"
  (theory h-o-real-arithmetic))

(def-theorem next-for-discrete-sets
  "forall(s:sets[rr], x:rr, discrete%set(s) and #(next(s,x)) implies next(s,x) in s)"

  (proof

   (

    (unfold-single-defined-constant (0 1) next)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(a,b:sets[rr],inf(a) in a and a subseteq b implies inf(a) in b)")
    (backchain "forall(a,b:sets[rr],inf(a) in a and a subseteq b implies inf(a) in b)")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises discrete-sets-contain-inf)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(s:sets[rr],discrete%set(s));")
    unfold-defined-constants
    simplify-insistently
    simplify

    ))

  (theory h-o-real-arithmetic))

(def-theorem next-definedness-condition
  "forall(s:sets[rr], x:rr,  #(next(s,x)) iff forsome(y:rr, y in s and x<y))"
  
  (proof

   (

    (unfold-single-defined-constant (0) next)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(y:rr, y in indic{x_$1:rr,  x_$1 in s and x<x_$1})")
    (antecedent-inference "with(x:rr,s:sets[rr],
  nonempty_indic_q{indic{x_$1:rr,  x_$1 in s and x<x_$1}});")
    (instantiate-existential ("y"))
    (contrapose "with(y,x:rr,s:sets[rr],
  y in indic{x_$1:rr,  x_$1 in s and x<x_$1});")
    simplify-insistently
    (contrapose "with(y,x:rr,s:sets[rr],
  y in indic{x_$1:rr,  x_$1 in s and x<x_$1});")
    simplify-insistently
    (apply-macete-with-minor-premises inf-defined-implies-non-empty)

    ;; The second branch:

    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    simplify-insistently
    auto-instantiate-existential
    (instantiate-existential ("x"))
    (unfold-single-defined-constant (0) minorizes)
    simplify-insistently


    ))

   (theory h-o-real-arithmetic))



