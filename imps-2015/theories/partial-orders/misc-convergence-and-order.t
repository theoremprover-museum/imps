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


(herald misc-convergence-and-order)

(include-files
 (files 
  (imps theories/partial-orders/convergence-and-order)))


(def-constant discrete%set
  "lambda(s:sets[rr], forsome(a:rr,0<a and forall(x,y:rr, x<y implies a<=y-x)))"
  (theory h-o-real-arithmetic))

(def-theorem discrete-sets-contain-sup-lemma
  "forall(s:sets[rr], discrete%set(s) and #(sup(s)) implies
          forsome(a:rr,0<a and forall(x:rr, x in s implies x=sup(s) or x<=sup(s)-a)))"

  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant (0) discrete%set)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (cut-with-single-formula "forsome(z:rr, z in s and x<z and sup(s)-a<=z and z<=sup(s))")
    (antecedent-inference "with(a,x:rr,s:sets[rr],
  forsome(z:rr,
    z in s and x<z and sup(s)-a<=z and z<=sup(s)));")
    (instantiate-universal-antecedent "with(a:rr,forall(x,y:rr,x<y implies a<=y-x));" ("x" "z"))
    simplify
    (cut-with-single-formula "forall(z:rr, z<sup(s) implies forsome(x:rr, x in s and z<x))")
    (instantiate-universal-antecedent "with(s:sets[rr],
  forall(z:rr,
    z<sup(s) implies forsome(x:rr,x in s and z<x)));" ("max(x,sup(s)-a)"))
    (contrapose "with(a:rr,s:sets[rr],x:rr,not(max(x,sup(s)-a)<sup(s)));")
    (weaken (0))
    (cut-with-single-formula "x<=sup(s)")
    (unfold-single-defined-constant (0) max)
    (case-split-on-conditionals (0))
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-inference
    (instantiate-existential ("x"))
    simplify
    (instantiate-existential ("x_$0"))
    (cut-with-single-formula "x<=max(x,sup(s)-a)")
    simplify
    (apply-macete-with-minor-premises maximum-1st-arg)
    (cut-with-single-formula "sup(s)-a<=max(x,sup(s)-a)")
    simplify
    (apply-macete-with-minor-premises maximum-2nd-arg)
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-inference
    (instantiate-existential ("x_$0"))
    simplify
    direct-and-antecedent-inference-strategy
    (force-substitution "z" "sup(s)-(sup(s)-z)" (0))
    (apply-macete-with-minor-premises sup-minus-epsilon-corollary)
    simplify
    simplify
    )))



(def-theorem empty-indic-sup-is-undefined
  "not(#(sup(empty_indic{rr})))"
  (theory h-o-real-arithmetic)
  (proof

   (
    

    (cut-with-single-formula " #(sup(empty_indic{rr})) implies sup(empty_indic{rr})<=sup(empty_indic{rr})-1")
    (antecedent-inference "with(p,q:prop, p implies q)")
    (simplify-antecedent "sup(empty_indic{rr})<=sup(empty_indic{rr})-1;")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) majorizes)
    direct-and-antecedent-inference-strategy
    (contrapose "with(x_$0:rr,x_$0 in empty_indic{rr});")
    simplify-insistently

    )))

;;;(def-theorem discrete-sets-contain-sup-lemma
;;;  "forall(s:sets[rr], discrete%set(s) and #(sup(s)) implies
;;;          forsome(a:rr,0<a and forall(x:rr, x in s implies x=sup(s) or x<=sup(s)-a)))"
;;;
;;;  (theory h-o-real-arithmetic)
;;;  (proof
;;;   (
;;;    (unfold-single-defined-constant (0) discrete%set)
;;;    direct-and-antecedent-inference-strategy
;;;    auto-instantiate-existential
;;;    (cut-with-single-formula "forsome(z:rr, z in s and x<z and sup(s)-a<=z and z<=sup(s))")
;;;    (antecedent-inference "with(a,x:rr,s:sets[rr],
;;;  forsome(z:rr,
;;;    z in s and x<z and sup(s)-a<=z and z<=sup(s)));")
;;;    (instantiate-universal-antecedent "with(a:rr,forall(x,y:rr,x<y implies a<=y-x));" ("x" "z"))
;;;    simplify
;;;    (cut-with-single-formula "forall(z:rr, z<sup(s) implies forsome(x:rr, x in s and z<x))")
;;;    (instantiate-universal-antecedent "with(s:sets[rr],
;;;  forall(z:rr,
;;;    z<sup(s) implies forsome(x:rr,x in s and z<x)));" ("max(x,sup(s)-a)"))
;;;    (contrapose "with(a:rr,s:sets[rr],x:rr,not(max(x,sup(s)-a)<sup(s)));")
;;;    (weaken (0))
;;;    (cut-with-single-formula "x<=sup(s)")
;;;    (unfold-single-defined-constant (0) max)
;;;    (case-split-on-conditionals (0))
;;;    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
;;;    direct-inference
;;;    (instantiate-existential ("x"))
;;;    simplify
;;;    (instantiate-existential ("x_$0"))
;;;    (cut-with-single-formula "x<=max(x,sup(s)-a)")
;;;    simplify
;;;    (apply-macete-with-minor-premises maximum-1st-arg)
;;;    (cut-with-single-formula "sup(s)-a<=max(x,sup(s)-a)")
;;;    simplify
;;;    (apply-macete-with-minor-premises maximum-2nd-arg)
;;;    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
;;;    direct-inference
;;;    (instantiate-existential ("x_$0"))
;;;    simplify
;;;    direct-and-antecedent-inference-strategy
;;;    (force-substitution "z" "sup(s)-(sup(s)-z)" (0))
;;;    (apply-macete-with-minor-premises sup-minus-epsilon-corollary)
;;;    simplify
;;;    simplify
;;;    )))



(def-theorem discrete-sets-contain-sup
  "forall(s:sets[rr], discrete%set(s) and #(sup(s)) implies sup(s) in s)"
  (theory h-o-real-arithmetic)

  (proof

   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(a:rr,0<a and forall(x:rr, x in s implies x=sup(s) or x<=sup(s)-a))")
    (antecedent-inference "with(s:sets[rr],
  forsome(a:rr,
    0<a
     and 
    forall(x:rr,x in s implies x=sup(s) or x<=sup(s)-a)));")
    (antecedent-inference "with(s:sets[rr],a:rr,
  0<a
   and 
  forall(x:rr,x in s implies x=sup(s) or x<=sup(s)-a));")
    (contrapose "with(s:sets[rr],discrete%set(s));")
    (cut-with-single-formula "sup(s)<=sup(s)-a")
    (contrapose "with(a:rr,s:sets[rr],sup(s)<=sup(s)-a);")
    simplify
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-inference
    (unfold-single-defined-constant (0) majorizes)
    direct-and-antecedent-inference-strategy
    (backchain "with(a:rr,s:sets[rr],
  forall(x:rr,x in s implies x=sup(s) or x<=sup(s)-a));")
    direct-and-antecedent-inference-strategy
    (contrapose "with(s:sets[rr],not(sup(s) in s));")
    (backchain-backwards "with(s:sets[rr],x_$0:rr,x_$0=sup(s));")
    (apply-macete-with-minor-premises discrete-sets-contain-sup-lemma)
    direct-and-antecedent-inference-strategy

    )))


(def-constant preceding
  "lambda(s:sets[rr],a:rr, sup(indic{x:rr,x in s and x<a}))"
  (theory h-o-real-arithmetic))

(def-theorem preceding-for-discrete-sets
  "forall(s:sets[rr], x:rr, discrete%set(s) and #(preceding(s,x)) implies preceding(s,x) in s)"

  (proof

   (

    (unfold-single-defined-constant (0 1) preceding)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(a,b:sets[rr],sup(a) in a and a subseteq b implies sup(a) in b)")
    (backchain "forall(a,b:sets[rr],sup(a) in a and a subseteq b implies sup(a) in b)")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises discrete-sets-contain-sup)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(s:sets[rr],discrete%set(s));")
    unfold-defined-constants
    simplify-insistently
    simplify


    ))

  (theory h-o-real-arithmetic))

(def-theorem preceding-defined
  "forall(s:sets[rr], x:rr,  #(preceding(s,x)) iff forsome(y:rr, y in s and y<x))"
  (theory h-o-real-arithmetic)
  (proof

   (

    (unfold-single-defined-constant (0) preceding)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(s:sets[rr], s =empty_indic{rr} implies not(#(sup(s))))")
    (contrapose "with(t:rr, #(t))")
    (backchain "forall(s:sets[rr],s=empty_indic{rr} implies not(#(sup(s))));")
    simplify-insistently
    extensionality
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(x:rr,s:sets[rr],forall(y:rr,not(y in s) or not(y<x)));" ("x_0"))
    simplify
    simplify
    direct-and-antecedent-inference-strategy
    (backchain "with(s_$0:sets[rr],s_$0=empty_indic{rr});")
    (apply-macete-with-minor-premises empty-indic-sup-is-undefined)

    ;;Finishes half the proof.

    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    simplify-insistently
    auto-instantiate-existential
    (instantiate-existential ("x"))
    (unfold-single-defined-constant (0) majorizes)
    simplify-insistently


    )))


