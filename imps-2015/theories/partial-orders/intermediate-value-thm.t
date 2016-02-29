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


(herald real-intervals)

(load-section foundation)
(load-section partial-orders)

(include-files
  (files 
   (imps theories/partial-orders/induction-in-cpos)
   (imps theories/partial-orders/real-intervals)))

(def-constant continuous%at%point%rr
  "lambda(f:[rr,rr], x:rr ,forall(eps:rr,0<eps 
       implies 
  forsome(delta:rr,0<delta 
        and forall(y:rr,abs(x-y)<=delta implies abs(f(x)-f(y))<=eps))))"
  (theory h-o-real-arithmetic))

(def-theorem ivt-sup-property-of-continuity
  "forall(f:[rr,rr],x,a:rr,s:sets[rr],
     continuous%at%point%rr(f,sup(s))
      and 
     forall(x:rr,x in s implies f(x)<=a)
      implies 
     f(sup(s))<=a)"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally continuous%at%point%rr)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(sup(s)) and #(f(sup(s)))")
    (move-to-sibling 1)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(r:rr,with(f:[[rr,rr],rr,prop],f)(with(f:[rr,rr],f),r));")
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,
  forall(eps:rr,0<eps implies forsome(delta:rr,p)));"
				      ("1"))
    (simplify-antecedent "with(p:prop,not(p));")
    (instantiate-universal-antecedent "with(delta,r:rr,forall(y:rr,r<=delta implies r<=1));"
				      ("sup(s)"))
    (contrapose "with(p:prop,not(p));")
    (unfold-single-defined-constant-globally abs)
    simplify
    (incorporate-antecedent "with(r:rr,with(f:[[rr,rr],rr,prop],f)(with(f:[rr,rr],f),r));")
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,
  forall(eps:rr,0<eps implies forsome(delta:rr,p)));")
    (instantiate-existential ("(f(sup(s))-a)/2"))
    simplify
    (cut-with-single-formula "forsome(x:rr, x in s and sup(s)-delta_$0<x)")
    (instantiate-existential ("x"))
    (apply-macete-with-minor-premises absolute-value-non-negative)
    simplify
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x"))
    simplify
    (cut-with-single-formula "f(x)<=a")
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises absolute-value-non-negative)
    simplify
    (apply-macete-with-minor-premises sup-minus-epsilon-corollary)
    direct-and-antecedent-inference-strategy
    )))

(def-theorem lower-semicontinuity-of-continuous
  "forall(f:[rr,rr],x,a:rr,
            continuous%at%point%rr(f,x)
             and
            f(x)<a
             implies
            forsome(x_0:rr, x<x_0 and forall(y:rr,x<=y and y<=x_0 implies f(y)<a)))"
  (theory h-o-real-arithmetic)
  (proof 
   (


    (unfold-single-defined-constant-globally continuous%at%point%rr)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,p));"
				      ("(a-f(x))/2"))
    (simplify-antecedent "with(p:prop,not(p));")
    (instantiate-existential ("x+delta_$0"))
    simplify
    (instantiate-universal-antecedent "with(p:prop,forall(y_$0:rr,p));" ("y_$0"))
    (contrapose "with(p:prop,not(p));")
    (apply-macete-with-minor-premises absolute-value-non-positive)
    simplify
    (cut-with-single-formula "f(x)<=f(y_$0) or f(y_$0)<=f(x)")
    (move-to-sibling 1)
    simplify
    (incorporate-antecedent "with(r:rr,r<=r);")
    (antecedent-inference "with(p:prop,p or p);")
    (apply-macete-with-minor-premises absolute-value-non-positive)
    simplify
    (apply-macete-with-minor-premises absolute-value-non-negative)
    simplify

    )))

  

(def-theorem intermediate-value-theorem
  "forall(f:[rr,rr], a,b:rr, 
               a<=b
                 and 
               forall(x:rr, a<=x and x<=b implies continuous%at%point%rr(f,x))
                 and
               f(a)<0
                 and
               0<f(b) 
                 implies
               forsome(z:rr, a<=z and z<=b and f(z)=0))"
  (theory fixed-interval-theory)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (contrapose "with(r:rr,0<r);")
    (cut-with-single-formula "forall(x:rr, a<=x and x<=b implies f(x)<=0)")
    (instantiate-universal-antecedent "with(r:rr,p:prop,forall(x:rr,p and p implies r<=0));"
				      ("b"))
    (simplify-antecedent "with(p:prop,not(p));")
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(x:rr, a<=x implies x in indic{z:rr,z<=b implies f(z)<=0})")
    (incorporate-antecedent "with(f:sets[rr],a:rr,forall(x:rr,a<=x implies x in f));")
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,a:rr,forall(x:rr,a<=x implies (p implies p)));")
    simplify
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%induction-in-cpos)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("a"))
    simplify-insistently
    simplify-insistently
    (apply-macete-with-minor-premises ivt-sup-property-of-continuity)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(x:rr,p implies p));")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-inference
    (instantiate-existential ("a"))
    simplify
    (antecedent-inference "with(p:prop,p and p and p);")
    (incorporate-antecedent "with(f,t_$0:sets[rr],t_$0 subseteq f);")
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,t_$0:sets[rr],
  forall(x_$1:rr,x_$1 in t_$0 implies (p implies p)));")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("sup(t_$0)"))
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-inference
    (instantiate-existential ("x_$1"))
    simplify
    (case-split ("b<=y_$1"))
    (instantiate-existential ("z_$0"))
    simplify-insistently
    simplify
    simplify
    (cut-with-single-formula "f(y_$1)<=0 and not(f(y_$1)=0)")
    (move-to-sibling 1)
    direct-and-antecedent-inference-strategy
    (antecedent-inference "with(p:prop,p and p and p and p);")
    (incorporate-antecedent "with(y_$1:rr,f:[rr,rr],b:rr,
  y_$1 in indic{z:rr,  z<=b implies f(z)<=0});")
    simplify-insistently
    (backchain "with(p:prop,forall(z:rr,p or p or p));")
    simplify
    (cut-with-single-formula "y_$1<b and f(y_$1)<0")
    (move-to-sibling 1)
    simplify
    (weaken (2 1))
    (cut-with-single-formula
     "forsome(x_0:rr, y_$1<x_0 and forall(y:rr,y_$1<=y and y<=x_0 
                       implies
                      f(y)<0))")
    (antecedent-inference-strategy (0))
    simplify-insistently
    (cut-with-single-formula
     "forsome(w:rr, y_$1<w and w<=x_0 and w<=z_$0 and w<=b)")
    (instantiate-existential ("w"))
    (instantiate-universal-antecedent
     "with(r:rr,p:prop,forall(y:rr,p and p implies r<0));"
     ("w"))
    (simplify-antecedent "with(p:prop,not(p));")
    simplify
    simplify
    simplify
    (instantiate-existential ("min(x_0,min(z_$0,b))"))
    unfold-defined-constants
    (case-split ("z_$0<=b"))
    simplify
    (case-split ("x_0<=z_$0"))
    simplify
    simplify
    simplify
    (case-split ("x_0<=b"))
    simplify
    simplify
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("min(z_$0,b)"))
    (apply-macete-with-minor-premises minimum-2nd-arg)
    (apply-macete-with-minor-premises minimum-1st-arg)
    (apply-macete-with-minor-premises transitivity-of-<=)
    (instantiate-existential ("min(z_$0,b)"))
    (apply-macete-with-minor-premises minimum-2nd-arg)
    (apply-macete-with-minor-premises minimum-2nd-arg)
    (apply-macete-with-minor-premises lower-semicontinuity-of-continuous)
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,forall(x:rr,p implies p));")
    simplify    

    )))
  

