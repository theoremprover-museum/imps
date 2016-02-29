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

(def-language language-for-fixed-interval-theory
  (embedded-languages h-o-real-arithmetic)
  (sorts (ii rr)))

(def-theory fixed-interval-theory
  (component-theories h-o-real-arithmetic)
  (language language-for-fixed-interval-theory)
  (axioms
   (interval-characterization
    "forall(a,b:ii,x:rr, a<=x and x<=b implies #(x,ii))")
   (non-degeneracy
    "forsome(x,y:ii, x<y)")))

(def-theorem interval-bounding-lemma
  "forall(x,y:rr, c,d :ii, 
          not(#(x,ii)) and not(#(y,ii)) and x<=c and c<=y 
            implies 
          x<d  and d<y)"
         
  ;; If reals not in the interval surround one element of the 
  ;; interval then they surround them all.

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

(def-theorem ()
  "forall(a,c:ii,forsome(b:ii,a<=b and b<=c) implies a<=c)"
  (theory fixed-interval-theory)
  lemma
  (proof
   (
    
    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises transitivity-of-<=)
    auto-instantiate-existential
    )))


(def-theorem ()
  "forall(p:[ii,prop],
     nonvacuous_q{p}
      and 
     forsome(alpha:ii,
       forall(theta:ii,p(theta) implies theta<=alpha))
      implies 
     forsome(gamma:ii,
       forall(theta:ii,p(theta) implies theta<=gamma)
        and 
       forall(gamma_1:ii,
         forall(theta:ii,p(theta) implies theta<=gamma_1)
          implies 
         gamma<=gamma_1)))"
  (theory fixed-interval-theory)
  lemma
  (proof
   (
    
    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises completeness)
    (instantiate-theorem completeness ("p"))
    (instantiate-universal-antecedent "with(p:prop,forall(x_0:rr,not(p)));" ("x_0"))
    (instantiate-universal-antecedent "with(p:prop,forall(alpha:rr,forsome(theta:rr,p)));"
				      ("alpha"))
    (contrapose "with(p:prop,not(p));")
    simplify
    (instantiate-existential ("gamma"))
    simplify
    simplify
    (apply-macete-with-minor-premises interval-characterization)
    (instantiate-universal-antecedent "with(gamma:rr,p:[ii,prop],
  forall(theta:rr,p(theta) implies theta<=gamma));"
				      ("x_0"))
    (instantiate-universal-antecedent "with(gamma:rr,p:prop,
  forall(gamma_1:rr,
    forall(theta:rr,p) implies gamma<=gamma_1));"
				      ("alpha"))
    (simplify-antecedent "with(p:prop,not(p));")
    (instantiate-existential ("alpha" "x_0"))

    )))

(def-translation cpo-to-fixed-interval-theory
  force-under-quick-load
  (source complete-partial-order)
  (target fixed-interval-theory)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs
   (prec "lambda(x,y:ii,x<=y)")
   (rev%prec "lambda(a,b:ii,b<=a)"))
  (sort-pairs (uu ii))
  (theory-interpretation-check using-simplification))



