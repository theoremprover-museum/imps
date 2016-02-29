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


(herald interval-in-cpos)

;; This is a theory of intervals in cpos.

(def-language language-for-interval-in-cpo
  (embedded-languages complete-partial-order)
  (constants 
   (bot uu)
   (top uu)))

(def-theory interval-in-cpo
  (component-theories complete-partial-order)
  (language language-for-interval-in-cpo)
  (axioms
   (non-triviality "bot prec top")))

(def-theorem ()
  "lambda(x:uu,bot prec x and x prec top)(bot)"
  (theory interval-in-cpo)
  (proof
   (
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises prec-reflexivity)
    (apply-macete-with-minor-premises non-triviality)
    )))

(def-atomic-sort ii
  "lambda(x:uu, bot prec x and x prec top)"
  (theory interval-in-cpo)
  (witness "bot"))

(def-theorem ()
  "forall(a,c:ii,
    forsome(b:ii,a prec b and b prec c) implies a prec c)"
  lemma
  (theory interval-in-cpo)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prec-transitivity)
    auto-instantiate-existential
    )))

(def-theorem cpo-interval-characterization
  "forall(a,b:ii,x:uu, a prec x and x prec b implies #(x,ii))"
  (theory interval-in-cpo)
  (proof
   (
    
    
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises ii-defining-axiom_interval-in-cpo)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prec-transitivity)
    (instantiate-existential ("a"))
    (cut-with-single-formula "#(a,ii)")
    (incorporate-antecedent "with(a:ii,#(a,ii));")
    (apply-macete-with-minor-premises ii-defining-axiom_interval-in-cpo)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises prec-transitivity)
    (instantiate-existential ("b"))
    (cut-with-single-formula "#(b,ii)")
    (incorporate-antecedent "with(b:ii,#(b,ii));")
    (apply-macete-with-minor-premises ii-defining-axiom_interval-in-cpo)
    direct-and-antecedent-inference-strategy
    )))



(def-theorem ()
  "forall(p:[ii,prop],
    nonvacuous_q{p}
      and 
     forsome(alpha:ii,
       forall(theta:ii,p(theta) implies theta prec alpha))
      implies 
     forsome(gamma:ii,
       forall(theta:ii,p(theta) implies theta prec gamma)
        and 
       forall(gamma_1:ii,
         forall(theta:ii,p(theta) implies theta prec gamma_1)
          implies 
         gamma prec gamma_1)))"
  lemma
  (theory interval-in-cpo)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem prec-completeness ("lambda(x:ii,p(x))"))
    (simplify-antecedent "with(p:prop,forall(x_0:uu,not(p)));")
    (instantiate-universal-antecedent "with(p:prop,forall(x_$1:ii,not(p)));"
				      ("x_0"))
    (instantiate-universal-antecedent "with(p:prop,forall(alpha:uu,forsome(theta:uu,p)));"
				      ("with(alpha:ii, alpha)"))
    (contrapose "with(p:prop,not(p));")
    (backchain "with(p:prop,forall(theta:ii,p implies p));")
    (cut-with-single-formula "#(gamma,ii)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises cpo-interval-characterization)
    (instantiate-existential ("alpha" "x_0"))
    (backchain "with(gamma:uu,p:prop,
  forall(theta:uu,
    lambda(x:ii,p)(theta) implies theta prec gamma));")
    beta-reduce-repeatedly
    (backchain "with(gamma:uu,p:prop,
  forall(gamma_1:uu,
    forall(theta:uu,p) implies gamma prec gamma_1));")
    direct-and-antecedent-inference-strategy
    (backchain "with(alpha:ii,p:[ii,prop],
  forall(theta:ii,p(theta) implies theta prec alpha));")
    (instantiate-existential ("gamma"))
    (backchain "with(gamma:uu,p:prop,
  forall(theta:uu,
    lambda(x:ii,p)(theta) implies theta prec gamma));")
    beta-reduce-repeatedly
    simplify    )))

(def-translation relativize-to-interval
  force-under-quick-load
  (source complete-partial-order)
  (target interval-in-cpo)
  (fixed-theories h-o-real-arithmetic)
  (constant-pairs
   (prec "lambda(x,y:ii, x prec y)"))
  (sort-pairs (uu ii))
  (theory-interpretation-check using-simplification))




   
