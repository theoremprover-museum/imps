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


(herald pointed-metric-spaces)

(include-files
 (files (imps theories/metric-spaces/metric-space-pairs)
	(imps theories/partial-orders/real-order-properties)))


(def-language POINTED-METRIC-SPACES
  (embedded-languages metric-spaces-language)
  (constants (a_0 pp)))
      
(def-theory POINTED-METRIC-SPACES
  (component-theories metric-spaces)
  (language pointed-metric-spaces))

(def-theory mappings-into-a-pointed-metric-space
  (component-theories pointed-metric-spaces generic-theory-1))

(def-constant rad%dist
  "lambda(x:pp, dist(a_0,x))"
  (theory pointed-metric-spaces))

(def-theorem ()
  "lambda(f:[ind_1,pp], total_q{f,[ind_1,pp]} and #(sup(ran{rad%dist oo f})))(lambda(x:ind_1, a_0))"
  (proof

   (beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    beta-reduce-repeatedly ;;gr
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("rad%dist(a_0)"))
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-with-minor-premises
    beta-reduce-with-minor-premises
    beta-reduce-with-minor-premises
    (instantiate-existential ("x_$1"))
    simplify
    unfold-defined-constants
    (instantiate-existential ("rad%dist(a_0)"))
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    simplify))


  (theory mappings-into-a-pointed-metric-space))
  

(def-atomic-sort bfun
  "lambda(f:[ind_1,pp], total_q{f,[ind_1,pp]} and #(sup(ran{rad%dist oo f})))"
  (theory mappings-into-a-pointed-metric-space)
  (witness "lambda(x:ind_1, a_0)"))

(def-theorem bounded-rad-dist
  "forall(n:ind_1,x:bfun, dist(a_0,x(n))<=sup(ran{rad%dist oo x}))"
  
  (proof
   ((assume-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("dist(a_0,x(n))"))
    simplify-insistently
    (unfold-single-defined-constant (0) rad%dist)
    (instantiate-existential ("n"))
    simplify
    (backchain "forall(x:[ind_1,pp],#(x,bfun)
   iff 
  (total_q{x,[ind_1,pp]} and #(sup(ran{rad%dist oo x}))))")))

  (theory mappings-into-a-pointed-metric-space))

(def-constant bfun%dist
  "lambda(f,g:bfun, sup(ran{lambda(x:ind_1, dist(f(x),g(x)))}))"
  (theory mappings-into-a-pointed-metric-space))

(def-theorem ()
  "total_q{bfun%dist,[bfun,bfun,rr]}"
  lemma
  (proof
   ((assume-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    insistent-direct-inference
    (unfold-single-defined-constant (0) bfun%dist)
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    (instantiate-existential ("x_$0"))
    simplify
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises triangle-inequality-alternate-form)
    (instantiate-existential ("sup(ran{rad%dist oo x_0})+sup(ran{rad%dist oo x_1})"))
    (apply-macete-with-minor-premises sum-inequality-macete)
    (instantiate-existential ("a_0"))
    (apply-macete-with-minor-premises symmetry-of-distance)
    (apply-macete-with-minor-premises bounded-rad-dist)
    (apply-macete-with-minor-premises bounded-rad-dist)))

  (usages d-r-convergence)
  (theory mappings-into-a-pointed-metric-space))


(def-theorem bounded-bfun%dist
  "forall(x,y:bfun,n:ind_1 ,dist(x(n),y(n))<=bfun%dist(x,y))"
  (proof
   ((assume-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    (unfold-single-defined-constant (0) bfun%dist)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("dist(x(n),y(n))"))
    simplify-insistently (instantiate-existential ("n"))
    simplify (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly simplify
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    (instantiate-existential ("sup(ran{rad%dist oo x})+sup(ran{rad%dist oo y})"))
    (apply-macete-with-minor-premises triangle-inequality-alternate-form)
    (instantiate-existential ("a_0"))
    (apply-macete-with-minor-premises sum-inequality-macete)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises symmetry-of-distance)
    (apply-macete-with-minor-premises bounded-rad-dist)
    (apply-macete-with-minor-premises bounded-rad-dist)))

  (usages transportable-macete)
  (theory  mappings-into-a-pointed-metric-space))
  

(def-theorem ()
  "forall(x,y,z:bfun, bfun%dist(x,z)<=bfun%dist(x,y)+bfun%dist(y,z))"
  lemma
  (proof
   ((unfold-single-defined-constant (0) bfun%dist)
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises triangle-inequality-alternate-form)
    (instantiate-existential ("y(n_$0)"))
    (apply-macete-with-minor-premises sum-inequality-macete)
    (apply-macete-with-minor-premises bounded-bfun%dist)
    (assume-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    (assume-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    simplify
    auto-instantiate-existential))

  (theory  mappings-into-a-pointed-metric-space))

(def-theorem ()
  "forall(x,y:bfun, bfun%dist(x,y)=bfun%dist(y,x))"

  (proof
   ((unfold-single-defined-constant (0 1) bfun%dist)
    (apply-macete-locally symmetry-of-distance (0) " dist(x(x_$0),y(x_$0)) ")
    simplify
    (assume-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    (cut-with-single-formula "total_q{bfun%dist,[bfun,bfun,rr]}")
    (incorporate-antecedent "total_q{bfun%dist,[bfun,bfun,rr]}")
    (unfold-single-defined-constant (0) bfun%dist)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "total_q{lambda(f,g:bfun,
          sup(ran{lambda(x:ind_1,dist(f(x),g(x)))})),[bfun,bfun,rr]}"
				      ("y" "x"))
    (beta-reduce-antecedent
     "with(x,y:bfun,
       #(lambda(f_$0,g_$0:bfun,
          sup(ran{lambda(x_$0:ind_1,dist(f_$0(x_$0),g_$0(x_$0)))})) (y,x)))")
    insistent-direct-inference))

  (theory  mappings-into-a-pointed-metric-space))

(def-theorem ()
  "forall(x,y:bfun, 0<=bfun%dist(x,y))"


  (proof
   (direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) bfun%dist)
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("dist(x(x_$0),y(x_$0))"))
    (assume-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    simplify
    (instantiate-existential ("x_$0"))
    simplify
    (assume-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    simplify
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    (instantiate-existential ("bfun%dist(x,y)"))
    (apply-macete-with-minor-premises bounded-bfun%dist)))

  (theory  mappings-into-a-pointed-metric-space))

(def-theorem ()
  "forall(x,y:bfun, x=y iff bfun%dist(x,y)=0)"
  (theory  mappings-into-a-pointed-metric-space)

  (proof
   ((assume-theorem bfun-defining-axiom_mappings-into-a-pointed-metric-space)
    direct-and-antecedent-inference-strategy
    (force-substitution "y" "x" (0))
    (weaken (0))
    (unfold-single-defined-constant (0) bfun%dist)
    (apply-macete-with-minor-premises zero-self-distance)
    (weaken (0))
    (cut-with-single-formula "forall(x,y:rr,x<=y and y<=x implies x=y)")
    (backchain "forall(x,y:rr,x<=y and y<=x implies x=y);")
    direct-and-antecedent-inference-strategy
    (weaken (0))
    (apply-macete-with-minor-premises tr%lub-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%prec%majorizes%characterization)
    beta-reduce-repeatedly
    simplify
    (weaken (0))
    (apply-macete-with-minor-premises tr%prec%sup-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%non-empty-range)
    beta-reduce-repeatedly
    (weaken (0))
    (instantiate-existential ("0"))
    (weaken (0 1))
    (apply-macete-with-minor-premises tr%minorizes-property-of-prec%sup)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("0"))
    simplify-insistently
    (weaken (0))
    simplify
    extensionality
    direct-and-antecedent-inference-strategy
    (force-substitution "x(x_0)==y(x_0)" "dist(x(x_0),y(x_0))<=bfun%dist(x,y)" (0))
    (apply-macete-with-minor-premises bounded-bfun%dist)
    (force-substitution "x(x_0)==y(x_0)" "x(x_0)=y(x_0)" (0))
    (apply-macete-with-minor-premises point-separation-for-distance)
    direct-and-antecedent-inference-strategy
    simplify
    simplify)))
