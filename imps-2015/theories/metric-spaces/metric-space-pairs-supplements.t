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


(herald metric-space-pairs-supplements)

(include-files
 (files (imps theories/metric-spaces/metric-space-pairs)
	(imps theories/metric-spaces/metric-space-supplements)))


(def-theory-ensemble-instances metric-spaces
 (target-multiple 2)
 (multiples 1))

(def-theory-ensemble-overloadings metric-spaces (1))

(def-theorem LIM-PRESERVATION
  "forall(f:[pp_0,pp_1],x:pp_0,s:[zz,pp_0],continuous%at%point(f,lim(s)) implies
lim(f oo s)=f(lim(s)))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)
  reverse
  (proof

   (

    (force-substitution "continuous%at%point(f,lim(s))" "lim(s)=lim(s) and continuous%at%point(f,lim(s))" (0))
    (unfold-single-defined-constant (0) continuous%at%point)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%characterization-of-limit)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(lim(s))")
    (incorporate-antecedent "with(s:[zz,pp_0],lim(s)=lim(s));")
    (apply-macete-with-minor-premises tr%characterization-of-limit)
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies forsome(delta:rr, 0<delta and p)))")
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("delta"))
    (instantiate-existential ("n_$0"))
    simplify-insistently
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies forsome(delta:rr, 0<delta and p)))" ("1"))
    (simplify-antecedent "with(p:prop, not(p))")
    (instantiate-universal-antecedent "with(f:[pp_0,pp_1],delta:rr,s:[zz,pp_0],
  forall(y:pp_0,
    dist_0(lim(s),y)<=delta
     implies 
    dist_1(f(lim(s)),f(y))<=1));" ("lim(s)"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises tr%zero-self-distance)
    simplify
    simplify

    )))


;;;(def-theorem LIM-PRESERVATION-REV
;;; "forall(f:[pp_0,pp_1],x:pp_0,s:[zz,pp_0],continuous%at%point(f,lim(s)) implies
;;;f(lim(s)) = lim(f oo s))"
;;; (theory metric-spaces-2-tuples)
;;; (proof "$METRIC_SPACES/proofs/lim-to-lim-ptwise-rev.t")
;;; (usages transportable-macete))

(def-theorem LIM-PRESERVATION-GLOBAL
  "forall(f:[pp_0,pp_1],total_q{f,[pp_0,pp_1]} and continuous(f) implies forall(s:[zz,pp_0],#(lim(s)) implies
lim(f oo s)=f(lim(s))))"
  (theory metric-spaces-2-tuples)

  (proof
   
   (

    (apply-macete-with-minor-premises eps-delta-characterization-of-continuity)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises lim-preservation)
   
   )

   ))


(def-script use-minimum-values 3
  (
   (cut-with-single-formula (% "forsome(~A:rr, 0<~A and ~A <=~A and ~A<=~A)"
			       $1 $1 $1 $2 $1 $3))
   (label-node with-cut)

   (move-to-sibling 1)
   (instantiate-existential ((% "min(~A,~A)" $2 $3)))
   (unfold-single-defined-constant (0) min)
   (case-split ((% "~A<=~A" $2 $3)))
   simplify
   simplify

   (apply-macete-with-minor-premises minimum-1st-arg)
   (apply-macete-with-minor-premises minimum-2nd-arg)
   (jump-to-node with-cut)))
			       
    


(def-theorem splicing-continuous-functions-lemma-1
  "forall(f,g:[pp_0,pp_1], s:sets[pp_0],x:pp_0, 
                           continuous%at%point(f,x) and 
                           continuous%at%point(g,x) and
                           f(x)=g(x)
                           implies
                           continuous%at%point(lambda(z:pp_0,if(z in s, f(z),g(z))),x))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)
  (proof
   (


    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    
    (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,p));" ("eps_$0"))
    (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,p));" ("eps_$0"))
    (use-minimum-values "delta_1" "delta_$0" "delta")
    (instantiate-existential ("delta_1"))
    (case-split ("x in s" "y_$0 in s"))
    simplify
    simplify
    (backchain "with(p:pp_1,p=p);")
    simplify
    simplify
    (backchain-backwards "with(p:pp_1,p=p);")
    simplify
    simplify
    )))

(def-theorem splicing-continuous-functions-lemma-2
  "forall(f,g:[pp_0,pp_1],x:pp_0,
     continuous%at%point(f,x)
      and 
     forsome(r:rr,
       0<r
        and 
       forall(z:pp_0,z in open%ball(x,r) implies f(z)=g(z)))
      implies 
     continuous%at%point(g,x))"
  (theory metric-spaces-2-tuples)
  (usages transportable-macete)
  (proof
   (
    
    
    (unfold-single-defined-constant-globally continuous%at%point)
    (apply-macete-with-minor-premises tr%open-ball-membership-condition)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,p));" ("eps"))
    (use-minimum-values  "delta_1" "r/2" "delta")
    (instantiate-existential ("delta_1"))
    (backchain-backwards "with(p:pp_1,r:rr,forall(z:pp_0,r<r implies p=p));")
    (backchain-backwards "with(p:pp_1,r:rr,forall(z:pp_0,r<r implies p=p));")
    direct-and-antecedent-inference-strategy
    simplify
    (apply-macete-with-minor-premises tr%zero-self-distance)
    simplify)))
