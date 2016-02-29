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


(herald metric-space-triples)

(include-files
 (files (imps theories/metric-spaces/metric-space-pairs)))


(def-theory-ensemble-multiple metric-spaces 3)


(def-theory-ensemble-instances metric-spaces
 (permutations (0 1) (1 2) (0 2))
 (target-multiple 3))

(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-theorem general-composition-of-continuous-functions
  "forall(f:[pp_0,pp_1],g:[pp_1,pp_2],x:pp_0,continuous%at%point(f,x) and continuous%at%point(g,f(x)) implies continuous%at%point(g oo f,x))"
  (theory metric-spaces-3-tuples)

  (proof

   (

    unfold-defined-constants
    beta-reduce-with-minor-premises
    direct-and-antecedent-inference-strategy
    (auto-instantiate-universal-antecedent "with(p:prop,forall(eps:rr,  0<eps implies p))")
    (instantiate-universal-antecedent "with(p:prop,forall(eps:rr,  0<eps implies p))" ("delta_$0"))
    (instantiate-existential ("delta"))
    (backchain "forall(y_$0:pp_1,dist_1(f(x),y_$0)<=delta_$0
     implies 
    dist_2(g(f(x)),g(y_$0))<=eps_$0)")
    (backchain "forall(y:pp_0,
    dist_0(x,y)<=delta implies dist_1(f(x),f(y))<=delta_$0)")
    (cut-with-single-formula "dist_1(f(x),f(y_$0))<=delta_$0")
    (instantiate-universal-antecedent "with(p:prop, forall(eps:rr, 0<eps implies p))" ("1"))
    (simplify-antecedent "not(0<1);")
    (cut-with-single-formula "dist_1(f(x),f(x))<=1")
    (backchain "forall(y:pp_0,dist_0(x,y)<=delta implies dist_1(f(x),f(y))<=1)")
    (apply-macete-with-minor-premises tr%zero-self-distance)
    simplify

    )

   (usages transportable-macete)))

