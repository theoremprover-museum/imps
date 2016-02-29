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


(herald subspaces)

(include-files
 (files (imps theories/metric-spaces/metric-spaces)
	(imps theories/metric-spaces/metric-space-pairs)
	(imps theories/metric-spaces/metric-space-supplements)
	(imps theories/metric-spaces/metric-space-pairs-supplements)))


(def-language LANGUAGE-FOR-MS-SUBSPACE
  (embedded-languages metric-spaces-language)
  (sorts (aa pp)))
      
(def-theory MS-SUBSPACE
  (component-theories metric-spaces)
  (language language-for-ms-subspace))

(def-theorem () 
  "forall(x,y,z:aa,dist(x,z)<=dist(y,z)+dist(x,y))" 
  lemma
  (theory ms-subspace)
  (proof
   (
    (apply-macete-with-minor-premises commutative-law-for-addition)
    (apply-macete-with-minor-premises triangle-inequality-for-distance)
    )))

(def-theory-ensemble-instances
  metric-spaces
  force-under-quick-load
  (target-theories ms-subspace ms-subspace)
  (multiples 1 2)
  (theory-interpretation-check using-simplification)
  (sorts (pp aa aa))
  (constants (dist "lambda(x,y:aa, dist(x,y))" "lambda(x,y:aa, dist(x,y))"))
  (special-renamings 
   (ball sub%ball)
   (open%ball sub%open%ball)
   (lipschitz%bound sub%lipschitz%bound)
   (lipschitz%bound%on sub%lipschitz%bound%on)
   (complete sub%complete)
   (cauchy sub%cauchy)
   (lim sub%lim)))


(def-theorem cauchy-extends
  "forall(s:[zz,aa],cauchy(s) iff sub%cauchy(s))"
  (proof (unfold-defined-constants))
  (usages transportable-macete)
  (theory ms-subspace))

(def-constant subspace%closed
  "forall(s:[zz,aa], #(lim(s)) implies #(lim(s),aa))"
  (theory ms-subspace))

(def-theorem limit-definedness-extends
  "forall(s:[zz,aa],subspace%closed implies lim(s) == sub%lim(s))"
  reverse
  (usages transportable-macete)

  (proof
   ((unfold-single-defined-constant (0) subspace%closed)
    insistent-direct-inference-strategy
    (antecedent-inference "with(s:[zz,aa],#(lim(s)) or #(sub%lim(s)));")
    (force-substitution "lim(s)=sub%lim(s)" "sub%lim(s)=lim(s)" (0))
    (cut-with-single-formula "forsome(x:aa, lim(s)=x)")
    (antecedent-inference "with(s:[zz,aa],forsome(x:aa,lim(s)=x));")
    (backchain "with(x:aa,s:[zz,aa],lim(s)=x);")
    (apply-macete-with-minor-premises tr%characterization-of-limit)
    beta-reduce-repeatedly
    (backchain-backwards "with(x:aa,s:[zz,aa],lim(s)=x);")
    (cut-with-single-formula "lim(s)=lim(s)")
    (incorporate-antecedent "with(s:[zz,aa],lim(s)=lim(s));")
    (apply-macete-with-minor-premises characterization-of-limit)
    (instantiate-existential ("lim(s)"))
    simplify
    (apply-macete-with-minor-premises characterization-of-limit)
    (cut-with-single-formula "sub%lim(s)=sub%lim(s)")
    (incorporate-antecedent "with(s:[zz,aa],sub%lim(s)=sub%lim(s));")
    (apply-macete-with-minor-premises tr%characterization-of-limit)
    beta-reduce-repeatedly))
  (theory ms-subspace))

(def-theorem completeness-extends
  "complete implies subspace%closed iff sub%complete"
  reverse
  (proof
   (

    (unfold-single-defined-constant (0) complete)
    (unfold-single-defined-constant (0) sub%complete)
    (force-substitution "sub%cauchy(s)" "cauchy(s)" (0))
    direct-and-antecedent-inference-strategy
    (force-substitution "sub%lim(s)" "lim(s)" (0))
    (backchain "forall(s:[zz,pp],cauchy(s) implies #(lim(s)));")
    (apply-macete-with-minor-premises limit-definedness-extends)
    (unfold-single-defined-constant (0) subspace%closed)
    direct-and-antecedent-inference-strategy
    (instantiate-universal-antecedent "forall(s:[zz,aa],cauchy(s) implies #(sub%lim(s)));" ("s"))
    (contrapose "with(s:[zz,aa],not(cauchy(s)));")
    (apply-macete-with-minor-premises convergent-implies-cauchy)
    (cut-with-single-formula "forsome(x:aa, lim(s)=x)")
    (antecedent-inference "with(s:[zz,aa],forsome(x:aa,lim(s)=x));")
    (instantiate-existential ("sub%lim(s)"))
    (apply-macete-with-minor-premises characterization-of-limit)
    (cut-with-single-formula "sub%lim(s)=sub%lim(s)")
    (incorporate-antecedent "with(s:[zz,aa],sub%lim(s)=sub%lim(s));")
    (apply-macete-with-minor-premises tr%characterization-of-limit)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises cauchy-extends)

    ))
  
  (usages transportable-macete)
  (theory ms-subspace))


(def-constant subspace%dense
  "forall(x:pp, forsome(s:[zz,aa], lim(s)=x))"
  (theory ms-subspace))
