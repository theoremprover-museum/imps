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


(herald normed-groups)

(include-files 
 (files (imps theories/algebra/monoids)
        (imps theories/metric-spaces/metric-space-supplements)))

(def-language GROUPS-ALT
  (embedded-languages monoid-language)
  (constants (inv (uu uu ))))

(def-theory GROUPS-ALT
  (component-theories monoid-theory)
  (language groups-alt)
  (axioms
   (right-inverse-property "forall(x:uu,x**inv(x)=e)" rewrite)))

(def-theorem INV-IS-TOTAL-ALT
  "total_q(inv,[uu,uu])"
  (usages d-r-convergence)
  (theory groups-alt)
  (proof
   (
    insistent-direct-inference
    (cut-with-single-formula "x_0**inv(x_0)=e")
    (apply-macete-with-minor-premises right-inverse-property)
    )))

(def-language NORMED-GROUPS
  (embedded-language groups-alt)
  (constants
   (norm "[uu,rr]")))

(def-theory NORMED-GROUPS
  (language normed-groups)
  (component-theories groups-alt)
  (axioms
   (norm-totality-alt
    "total_q{norm,[uu, rr]}" d-r-convergence transportable-macete)
   (positivity-of-norm-alt
    "forall(x:uu, 0<=norm(x))" transportable-macete)
   (norm-zero-alt
    "forall(x:uu, norm(x)=0 iff x = e)" transportable-macete)
   (norm-triangle-inequality-alt
    "forall(x,y:uu, norm(x**y) <= norm(x) + norm(y))" transportable-macete)))

(comment

(def-theory-ensemble-instances
 metric-spaces 
 (target-theories normed-groups normed-groups)
 (multiples 1 2)
 (theory-interpretation-check using-simplification)
 (sorts (pp uu uu))
 (constants (dist "lambda(x,y:uu, norm(x**inv(y)))" "lambda(x,y:uu, norm(x**inv(y)))")))

)
