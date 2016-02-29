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


(herald continuous-mapping-spaces)

;;;Instance of mappings into a pointed spaces:

(include-files
 (files (imps theories/metric-spaces/mappings-into-pointed-metric-spaces)))


(def-language pointed-target-space
  (embedded-languages metric-spaces-2-tuples)
  (constants (a_0 pp_1)))

(def-theory pointed-ms-2-tuples
  (language  pointed-target-space)
  (component-theories  metric-spaces-2-tuples))

;; Interpret  pointed-ms-2-tuples as an (ind_1, pp) pair:

(def-translation mappings-pointed-metric-spaces-2-tuples
  force-under-quick-load
  (source mappings-into-a-pointed-metric-space)
  (target pointed-ms-2-tuples)
  (sort-pairs (ind_1 pp_0) (pp pp_1))
  (constant-pairs (a_0 a_0) (dist dist_1))
  (fixed-theories h-o-real-arithmetic)
  (theory-interpretation-check using-simplification))

(def-renamer mappings-to-pointed-target-space-renamer
  (pairs (bfun%dist ms%bfun%dist) (bfun ms%bfun)))

(def-transported-symbols (bfun%dist bfun)
  (translation  mappings-pointed-metric-spaces-2-tuples)
  (renamer mappings-to-pointed-target-space-renamer))

;; Obligations: Just translate the corresponding theorems for the sup metric
;; on an arbitrary ind_1.

(def-theorem ()
  "forall(x,y,z:bfun, bfun%dist(x,z)<=bfun%dist(x,y)+bfun%dist(y,z))"
  lemma
  (home-theory mappings-into-a-pointed-metric-space)
  (translation mappings-pointed-metric-spaces-2-tuples)
  (proof existing-theorem)
  (theory  pointed-ms-2-tuples))

(def-theorem non-negativity-of-distance
  "forall(x,y:bfun, 0<=bfun%dist(x,y))"
  (home-theory mappings-into-a-pointed-metric-space)
  (translation mappings-pointed-metric-spaces-2-tuples)
  (proof existing-theorem)
  (usages transportable-macete)
  (theory  pointed-ms-2-tuples))


(def-theorem ()
  "forall(x,y:bfun, bfun%dist(x,y)=bfun%dist(y,x))"
  lemma
  (home-theory mappings-into-a-pointed-metric-space)
  (translation mappings-pointed-metric-spaces-2-tuples)
  (proof existing-theorem)
  (theory  pointed-ms-2-tuples))

(def-theorem ()
  "forall(x,y:bfun, x=y iff bfun%dist(x,y)=0)"
  lemma
  (home-theory mappings-into-a-pointed-metric-space)
  (translation mappings-pointed-metric-spaces-2-tuples)
  (proof existing-theorem)
  (theory  pointed-ms-2-tuples))

(def-theory-ensemble-instances
  metric-spaces
  force-under-quick-load
  (permutations (0))
  (sorts (pp ms%bfun))
  (constants (dist ms%bfun%dist))
  (target-theories pointed-ms-2-tuples)
  (special-renamings
   (ball ms%bfun%ball)
   (open%ball ms%bfun%open%ball)
   (complete ms%bfun%complete)
   (lipschitz%bound%on ms%bfun%lipschitz%bound%on)
   (lipschitz%bound ms%bfun%lipschitz%bound)))


(def-theory-ensemble-overloadings metric-spaces (1 2))

(def-overloading dist
  (pointed-ms-2-tuples ms%bfun%dist)
  (metric-spaces dist))




