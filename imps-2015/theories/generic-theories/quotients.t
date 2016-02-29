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

(herald quotients)

(include-files
   (files (imps theories/generic-theories/binary-relations-and-predicates)))

(def-constant quotient
  "lambda(rel:[ind_1,ind_1 -> prop], lambda(x:ind_1, indic{z:ind_1, rel(x,z)}))"
  (theory generic-theory-1))


(def-theorem quotient-map-for-equivalence-relations
  "forall(rel:[ind_1,ind_1 -> prop], 
           equiv%predicate(rel) 
            implies
           forall(x,y:ind_1, rel(x,y) iff quotient(rel)(x)=quotient(rel)(y)))"
  (usages transportable-macete)
  reverse
  (theory generic-theory-1)
  (proof
   (

    (apply-macete-with-minor-premises characterization-of-equivalence-predicates)
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0)")
      extensionality
      simplify
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
	simplify
	(backchain "with(p:prop,forall(a,b:ind_1,p));")
	(backchain "with(p:prop,forall(a,b,c:ind_1,p));")
	(instantiate-existential ("x"))
	(backchain "with(p:prop,forall(a,b:ind_1,p));"))
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
	(contrapose "with(p:prop,not(p));")
	(backchain "with(p:prop,forall(a,b:ind_1,p));")
	(backchain "with(p:prop,forall(a,b,c:ind_1,p));")
	(instantiate-existential ("y"))
	(backchain "with(p:prop,forall(a,b:ind_1,p));")
	(backchain "with(p:prop,forall(a,b:ind_1,p));")))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 1 0)")
      (contrapose "with(f:sets[ind_1],f=f);")
      extensionality
      simplify
      (instantiate-existential ("y"))
      simplify)

    )))

