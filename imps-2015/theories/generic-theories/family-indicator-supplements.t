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


(herald FAMILY-INDICATOR-SUPPLEMENTS)

(include-files
  (files (imps theories/generic-theories/indicator-lemmas)))


(def-theorem BIG-UNION-RECURSION
  "forall(f:[index,sets[uu]], i:index, 
     i in dom{f}
       implies
     big_u{f} = f(i) union big_u{lambda(k:index, if(not(k=i), f(k),?sets[uu]))})"
  (theory family-indicators)
  (usages transportable-macete)
  (proof 
   (
	  

    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      insistent-direct-inference
      (apply-macete-with-minor-premises union-disjunction-conversion)
      (apply-macete-with-minor-premises big-union-member)
      beta-reduce-repeatedly
      direct-and-antecedent-inference-strategy
      (instantiate-existential ("i_$0"))
      (cut-with-single-formula "not(i_$0=i)")
      simplify
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(contrapose "with(p:prop,not(p));")
	simplify))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      insistent-direct-inference
      (apply-macete-with-minor-premises union-disjunction-conversion)
      (apply-macete-with-minor-premises big-union-member)
      beta-reduce-repeatedly
      direct-and-antecedent-inference-strategy
      auto-instantiate-existential
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
	(instantiate-existential ("i_$0"))
	(cut-with-single-formula "not(i_$0=i)")
	(contrapose "with(x_$0:uu,f:sets[uu],x_$0 in f);")
	simplify))

    )))


(def-theorem UNION-SPECIAL-CASE
  "forall(f:[index,sets[uu]], j,k:index, 
     dom{f}=indic{i:index, i=j or i=k}
       implies
     big_u{f} = f(j) union f(k))"
  (theory family-indicators)
  (usages transportable-macete)
  (proof 
   (

    direct-and-antecedent-inference-strategy
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "i in dom{f}")
    (move-to-sibling 1)
    simplify
    (block 
     (script-comment "node added by `cut-with-single-formula' at (0)")
     (contrapose "with(i:index,f:sets[index],i in f);")
     (backchain "with(f:sets[index],f=f);")
     (apply-macete-with-minor-premises indicator-facts-macete)
     simplify
     (contrapose "with(x_0:uu,k:index,f:[index,sets[uu]],not(x_0 in f(k)));")
     (antecedent-inference "with(p:prop,p implies p);")
     (simplify-antecedent "with(p:prop,not(p));")
     simplify)

    )))
