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


(herald group-cardinality)


(include-files
  (files (imps theories/groups/cosets)
	 (imps theories/cardinality/finite-cardinality)))



(def-theorem FINITENESS-OF-SUBGROUPS
  "forall(a:sets[gg], 
     f_indic_q{gg%subgroup} and subgroup(a) implies f_indic_q{a})"
  (theory groups)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
    (instantiate-existential ("gg%subgroup"))
    (apply-macete-with-minor-premises subgroups-are-subsets-of-gg%subgroup)
    )))

(def-theorem FINITENESS-OF-STABILIZERS
  "forall(alpha:uu, 
     f_indic_q{gg%subgroup} implies f_indic_q{stabilizer(alpha)})"
  (theory group-actions)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises finiteness-of-subgroups)
    (apply-macete-with-minor-premises stabilizers-are-subgroups)
    )))
  
(def-theorem RIGHT-COSETS-ARE-EQUINUMEROUS
  "forall(a:sets[gg],g,h:gg, right%trans(a,g) equinumerous right%trans(a,h))"
  (theory groups)
  (usages transportable-macete)
  (proof
   (					; 169 nodes

    direct-inference
    (unfold-single-defined-constant-globally right%trans)
    (instantiate-existential 
     ("lambda(i:gg,iota(j:gg, 
         forsome(k:gg, (k in a) and i=k mul g and j=k mul h)))"))
    insistent-direct-inference
    (block 
      (script-comment "node added by `insistent-direct-inference' at (0)")
      insistent-direct-inference
      (block 
	(script-comment "node added by `insistent-direct-inference' at (0)")
	extensionality
	direct-inference
	beta-reduce-repeatedly
	simplify
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment 
	   "node added by `direct-and-antecedent-inference-strategy' at (0)")
	  (contrapose "with(p:prop,p);")
	  (eliminate-iota 0)
	  direct-and-antecedent-inference-strategy
	  (contrapose "with(p:prop,forall(i_$2:gg,p or p));")
	  (instantiate-existential ("k")))
	(block 
	  (script-comment 
	   "node added by `direct-and-antecedent-inference-strategy' at (1 0 0)")
	  (contrapose "with(p:prop,not(p));")
	  (eliminate-iota 0)
	  (instantiate-existential ("i_$2 mul h"))
	  auto-instantiate-existential
	  (block 
	    (script-comment "node added by `instantiate-existential' at (0 1 0 0)")
	    (antecedent-inference-strategy (0))
	    (backchain "with(h,k_$0,z%iota_$0:gg,z%iota_$0=k_$0 mul h);")
	    (apply-macete-with-minor-premises group-cancellation-laws)
	    (force-substitution "k_$0" "x_0 mul inv(g)" (0))
	    (block 
	      (script-comment "node added by `force-substitution' at (0)")
	      (backchain "with(g,i_$2,x_0:gg,x_0=i_$2 mul g);")
	      (weaken (5 4 3 2 1 0))
	      simplify)
	    (block 
	      (script-comment "node added by `force-substitution' at (1)")
	      (weaken (5 4 3 2 0))
	      simplify
	      (backchain "with(p:prop,p);")
	      (weaken (0))
	      simplify))))
      (block 
	(script-comment "node added by `insistent-direct-inference' at (1)")
	(weaken (0))
	extensionality
	direct-inference
	beta-reduce-repeatedly
	simplify
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment 
	   "node added by `direct-and-antecedent-inference-strategy' at (0 0)")
	  (cut-with-single-formula 
	   "#(iota(j:gg, forsome(k:gg,k in a and x_$10=k mul g and j=k mul h)))")
	  (incorporate-antecedent "with(g,x_0:gg,x_0=g);")
	  (eliminate-defined-iota-expression 0 u)
	  direct-and-antecedent-inference-strategy
	  (antecedent-inference "with(p:prop,forsome(k:gg,p));")
	  (instantiate-existential ("k")))
	(block 
	  (script-comment 
	   "node added by `direct-and-antecedent-inference-strategy' at (1 0 0)")
	  (contrapose "with(p:prop,not(p));")
	  (instantiate-existential ("i_$1 mul g"))
	  (apply-macete-with-minor-premises eliminate-iota-macete)
	  direct-and-antecedent-inference-strategy
	  auto-instantiate-existential
	  (block 
	    (script-comment 
	     "node added by `direct-and-antecedent-inference-strategy' at (1 0 0 0 0 0 0)")
	    (backchain "with(h,k_$1,x_0:gg,x_0=k_$1 mul h);")
	    (backchain "with(h,k_$0,b_$0:gg,b_$0=k_$0 mul h);")
	    (incorporate-antecedent "with(k_$1,g,i_$1:gg,i_$1 mul g=k_$1 mul g);")
	    (incorporate-antecedent "with(k_$0,g,i_$1:gg,i_$1 mul g=k_$0 mul g);")
	    (apply-macete-with-minor-premises group-cancellation-laws)
	    (weaken (5 4 3 2 1 0))
	    simplify))))
    (block 
      (script-comment "node added by `insistent-direct-inference' at (1)")
      (weaken (0))
      insistent-direct-inference
      simplify
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula 
       "#(iota(j:gg, forsome(k:gg,k in a and x_$1=k mul g and j=k mul h)))")
      (cut-with-single-formula 
       "#(iota(j:gg, forsome(k:gg,k in a and x_$2=k mul g and j=k mul h)))")
      (incorporate-antecedent "with(p:prop,iota(j:gg,p)=iota(j:gg,p));")
      (eliminate-defined-iota-expression 0 u)
      (eliminate-defined-iota-expression 0 v)
      (antecedent-inference-strategy (0 2))
      (weaken (2 3 4 5 8 9 10 11 12 13))
      (backchain "with(h,k,v:gg,v=k mul h);")
      (backchain "with(g,k,x_$2:gg,x_$2=k mul g);")
      (backchain "with(g,k_$0,x_$1:gg,x_$1=k_$0 mul g);")
      (backchain "with(h,k_$0,u:gg,u=k_$0 mul h);")
      (apply-macete-with-minor-premises group-cancellation-laws))

    )))

