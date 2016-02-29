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
;% COPYRIGHT NOTICE INSERTED: Sun Feb 26 17:20:40 EST 1995


(herald schroeder-bernstein-supplements)

(include-files 
 (files 
  (imps theories/partial-orders/schroeder-bernstein)
  (imps theories/cardinality/cardinality)))

(def-language indicator-pairs
  (embedded-languages generic-theory-2)
  (constants (a "sets[ind_1]") (b "sets[ind_2]")))
  

(def-theory indicator-pairs
  (component-theories generic-theory-2)
  (language indicator-pairs)
  (axioms
   (nonempty-a "nonempty_indic_q{a}")
   (nonempty-b "nonempty_indic_q{b}")))

(def-translation generic-theory-2-to-indicator-pairs
  (source generic-theory-2)
  (target indicator-pairs)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 (indic "a")) (ind_2 (indic "b")))
  (theory-interpretation-check using-simplification))

(def-theorem SCHROEDER-BERNSTEIN-NONEMPTY-CASE
  "(a embeds b) and (b embeds a) implies (a equinumerous b)"
  (home-theory indicator-pairs)
  (theory generic-theory-2)
  lemma
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-transported-theorem schroeder-bernstein-for-types
				     generic-theory-2-to-indicator-pairs
				     ("f_$1" "f_$0"))
    (block 
     (script-comment "`instantiate-transported-theorem' at (0 0 0 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     simplify
     (backchain "with(f:sets[ind_1],f subseteq a);")
     (apply-macete-with-minor-premises tr%range-domain-membership)
     simplify)
    (block 
     (script-comment "`instantiate-transported-theorem' at (0 0 0 0 1)")
     (contrapose "with(p:prop,not(p));")
     simplify
     (backchain-backwards "with(f:sets[ind_2],f=b);")
     simplify
     (apply-macete-with-minor-premises tr%domain-membership-iff-defined))
    (block 
     (script-comment "`instantiate-transported-theorem' at (0 0 1 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     (backchain "with(f:sets[ind_2],f subseteq b);")
     (apply-macete-with-minor-premises range-domain-membership)
     simplify)
    (block 
     (script-comment "`instantiate-transported-theorem' at (0 0 1 0 1)")
     (contrapose "with(p:prop,not(p));")
     (backchain-backwards "with(f:sets[ind_1],f=a);")
     (apply-macete-with-minor-premises domain-membership-iff-defined))
    (block 
     (script-comment "`instantiate-transported-theorem' at (0 1 0 0 0 0)")
     (contrapose "with(x_$2:ind_1,x_$2 in a);")
     (backchain-backwards "with(f:sets[ind_1],f=a);")
     (apply-macete-with-minor-premises domain-membership-iff-defined))
    (block 
     (script-comment "`instantiate-transported-theorem' at (0 1 0 1 0 0)")
     (contrapose "with(x_$5:ind_2,x_$5 in b);")
     (backchain-backwards "with(f:sets[ind_2],f=b);")
     (apply-macete-with-minor-premises tr%domain-membership-iff-defined))
    (block 
     (script-comment "`instantiate-transported-theorem' at (0 1 0 2 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     simplify)
    (block 
     (script-comment "`instantiate-transported-theorem' at (0 1 0 3 0 0 0)")
     (contrapose "with(p:prop,not(p));")
     simplify)
    (block 
     (script-comment "`instantiate-transported-theorem' at (0 1 1 0 0 0 0)")
     (instantiate-existential ("h"))
     insistent-direct-inference
     (block 
      (script-comment "`insistent-direct-inference' at (0)")
      insistent-direct-inference
      (block 
       (script-comment "`insistent-direct-inference' at (0)")
       (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
       direct-and-antecedent-inference-strategy
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	simplify-insistently
	(instantiate-universal-antecedent "with(p:prop,forall(x_$0:ind_1,if_form(p, p, p)));"
					  ("x")))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	simplify-insistently
	direct-and-antecedent-inference-strategy
	(instantiate-universal-antecedent "with(f:sets[ind_1],a subseteq f);"
					  ("x_$0"))
	(contrapose "with(x_$0:ind_1,u:unit%sort,x_$0 in lambda(x_$3:ind_1,u));")
	beta-reduce-repeatedly
	simplify))
      (block 
       (script-comment "`insistent-direct-inference' at (1)")
       (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
       direct-and-antecedent-inference-strategy
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	insistent-direct-inference
	(apply-macete-with-minor-premises indicator-facts-macete)
	beta-reduce-repeatedly
	direct-and-antecedent-inference-strategy
	(instantiate-universal-antecedent "with(p:prop,forall(x_$0:ind_1,if_form(p, p, p)));"
					  ("x_$0"))
	(backchain "with(i,x_$2:ind_2,x_$2=i);"))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	insistent-direct-inference
	(apply-macete-with-minor-premises indicator-facts-macete)
	beta-reduce-repeatedly
	direct-and-antecedent-inference-strategy
	(instantiate-universal-antecedent "with(f:sets[ind_2],b subseteq f);"
					  ("x_$1"))
	(contrapose "with(x_$1:ind_2,u:unit%sort,x_$1 in lambda(x_$6:ind_2,u));")
	simplify)))
     (block 
      (script-comment "`insistent-direct-inference' at (1)")
      insistent-direct-inference
      direct-and-antecedent-inference-strategy
      simplify))


    )))

(def-theorem SCHROEDER-BERNSTEIN-THEOREM-AGAIN
  "forall(b:sets[ind_2],a:sets[ind_1],
    (a embeds b and b embeds a implies a equinumerous b))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (

    direct-inference
    direct-inference
    (antecedent-inference "with(p:prop,p);")
    (case-split ("nonempty_indic_q{a}"))
    (block 
     (script-comment "`case-split' at (1)")
     (cut-with-single-formula "nonempty_indic_q{b}")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (apply-macete-with-minor-premises schroeder-bernstein-nonempty-case)
      simplify)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (antecedent-inference "with(a:sets[ind_1],nonempty_indic_q{a});")
      (antecedent-inference "with(b:sets[ind_2],a:sets[ind_1],a embeds b);")
      (instantiate-existential ("f_$1(x)"))
      (backchain "with(p:prop,p and p and p);")
      (block 
       (script-comment "`backchain' at (0)")
       (apply-macete-with-minor-premises range-domain-membership)
       (backchain "with(p:prop,p and p and p);"))
      simplify))
    (block 
     (script-comment "`case-split' at (2)")
     (cut-with-single-formula "not(nonempty_indic_q{b})")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (contrapose "with(b:sets[ind_2],not(nonempty_indic_q{b}));")
      (contrapose "with(p:prop,forall(f:[ind_1,ind_2],p));")
      (contrapose "with(p:prop,not(p));")
      (contrapose "with(p:prop,forall(f:[ind_1,ind_2],p));")
      (instantiate-existential ("with(x:ind_2, lambda(m:ind_1, if(m in a, x, ?ind_2)))"))
      insistent-direct-inference
      (block 
       (script-comment "`insistent-direct-inference' at (0)")
       insistent-direct-inference
       (block 
	(script-comment "`insistent-direct-inference' at (0)")
	(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	simplify-insistently)
       (block 
	(script-comment "`insistent-direct-inference' at (1)")
	(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	simplify-insistently))
      (block 
       (script-comment "`insistent-direct-inference' at (1)")
       insistent-direct-inference
       simplify
       direct-and-antecedent-inference-strategy
       simplify
       (instantiate-universal-antecedent "with(a:sets[ind_1],empty_indic_q{a});"
					 ("x_$4"))))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (contrapose "with(p:prop,not(p));")
      (antecedent-inference "with(b:sets[ind_2],nonempty_indic_q{b});")
      (antecedent-inference "with(a:sets[ind_1],b:sets[ind_2],b embeds a);")
      (instantiate-existential ("f_$1(x)"))
      (backchain "with(p:prop,p and p and p);")
      (block 
       (script-comment "`backchain' at (0)")
       (apply-macete-with-minor-premises tr%range-domain-membership)
       (backchain "with(p:prop,p and p and p);"))
      simplify))

    )))
