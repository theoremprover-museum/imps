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


(herald monoids-and-cardinality)

(include-files
 (files (imps theories/algebra/monoids-supplements)))

(load-section basic-cardinality)

(def-theorem cardinality-of-intervals-lemma
  "forall(m:zz, n:nn, omega(n) equinumerous zz%interval(m,m+n-1))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (

    direct-inference
    unfold-defined-constants
    (instantiate-existential ("lambda(k:nn,if(k<n,m+k,?zz))"))
    (block 
	(script-comment "`instantiate-existential' at (0 0 0)") 
      extensionality
      beta-reduce-repeatedly direct-inference 
      (case-split-on-conditionals (1)))
    (block 
	(script-comment "`instantiate-existential' at (0 0 1)") 
      (weaken (0))
      extensionality beta-reduce-repeatedly 
      direct-inference 
      simplify
      direct-inference
      (block 
	  (script-comment "`direct-inference' at (0)")
	(antecedent-inference "with(p:prop,p);") 
	(cut-with-single-formula "0<=x_$7")
	(block 
	    (script-comment "`cut-with-single-formula' at (0)")
	  (backchain-repeatedly ("with(m,x_0:zz,n,x_$7:nn,x_$7<n and x_0=m+x_$7);"))
	  simplify)
	simplify)
      (block 
	  (script-comment "`direct-inference' at (1)")
	(contrapose "with(p:prop,p);") 
	(instantiate-existential ("x_0-m"))
	(block 
	    (script-comment "`instantiate-existential' at (0 0)")
	  (cut-with-single-formula "0<=n") 
	  simplify simplify)
	simplify))
    (block 
	(script-comment "`instantiate-existential' at (0 1)")
      insistent-direct-inference 
      simplify)
    (block 
	(script-comment "`instantiate-existential' at (1 0)") 
      sort-definedness
      direct-and-antecedent-inference-strategy 
      (contrapose "with(r:rr,#(r));")
      simplify 
      (contrapose "with(p:prop,not(p));") 
      simplify)

    )))

;; Commented out by Josh
;;
;; 
;;  (def-theorem second-characterization-of-monoid%prod%unordered
;;    "forall(s:sets[ind_1], f:[ind_1,uu],a:uu, f_indic_q{s} implies
;;           
;;           monoid%prod%unordered(s,f) = a iff
;;           forall(m:zz,phi:[zz,ind_1], 
;;             injective_q{phi} 
;;               and 
;;             zz%interval(m,m+f_card{s}-1) subseteq dom{phi}
;;               and
;;             image{phi,zz%interval(m,m+f_card{s}-1)} = s
;;               implies 
;;             monoid%prod(m,m+f_card{s}-1,f oo phi)=a))"
;;    (theory monoids-with-index-set))
