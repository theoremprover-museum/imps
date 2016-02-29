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


(herald aux-bell-lapadula)



;; The next six lemmas simply assert that the functions just defined are
;; defined, with values of the right sort.   The first two are trivial, so
;; don't bother proving them, just execute the forms.  

(def-theorem ()
  "total_q{with%read%access,[access,access]}"
  (theory access_records)
  (usages d-r-convergence)
  (proof ((unfold-single-defined-constant-globally with%read%access)
	  simplify-insistently
	  )))

(def-theorem ()
  "total_q{without%read%access,[access,access]}"
  (theory access_records)
  (usages d-r-convergence)
  (proof ((unfold-single-defined-constant-globally without%read%access)
	  simplify-insistently
	  )))

;; To prove this one, unfold del%read%access, then unfold without%read%access. 
;; Use direct inference to remove the universal quantifier.  Finally, use
;; sort-definedness-and-conditionals to complete the proof.  

(def-theorem del-read-returns-state
  "forall(s:state, u_0:user, o_0:object, #(del%read%access(s,u_0,o_0),state))"
  (theory access_records)
  (usages d-r-convergence)
  (proof ((unfold-single-defined-constant-globally del%read%access)
	  (unfold-single-defined-constant-globally without%read%access)
	  direct-inference
	  sort-definedness-and-conditionals
	  )))

;; This theorem is very similar, except that at the end you will have to do
;; the following on each of two lingering subgoals:
;; 
;; 1.  Insistent-direct-inference (breaks up a "total_q")
;; 2.  Beta-reduce
;; 3.  Case-split-on-conditionals.  

(def-theorem get-read-returns-state
 "forall(s:state, u_0:user, o_0:object, #(get%read%access(s,u_0,o_0),state))"
 (theory access_records)
 (usages d-r-convergence)
 (proof ((unfold-single-defined-constant-globally get%read%access)
	 (unfold-single-defined-constant-globally with%read%access)
	 direct-inference
	 sort-definedness-and-conditionals
	 insistent-direct-inference
	 beta-reduce
	 (case-split-on-conditionals (0))
	 insistent-direct-inference
	 beta-reduce
	 (case-split-on-conditionals (0)))))

;; Two convenient variants, both straightforward to prove.  Just evaluate
;; the forms; don't bother to prove them.   

(def-theorem get-read-returns-total-fn
  "forall(o:object,u:user,s:state, 
 total_q{get%read%access(s,u,o),[user,object,access]});"
  (theory access_records)
  (usages rewrite)
  (proof ((unfold-single-defined-constant-globally get%read%access)
	  insistent-direct-and-antecedent-inference-strategy
	  (case-split-on-conditionals (0))
	  (case-split-on-conditionals (0))
	  (unfold-single-defined-constant-globally with%read%access)
	  )))
  
(def-theorem del-read-returns-total-fn
  "forall(o:object,u:user,s:state, 
 total_q{del%read%access(s,u,o),[user,object,access]});"
  (theory access_records)
  (usages rewrite)
  (proof ((unfold-single-defined-constant-globally del%read%access)
	  simplify-insistently
	  (raise-conditional (0))
	  simplify
	  )))

