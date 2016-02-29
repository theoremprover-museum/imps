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


(herald state-machines)


(push-current-theory)

(def-language state-machine-language
  (base-types state action)
  (constants 
   (tr (state action state prop))
   (initial (state prop))
   (accepting (state prop))))
      
(define state-machines-0
  (theory-from-definition
   '(state-machines-0
     (language state-machine-language))))

(def-theory state-machines
  (language state-machine-language)
  (component-theories h-o-real-arithmetic))

(set (current-theory) (name->theory 'state-machines))

;;; Definitions

(def-constant  history
  "lambda(s_seq:[nn,state], a_seq:[nn,action],
        (#(s_seq(0)) implies initial(s_seq(0)))
       and
	forall(i:nn, #(s_seq(i+1)) implies tr(s_seq(i),a_seq(i),s_seq(i+1))))"  
  (theory state-machines)
  (usages transportable-macete))

(def-constant  state%history
  "lambda(s_seq:[nn,state], forsome(a_seq:[nn,action], history(s_seq, a_seq)))"  
  (theory state-machines)
  (usages transportable-macete))

(def-constant  action%history
  "lambda(a_seq:[nn,action], forsome(s_seq:[nn,state], history(s_seq, a_seq)))"  
  (theory state-machines)
  (usages transportable-macete))

(def-constant  accessible
  "lambda(s:state,
	forsome(s_seq:[nn,state], a_seq:[nn,action], i:nn,
	 history(s_seq, a_seq) and s_seq(i)=s))"  
  (theory state-machines)
  (usages transportable-macete))


(def-constant  in%language
  "lambda(a_seq:[nn,action],
	forsome(s_seq:[nn,state],
	 history(s_seq, a_seq) and accepting(s_seq(length(s_seq)-1))))"  
  (theory state-machines)
  (usages transportable-macete))

(theory-import-transportable-rewrite-rules
 (name->theory 'state-machines)
 (list sequences))

(def-theorem histories-defined-on-state-segment
 "forall(s_seq:[nn,state], a_seq:[nn,action], i,j:zz,
history(s_seq, a_seq) and #(s_seq(j)) and i<=j and 0<=i implies #(s_seq(i)))"
 (theory state-machines)
 (usages tranportable-macete)
 (proof "$THEORIES/state-machines/proofs/histories-defined-on-state-segment.t"))

(def-theorem histories-defined-on-action-segment
 "forall(s_seq:[nn,state], a_seq:[nn,action], i,j:zz,
history(s_seq, a_seq) and #(s_seq(j+1)) and i<=j and 0<=i implies #(a_seq(i)))"
 (theory state-machines)
 (usages tranportable-macete)
 (proof "$THEORIES/state-machines/proofs/histories-defined-on-action-segment.t"))

(def-theorem histories-defined-at-0
 "forall(s_seq:[nn,state], a_seq:[nn,action], j:zz,
history(s_seq, a_seq) and #(s_seq(j)) implies #(s_seq(0)))"
 (theory state-machines)
 (usages )
 (proof "$THEORIES/state-machines/proofs/histories-defined-at-0.t"))

(def-theorem fundamental-sm-thm
 "forall(p:[state,prop],
	(forall(s:state, initial(s) implies p(s))
	and
	 forall(s_1, s_2:state, a:action,
		(p(s_1) and tr(s_1, a, s_2))
		implies
		p(s_2)))
	implies
	 forall(s:state, accessible(s) implies p(s)))"
 (theory state-machines)
 (usages )
 (proof "$THEORIES/state-machines/proofs/fundamental-sm-thm.t"))

;(BUILD-INDUCTOR-FROM-INDUCTION-PRINCIPLE
; (name->theorem 'fundamental-sm-thm)			
; 'sm-inductor						
; (name->macete 'eliminate-nonrecursive-definitions-and-simplify) 
; '#f)

(def-theorem initial-implies-accessible
 "forall(s:state, initial(s) implies accessible(s))"
 (theory state-machines)
 (usages transportable-macete)
 (proof "$THEORIES/state-machines/proofs/initial-implies-accessible.t"))

(def-theorem tr-preserves-accessible
 "forall(s_1,s_2:state, a:action, 
  accessible(s_1) and tr(s_1,a,s_2) implies accessible(s_2))"
 (theory state-machines)
 (usages transportable-macete)
 (proof "$THEORIES/state-machines/proofs/tr-preserves-accessible.t"))

(def-theorem converse-sm-induction
 "forall(p:[state,prop], 
 forall(s:state, 
 accessible(s) 
 implies
p(s)) 
 implies
forall(s:state, 
 initial(s) 
 implies
p(s)) and forall(s_1,s_2:state,a:action, 
 accessible(s_1) and p(s_1) and tr(s_1,a,s_2) 
 implies
p(s_2)))"
 (theory state-machines)
 (usages )
 (proof "$THEORIES/state-machines/proofs/converse-sm-induction.t"))

(def-theorem sm-induction
 "forall(p:[state,prop], 
 forall(s:state, 
 initial(s) 
 implies
p(s)) and forall(s_1,s_2:state,a:action, 
 accessible(s_1) and p(s_1) and tr(s_1,a,s_2) 
 implies
p(s_2)) 
 implies
forall(s:state, 
 accessible(s) 
 implies
p(s)))"
 (theory state-machines)
 (usages )
 (proof "$THEORIES/state-machines/proofs/sm-induction.t"))


(def-theorem sm-induction-biconditional
 "forall(p:[state,prop],
	(forall(s:state, initial(s) implies p(s))
	and
	 forall(s_1, s_2:state, a:action,
		(accessible(s_1) and p(s_1) and tr(s_1, a, s_2))
		implies
		p(s_2)))
	iff
	 forall(s:state, accessible(s) implies p(s)))"
 (theory state-machines)
 (usages )
 (proof "$THEORIES/state-machines/proofs/sm-induction-biconditional.t"))

(def-theorem sm-induction-biconditional-conv
 "forall(p:[state,prop],
	 forall(s:state, accessible(s) implies p(s))
	iff
	(forall(s:state, initial(s) implies p(s))
	and
	 forall(s_1, s_2:state, a:action,
		(accessible(s_1) and p(s_1) and tr(s_1, a, s_2))
		implies
		p(s_2))))"
 (theory state-machines)
 (usages )
 (proof "$THEORIES/state-machines/proofs/sm-induction-biconditional-conv.t"))

(def-inductor sm-induct
  sm-induction-biconditional-conv
  (theory state-machines)
  (base-case-hook eliminate-nonrecursive-definitions-and-simplify))

(def-theory-ensemble state-machines)

(pop-current-theory)


 
