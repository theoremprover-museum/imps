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


(herald deterministic-state-machines)

(*require nil '(theories state-machines/state-machines) imps-implementation-env)
(push-current-theory)

(def-language det-state-machine-language
  (base-types state action)
  (constants 
   (next (state action state))))
      
(def-theory det-state-machines
  (language det-state-machine-language)
  (component-theories state-machines)
  (axioms
   (tr-means-next
    "forall(s:state, a:action, s_1:state, tr(s,a,s_1) iff next(s,a)=s_1)"
    rewrite)))

(language-from-definition
 '(start-det-state-machine-language
   (base-types state action)
   (constants 
    (s_init state))))

(define det-state-machines-with-start
  (theory-from-definition
   '(det-state-machines-with-start
     (language start-det-state-machine-language)
     (component-theories det-state-machines)
     (axioms
      (s_init-sole-initial
       "forall(s:state, initial(s) iff s=s_init)"
       (rewrite))))))

(define det-state-machines (name->theory 'det-state-machines))
;; (define det-state-machines-with-start (name->theory 'det-state-machines-with-start))
;;; Definitions 
(set (current-theory) (name->theory 'det-state-machines))

(theory-build-recursive-definition
 det-state-machines
 'run
 (qr "lambda(r:[state,[nn,action],state],
       lambda(s:state,a_seq:[nn,action],
	if(a_seq=nil(action), s,
	   r(next(s,(a_seq(0))), drop(a_seq,1)))))")
 'run
 'transportable-macete)


(theory-import-transportable-rewrite-rules det-state-machines (list sequences))

(def-theorem next-preserves-accessible
 "forall(s,s_1:state, a:action, accessible(s) and next(s,a)=s_1 implies accessible(s_1))"
 (theory det-state-machines)
 (usages )
 (proof "$THEORIES/state-machines/proofs/next-preserves-accessible.t"))

(def-theorem run-next
 "forall(s_1:state,a:action,a_seq:[nn,action], 
 	run(next(s_1,a),a_seq)==run(s_1,cons(a,a_seq)))"
 (theory det-state-machines)
 (usages transportable-macete)
 (proof "$THEORIES/state-machines/proofs/run-next.t"))

(def-theorem det-fun-sm-thm
 "forall(p:[state,prop],
	(forall(s:state, initial(s) implies p(s))
	and
	 forall(s:state, a:action,
		p(s)
		implies
		p(next(s,a))))
	implies
	 forall(s:state, accessible(s) implies p(s)))"
 (theory det-state-machines)
 (usages transportable-macete)
 (proof "$THEORIES/state-machines/proofs/det-fun-sm-thm.t"))

(def-theorem dsm-induction-biconditional-conv
 "forall(p:[state,prop], forall(s:state, accessible(s) implies p(s)) 
 	iff
 	(forall(s:state,  initial(s) implies p(s))
 	and 
	 forall(s_1:state,a:action, 
	  accessible(s_1) and p(s_1) and #(next(s_1,a))
	  implies
	  p(next(s_1,a)))))"
 (theory det-state-machines)
 (usages transportable-macete)
 (proof "$THEORIES/state-machines/proofs/dsm-induction-biconditional-conv.t"))

(define dsm-inductor
  (build-inductor-from-induction-principle
   (name->theorem 'dsm-induction-biconditional-conv)
   'dsm-inductor                 
   (name->macete 'eliminate-nonrecursive-definitions-and-simplify)
   '#f
   det-state-machines))

(def-theorem dsm-induction-biconditional
  "forall(p:[state,prop],
	(forall(s:state,  initial(s) implies p(s))
 	and 
	 forall(s_1:state,a:action, 
	  accessible(s_1) and p(s_1) and #(next(s_1,a))
	  implies
	  p(next(s_1,a))))
 	iff
 	forall(s:state, accessible(s) implies p(s)))"
  (theory det-state-machines)
  (usages transportable-macete)
  (proof						;just cite the preceding and simplify.
   ""))

(define act-inductor
  (build-translated-inductor-from-induction-principle
   (translation-match
    sequences 
    det-state-machines
    the-empty-set
    (list the-kernel-theory *ho*)
    (name->theorem 'sequence-induction)			; pattern
    (qr "forall(p:[[nn,action],prop],
	forall(actions:[nn,action],
	 f_seq_q(actions) implies p(actions))
      iff
	(p(nil(action))
	and 
	 forall(actions:[nn,action], first:action,
	  f_seq_q(actions) and p(actions) implies p(cons{first,actions}))))"))
   (name->theorem 'sequence-induction)
   'act-inductor
   '#f
   '#f))

;; (qr "forall(m:zz,
;; 	0<=m
;;        implies
;; 	forall(s_1:state, a_seq_1,a_seq_2:[nn,action], 
;; 	 length(a_seq_1)=m
;; 	implies
;;          run(run(s_1,a_seq_1),a_seq_2)==run(s_1, append(a_seq_1,a_seq_2))))")

(def-theorem run-run-lemma
 "forall(a_seq_1:[nn,action], 
     f_seq_q(a_seq_1) implies
        forall(s_1:state, a_seq_2:[nn,action],
	run(run(s_1,a_seq_1),a_seq_2)==run(s_1, append(a_seq_1,a_seq_2))))"
 (theory det-state-machines)
 (usages )
 (proof "$THEORIES/state-machines/proofs/run-run-lemma.t"))


(qr "forall(a_seq_1:[nn,action], 
     f_seq_q(a_seq_1) implies
        forall(s_1:state, a_seq_2:[nn,action],
	run(s_1, append(a_seq_1,a_seq_2))==run(run(s_1,a_seq_1),a_seq_2)))")

(def-theorem run-run
 "forall(s_1:state, a_seq_1, a_seq_2:[nn,action], 
     f_seq_q(a_seq_1) implies
	run(run(s_1,a_seq_1),a_seq_2)==run(s_1, append(a_seq_1,a_seq_2)))"
 (theory det-state-machines)
 (usages transportable-macete)
 (proof "$THEORIES/state-machines/proofs/run-run.t"))


(set (current-theory) (name->theory 'det-state-machines-with-start))

(def-constant after
  "lambda(a_seq:[nn,action], run(s_init, a_seq))"
  (theory det-state-machines-with-start)
  (usages transportable-macete))

(language-from-definition
 '(det-state-machine-sublanguage
   (embedded-languages det-state-machine-language start-det-state-machine-language)))
      
(define det-state-machines-subtheory
  (theory-from-definition
   '(det-state-machines-subtheory
     (language det-state-machine-sublanguage))))

(define det-state-machine-ensemble
  (build-theory-ensemble det-state-machines))

(define det-state-machine-start-ensemble
  (build-theory-ensemble det-state-machines-with-start))

(pop-current-theory)


