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


(herald policy)

(*require nil '(generic_theories pairs) imps-implementation-env)

(*require nil '(theories state-machines/deterministic-state-machines)
	  imps-implementation-env)


(push-current-theory)
(push-current-syntax)
(set (use-string-form?) '#t)

(language-from-definition
 '(pre-policy-language
   (base-types uu ll)))

(define pre-policy-theory
  (theory-from-definition
   '(pre-policy-theory
     (language pre-policy-language))))

(set (current-theory) pre-policy-theory)

(theory-import-transportable-rewrite-rules pre-policy-theory (list pairs sequences))

(cartesian-product pre-policy-theory 'entry '(uu ll))

;; (let ((entry-def (build-sort-definition
;; 		  pre-policy-theory
;; 		  'entry
;; 		  (qr "lambda(e:sets[uu,ll], pair_q{e})"))))
;;   
;;   (theory-add-theorem 
;;    pre-policy-theory
;;    (nonemptyness-formula entry-def)
;;    'nonemptyness-for-entry)
;;   (theory-add-sort-definition
;;    pre-policy-theory
;;    entry-def))

(power-set pre-policy-theory 'state '(entry))

;;;
;;;(let ((state-def (build-sort-definition
;;;		  pre-policy-theory
;;;		  'state
;;;		  (qr "lambda(s:sets[entry], truth)"))))
;;;  
;;;  (theory-add-theorem 
;;;   pre-policy-theory
;;;   (nonemptyness-formula state-def)
;;;   'nonemptyness-for-state)
;;;  (theory-add-sort-definition
;;;   pre-policy-theory
;;;   state-def))

(theory-build-definition 
  pre-policy-theory
  'committed
  (qr "lambda(u:uu,s:state, forsome(l:ll, pair{u,l} in s))")
  '())

(theory-build-definition 
  pre-policy-theory
  'next
  (qr "lambda(s:state, e:entry, if(not(committed(first{e},s)), s union singleton{e}, s))")
  '())

(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "forall(e:sets[uu,ll], 
 pair_q{e} implies #(e,entry))")
 'entry-definedness
 '(d-r-convergence))

(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "forall(e:sets[uu,ll], 
 #(e,entry) iff pair_q{e})")
 'entry-rewrite
 '(rewrite))
(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "forall(e:entry, #(first{e}))")
 'entry-first-defined
 '(rewrite)
 "$THEORIES/state-machines/proofs/policy-entry-first-defined.t")

(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "forall(e:entry, #(second{e}))")
 'entry-second-defined
 '(rewrite)
 "$THEORIES/state-machines/proofs/policy-entry-second-defined.t")

(theory-verify-and-add-theorem				
 pre-policy-theory					;just simplify
 (qr "forall(e:entry, pair_q{e})")
 'entry-is-pair
 '(rewrite)
 "")

(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "forall(s:state, e:entry,
	      not(committed(first{e},s))
	 implies next(s,e)=s union singleton{e})")
 'next-uncommitted
 '())

(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "forall(s:state, e:entry,
	      not(committed(first{e},s))
	 implies s union singleton{e}=next(s,e))")
 'next-uncommitted-alt
 '())

(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "forall(s:state, e:entry,
	      committed(first{e},s)
	 implies next(s,e)=s)")
 'next-committed
 '())

(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "total_q{next,[state,entry,sets[entry]]}")
 'next-total
 '(d-r-convergence))


(define dsm->pol-tr
  (translation-from-definition
   '(dsm->pol-tr
     (source det-state-machines-subtheory)
     (target pre-policy-theory)
     (sort-pairs
      (state state)
      (action entry))
     (constant-pairs
      (s_init "empty_indic{entry}")
      (next next)))))

(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "#(empty_indic{entry},state)")
 'empty-entry-set-is-state
 '())

(theory-verify-and-add-theorem				
 pre-policy-theory
 (qr "#(next,[state,entry,state])")
 'next-is-transition-fn
 '())

(theory-interpretation-check-using-simplification dsm->pol-tr)

(define det-with-start->pol-machine
  (transport-theory
   dsm->pol-tr det-state-machines-with-start pre-policy-theory (list h-o-real-arithmetic)
   (default-namer 'dp) 'dsm->pm 'dp 'policy-machine))

(define policy-machine (translation-target-theory det-with-start->pol-machine))

(set (current-theory) policy-machine)
(theory-import-transportable-rewrite-rules policy-machine (list pairs sequences))

(theory-build-definition
 policy-machine
 'policy
 (qr "lambda(s:state, forall(e_1, e_2:entry, e_1 in s and e_2 in s and first{e_1}=first{e_2} implies e_1=e_2))"))
 

(define dp%dsm-inductor
  (build-translated-inductor-from-induction-principle
   det-with-start->pol-machine
   (name->theorem 'dsm-induction-biconditional-conv)
   'dp%dsm-inductor
   (name->macete 'eliminate-nonrecursive-definitions-and-simplify)
   '#f))


(theory-verify-and-add-theorem				
 policy-machine
 (qr "forall(a:entry,s:state, 
 forsome(e_0,e_1:entry, 
 e_1=a and first{e_1}=first{e_0} and e_0 in s) 
 implies
forsome(l_0:ll, 
 pair{first{a},l_0} in s))")
 'policy-first-membership-lemma
 '()
 "$THEORIES/state-machines/proofs/policy-first-membership-lemma.t")
 

(theory-verify-and-add-theorem				
 policy-machine
 (qr "forall(s:state,a:entry, 
    not(committed(first{a},s)) and policy(s) 
implies policy(s union singleton{a}))")
 'policy-preservation
 '()
 "")
(disable-quasi-constructor includes)
(qr "forall(s:state, dp%accessible(s) implies policy(s))")


(pop-current-syntax)
(pop-current-theory)
