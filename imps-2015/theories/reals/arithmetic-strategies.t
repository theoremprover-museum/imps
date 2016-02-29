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


(herald arithmetic-strategies)

(define trivial-integer-inductor
  (build-inductor-from-induction-principle
   (name->theorem 'induct)
   'trivial-integer-inductor
   '#f
   '#f))

(define integer-inductor
  (build-inductor-from-induction-principle
   (name->theorem 'induct)
   'integer-inductor
   (name->command 'unfold-defined-constants-repeatedly)
   '#f))

(define nonrecursive-integer-inductor
  (build-inductor-from-induction-principle
   (name->theorem 'induct)
   'nonrecursive-integer-inductor
   (name->command 'unfold-directly-defined-constants-repeatedly)
   '#f))

;;;******************commented out tentatively********************************

;;;(define (DEDUCTION-GRAPH-EQUIVALENCE-OF-ASSOCIATIVE-APPLICATIONS processor sqn)
;;;  (let ((assertion (universal-matrix (sequent-node-assertion sqn) '()))
;;;	(application? (lambda (x) (or (multiplication? processor x)
;;;				      (addition? processor x)))))
;;;    (if (or (and (quasi-equation? assertion)
;;;		 (application? (quasi-equation-lhs assertion))
;;;		 (application? (quasi-equation-rhs assertion)))
;;;	    (and (or (equation? assertion) (biconditional? assertion))
;;;		 (application? (expression-lhs assertion))
;;;		 (application? (expression-rhs assertion))))
;;;	
;;;	(let ((args-left (if (quasi-equation? assertion)
;;;			     (associative-arguments (quasi-equation-lhs assertion))
;;;			     (associative-arguments (expression-lhs assertion))))
;;;	      (args-right (if (quasi-equation? assertion)
;;;			      (associative-arguments (quasi-equation-rhs assertion))
;;;			      (associative-arguments (expression-rhs assertion)))))
;;;	  (receive (diff1 diff2)
;;;	    (match-up-expression-lists args-left args-right)
;;;	    (if (null? args-left) ;; if args-left is non-null, args-right is non-null.
;;;		(fail)
;;;		(let ((rhs (if (quasi-equation? assertion)
;;;			       (quasi-equation-rhs assertion)
;;;			       (expression-rhs assertion))))
;;;		  (cond ((addition? processor rhs)
;;;			 (deduction-graph-coerce-substitutions
;;;			  sqn
;;;			  (pair-individual-args-except-last   
;;;			   processor
;;;			   form-sum-expression
;;;			   diff1
;;;			   diff2)))
;;;			((multiplication? processor rhs)
;;;			 (deduction-graph-coerce-substitutions
;;;			  sqn
;;;			  (pair-individual-args-except-last   
;;;			   processor
;;;			   form-product-expression
;;;			   diff1
;;;			   diff2)))
;;;			(else (fail))))))))))
;;;
;;;
;;;(define (PAIR-INDIVIDUAL-ARGS-EXCEPT-LAST processor constructor l1 l2)
;;;  ;;assumes l1 has length <= that of l2.
;;;  (iterate loop ((l1 l1)  (l2 l2) (accum '()))
;;;    (if (null? (cdr l1))
;;;	;;if there is only one arg left in l1 pair it with the sum or product
;;;	;;of what's left  in l2.
;;;	 (cons (cons (car l1)
;;;		     (constructor processor l2))
;;;	       accum)
;;;	(block
;;;
;;;	  ;;otherwise, pair the first arg of l1 to the first of l2 and repeat.
;;;
;;;	  (loop (cdr l1) (cdr l2) (cons (cons (car l1) (car l2)) accum))))))
;;;
;;;
;;;(define (MATCH-UP-EXPRESSION-LISTS l1 l2)
;;;  (let ((inter (set-intersection l1 l2)))
;;;    (if (null? inter) (return l1 l2)
;;;	(let ((diff1 (set-difference l1 l2))
;;;	      (diff2 (set-difference l2 l1)))
;;;	  (if (< (length diff1) (length diff2))
;;;	      (return diff1 diff2)
;;;	      (return diff2 diff1))))))
;;;
;;;(theory-add-strategy
;;; *ho*
;;; (build-strategy
;;;  (lambda (sqn)
;;;    (deduction-graph-equivalence-of-associative-applications
;;;     (name->processor 'rr-algebraic-processor)
;;;     sqn))
;;; 'equate-assve-args))

;;;************************************************************************************

;;;(define (INEQUALITY-OR-NEGATION? processor expr)
;;;  (or (less-than? processor expr)
;;;      (less-than-or-equals? processor expr)
;;;      (and (negation? expr)
;;;	   (or (less-than? processor (car (expression-components expr)))
;;;	       (less-than-or-equals? processor (car (expression-components expr)))))))

;;;(theory-add-strategy
;;; h-o-real-arithmetic
;;; (build-strategy
;;;  (lambda (sqn)
;;;    (dg-primitive-inference-macete-application
;;;     sqn
;;;     (name->macete 'absolute-value-manipulations)))
;;;  'absolute-value-manipulations))


;;;(define (DEDUCTION-GRAPH-ROLL-THROUGH-NEGATED-EQUALITIES sqn)
;;;  (iterate loop ((assums (sequent-node-assumptions sqn)) (sqn sqn) (last-inference (fail)))
;;;    (if (null? assums)
;;;	last-inference
;;;	(if (negated-equation? (car assums))
;;;	    (let* ((contraposition (dg-primitive-inference-contraposition sqn (car assums)))
;;;		   (sqn1 (if (succeed-without-grounding? contraposition)
;;;			     (inference-node-1st-hypothesis contraposition)
;;;			     sqn))
;;;		   (simp (dg-primitive-inference-simplification sqn1))
;;;		   (sqn2 (if (succeed-without-grounding? simp)
;;;			     (inference-node-1st-hypothesis simp) sqn1)))
;;;
;;;	      (loop (cdr assums) sqn2 simp))
;;;	    (loop (cdr assums) sqn last-inference)))))
;;;	     
;;;(theory-add-strategy
;;; h-o-real-arithmetic
;;; (build-strategy
;;;  (lambda (sqn)
;;;    (deduction-graph-roll-through-negated-equalities sqn))
;;;  'roll-through-negated-equalities))

;;;(define (REAL-CASE-SPLIT sqn processor equation)
;;;  
;;;  (let ((<op (<r processor)))
;;;    (if (or (not <op) (not (equation? equation)))
;;;	(fail)
;;;	(let* ((lhs (expression-lhs equation))
;;;	       (rhs (expression-rhs equation))
;;;	       (assertion
;;;		(disjunction (apply-operator <op lhs rhs)
;;;			     (apply-operator <op rhs lhs)
;;;			     (equality rhs lhs)))
;;;	       (new-sqn 
;;;		(post
;;;		 (build-sequent
;;;		  (sequent-node-context sqn)
;;;		  assertion)
;;;		 (sequent-node-graph sqn))))
;;;	  (dg-primitive-inference-simplification new-sqn)
;;;	  (dg-primitive-inference-disjunction-elimination sqn new-sqn)))))
;;;
;;;
;;;(define (REAL-CASE-SPLIT-STRATEGY sqn processor string)
;;;  (let* ((sequent (sequent-node-sequent sqn))
;;;	 (assertion (sequent-read sequent string)))
;;;    (real-case-split sqn processor assertion)))
;;;
;;;(build-theory-command
;;; (lambda (sqn equation)
;;;   (real-case-split-strategy sqn (name->processor 'rr-order) equation))
;;; 'real-case-split
;;; (always '#t)
;;; (list *ho*)
;;; 'single-equation-retrieval-protocol)
