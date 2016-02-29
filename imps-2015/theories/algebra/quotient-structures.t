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


(herald quotient-structures)

(def-language relational-language
  (base-types uu)
  (constants 
   (equiv "[uu,uu,prop]"0)))

(def-parse-syntax equiv
  (left-method infix-operator-method)
  (binding 80))

(def-print-syntax equiv
  (token " equiv ")
  (method present-binary-infix-operator) 
  (binding 80))

(def-theory relational-theory
  (language relational-language)
  (component-theories h-o-real-arithmetic)
  (axioms
   (equiv-transitivity
    "forall(a,b,c:uu, a equiv b and b equiv c implies a equiv c)")
   (equiv-reflexivity
    "forall(a:uu, a equiv a)")
   (equiv-symmetry
    "forall(a,b:uu, a equiv b implies b equiv a)")))

(def-constant equiv%class
  "lambda(x:uu, indic{y:uu, x equiv y})"
  (theory relational-theory))

  
(def-constant equiv%class_q
  "lambda(a:sets[uu], forsome(y:uu, a=equiv%class(y)))"
  (theory relational-theory))

(def-theorem ()
  "forsome(a:sets[uu], equiv%class_q(a))"
  (theory relational-theory)
  (proof
   (
    (instantiate-existential ("with(x:uu,equiv%class(x))"))
    unfold-defined-constants
    unfold-defined-constants
    (instantiate-existential ("x"))
    unfold-defined-constants

    )))


(def-atomic-sort uu_q
  "equiv%class_q"
  (theory relational-theory))

;;;This is a possibility:

;;;(define (relational-replica-renamer i)
;;;  (lambda (name) 
;;;    (if (equal? name 'uu) 
;;;	(cond ((= i 0) 'uu)
;;;	      ((= i 1) 'vv)
;;;	      (else (imps-error "More than two copies for this ensemble.")))
;;;	(concatenate-symbol name '_ i))))
;;;
;;;(def-theory-ensemble RELATIONAL-THEORY
;;;  (replica-renamer relational-replica-renamer))
		     

(def-theory-ensemble RELATIONAL-THEORY)

(def-theory-ensemble-multiple relational-theory 2)

(def-theory-ensemble-overloadings relational-theory (1))

(def-overloading equiv
  (relational-theory equiv) 
  (relational-theory-2-tuples equiv_0)
  (relational-theory-2-tuples equiv_1))

(def-constant equiv%on%classes%unary
  "lambda(f:[uu_0,uu_1], forall(a,b:uu_0, a equiv b implies f(a) equiv f(b)))"
  (theory relational-theory-2-tuples))

;;;(def-constant quotient%unary
;;;  "lambda(f:[uu_0,uu_1], iota(g:[uu_q_0,uu_q_1], forall(x:uu_0, g(equiv%class
