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


(herald fields)

(load-section foundation)

(def-language FIELD-LANGUAGE
  (base-types kk)
  (constants
   (o_kk kk)
   (i_kk kk)
   (-_kk (kk kk))
   (+_kk (kk kk kk))
   (*_kk (kk kk kk))
   (inv (kk kk))))

(def-parse-syntax +_kk
  (left-method infix-operator-method) 
  (binding 100))

(def-parse-syntax *_kk
  (left-method infix-operator-method)
  (binding 120))

(def-parse-syntax -_kk
  (null-method  negation-operator-method)
  (binding 110))

(def-print-syntax +_kk
  (token " +_kk ")
  (method present-binary-infix-operator) 
  (binding 100))

(def-print-syntax  *_kk
  (token " *_kk ")
  (method  present-binary-infix-operator) 
  (binding 120))

(def-print-syntax  -_kk
  (token " -_kk ")
  (method  present-loglike-operator) 
  (binding 110))

(def-print-syntax  +_kk
  tex
  (token " \\oplus ") 
  (method present-tex-binary-infix-operator) 
  (binding 100))

(def-print-syntax  *_kk
  tex
  (token " \\otimes ") 
  (method  present-tex-binary-infix-operator) 
  (binding 120))

(def-print-syntax  -_kk
  tex
  (token " \\ominus ") 
  (method  present-loglike-operator) 
  (binding 110))


;Definition of the theory.

(def-theory FIELDS
  (component-theories h-o-real-arithmetic)
  (language field-language)
  (distinct-constants (i_kk o_kk))
  (axioms
   (associative-law-for-multiplication-for-fields
    "forall(z,y,x:kk,(x *_kk y) *_kk z=x *_kk (y *_kk z))")
   (left-distributive-law-for-fields
    "forall(z,y,x:kk,x *_kk (y +_kk z)=x *_kk y +_kk x *_kk z)")
   (multiplicative-identity-for-fields
    "forall(x:kk,i_kk  *_kk x = x)" rewrite)
   (additive-identity-for-fields
    "forall(x:kk,x +_kk o_kk = x)" rewrite)
   (additive-inverse-for-fields
    "forall(x:kk,x +_kk (-_kk x) = o_kk)" rewrite)
   (commutative-law-for-multiplication-for-fields
    "forall(y,x:kk,x *_kk y=y *_kk x)")
   (associative-law-for-addition-for-fields
    "forall(z,y,x:kk,(x +_kk y) +_kk z=x +_kk (y +_kk z))")
   (commutative-law-for-addition-for-fields
    "forall(y,x:kk,x +_kk y=y +_kk x)")
   (multiplicative-inverse-for-fields
    "forall(x:kk,not(x = o_kk) implies x *_kk inv(x)=i_kk)" )))

(def-theorem FIELD-ZERO-IS-NOT-FIELD-ONE
  "not(o_kk = i_kk)"
  (theory fields)
  (proof
   (
    simplify
    )))

(def-theorem ()
  "total_q(+_kk,[kk,kk,kk])"
  (theory fields)
  (usages d-r-convergence)
  (proof
   (
    insistent-direct-inference
    (assume-theorem commutative-law-for-addition-for-fields)
    )))


(def-theorem ()
  "total_q(*_kk,[kk,kk,kk])"
  (theory fields)
  (usages d-r-convergence)
  (proof
   (
    insistent-direct-inference
    (assume-theorem commutative-law-for-multiplication-for-fields)
    )))

(def-theorem ()
  "total_q(-_kk,[kk,kk])"	
  (theory fields)
  (usages d-r-convergence)
  (proof
   (
    insistent-direct-inference
    (assume-theorem additive-inverse-for-fields)
    )))
									  
;;;(def-algebraic-processor FIELD-ALGEBRAIC-PROCESSOR
;;;  (language field-language)
;;;  (base ((operations
;;;	  (+ +_kk)
;;;	  (* *_kk)
;;;	  (- -_kk)
;;;	  (zero o_kk)
;;;	  (unit i_kk))
;;;	 commutes)))
;;;
;;;(def-theory-processors
;;;  fields
;;;  (algebraic-simplifier (field-algebraic-processor *_kk +_kk -_kk))
;;;  (algebraic-term-comparator field-algebraic-processor))
;;;
;;;(make-tex-correspondence "kk" " \{ \\bf K \}")

(def-translation FIELDS-TO-RR-CORE
  (source fields)
  (target h-o-real-arithmetic)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (kk rr))
  (constant-pairs
   (o_kk 0)
   (i_kk 1)
   (-_kk -)
   (+_kk +)
   (*_kk *)
   (inv "lambda(x:rr,1/x)"))
 (theory-interpretation-check using-simplification))


