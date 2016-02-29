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
;% COPYRIGHT NOTICE INSERTED: Fri Jun 30 10:59:36 EDT 1995

(herald octets)

;(*require nil '(imps presentation/read-bitop-numbers) imps-implementation-env)


(define (sharp? char) (char= char #\#))

(define (READ-WIDTH partial-char-sequence port)
  (iterate loop ((current-token '()))
    (let ((peek (peek-char port)))
      (cond ((or (eof? peek) (not (decimal-digit? peek)))
	     (bitop (implode (reverse! partial-char-sequence))
		      (implode (reverse! current-token))))
	    (else (loop (cons (read-char port) current-token)))))))

(define (READ-NUMERICAL-TOKEN port)
  (iterate loop ((current-token '()))
    (let ((peek (peek-char port)))
      (cond ((dot? peek) (read-decimal-part (cons (read-char port) current-token) port))
	    ((vertical? peek)
	     (read-char port)
	     (read-modular-base current-token port))
	    ((sharp? peek)
	     (read-char port)
	     (read-width current-token port))
	    ((or (eof? peek) (not (decimal-digit? peek)))
	     (implode (reverse! current-token)))
	    (else (loop (cons (read-char port) current-token)))))))

;(*require nil '(imps presentation/print-bitop-numbers) imps-implementation-env)


(define (write-sexp-leaves-to-port x port)
    (cond ((null? x))
	  ((string? x) (xtv-format port x))
	  ((symbol? x) (xtv-format port "~a" (tex-process-symbol x)))
	  ((bitop-number? x) (xtv-format port "~a" (representative x)))
	  ((atom? x) (xtv-format port "~a" x))
	  (else (write-sexp-leaves-to-port (car x) port)
		(write-sexp-leaves-to-port (cdr x) port))))

(def-language octet-language
  (extensible 
   (*octet-type* octet))
  (base-types octet)
  (constants
   (logxor (octet octet octet))
   (logand (octet octet octet))
   (logneg (octet octet))))

(def-theory pre-octets
  (language octet-language)
  (component-theories h-o-real-arithmetic)
  (axioms
   ("forall(x:octet,logxor(x,logneg(x))=0#8)")
   (logand-is-idempotent
    "forall(x:octet,logand(x,x)=x)" rewrite)
   (associativity-of-logand
    "forall(x,y,z:octet,logand(logand(x,y),z)=logand(x,logand(y,z)))")
   ("forall(c,y,z:octet, 
       logand(c,logxor(y,z))=logxor(logand(c,y),logand(c,z)))")
   ("forall(x:octet,logand(255#8,x)=x)")
   ("forall(x,y:octet,logand(x,y)=logand(y,x))")
   (associativity-of-logxor
    "forall(x,y,z:octet,logxor(logxor(x,y),z)=logxor(x,logxor(y,z)))")
   ("forall(x:octet,logxor(x,0#8)=x)")
   ("forall(x,y:octet,logxor(x,y)=logxor(y,x))")))

(def-theorem logand-is-total
  "total_q{logand,[octet,octet -> octet]}"
  (usages d-r-convergence)
  (theory pre-octets)
  (proof
   (

    insistent-direct-inference
    (instantiate-theorem associativity-of-logand ("x_0" "x_1" "x_1"))

    )))

(def-theorem logxor-is-total
  "total_q{logxor,[octet,octet -> octet]}"
  (usages d-r-convergence)
  (theory pre-octets)
  (proof
   (

    insistent-direct-inference
    (instantiate-theorem associativity-of-logxor ("x_0" "x_1" "x_1"))

    )))

(def-constant atomic%octet
  "lambda(x:octet, 
     not(x=0#8) 
      and 
     forall(y:octet, logand(x,y)=y implies y=x or y=0#8))"
  (theory pre-octets))

(def-theory octets
  (component-theories pre-octets)
  (axioms
   (atom-1 "atomic%octet(1#8)")
   (atom-2 "atomic%octet(2#8)")
   (atom-4 "atomic%octet(4#8)")
   (atom-8 "atomic%octet(8#8)")
   (atom-16 "atomic%octet(16#8)")
   (atom-32 "atomic%octet(32#8)")
   (atom-64 "atomic%octet(64#8)")
   (atom-128 "atomic%octet(128#8)")
   ))

(def-algebraic-processor octet-algebraic-processor
  (language octets)
  (base ((scalars *octet-type*)
	  
	 ;; This declaration means that the map from octets (elements 
         ;; of *octet-type*) to IMPS objects is a homomorphism for the 
         ;; operations below.
	  
	 (operations
	  (+ logxor)
	  (* logand)
	  (- logneg))
	 use-numerals-for-ground-terms
	 commutes)))

(def-theory-processors octets
 (algebraic-simplifier (octet-algebraic-processor logxor logand logneg))
 (algebraic-term-comparator octet-algebraic-processor))

(def-theorem logand-simplification-lemma-1
  "forall(o_1,o_2:octet, 
     logand(logand(o_1,o_2),o_2) = logand(o_1,o_2))"
  lemma
  (theory octets)
  (proof
   (

    simplify
    (apply-macete-with-minor-premises logand-is-idempotent)
    simplify

    )))

(def-theorem octet-unit-decomposition
  "with(o:octet,
     255#8 = 
     logxor(1#8,
            logxor(2#8,
                   logxor(4#8,
                          logxor(8#8,
                                 logxor(16#8,
                                        logxor(32#8,
                                               logxor(64#8,
                                                      128#8))))))))"
  (theory octets)
  (proof
   (

    simplify

    )))

(def-theorem octet-decomposition
  "forall(o:octet,
     o = 
     logxor(logand(1#8,o),
            logxor(logand(2#8,o),
                   logxor(logand(4#8,o),
                          logxor(logand(8#8,o),
                                 logxor(logand(16#8,o),
                                        logxor(logand(32#8,o),
                                               logxor(logand(64#8,o),
                                                      logand(128#8,o)))))))))"
  (theory octets)
  (proof
   (

    simplify

    )))

(def-constant octet%to%nn
  "lambda(o:octet,
    if(logand(1#8,o) = 1#8,1,0) * 2^0
     +
    if(logand(2#8,o) = 2#8,1,0) * 2^1
     +
    if(logand(4#8,o) = 4#8,1,0) * 2^2
     +
    if(logand(8#8,o) = 8#8,1,0) * 2^3
     +
    if(logand(16#8,o) = 16#8,1,0) * 2^4
     +
    if(logand(32#8,o) = 32#8,1,0) * 2^5
     +
    if(logand(64#8,o) = 64#8,1,0) * 2^6
     +
    if(logand(128#8,o) = 128#8,1,0) * 2^7)"
  (theory octets))

(def-theorem octet%to%nn-is-injective
  "forall(o_1,o_2:octet, 
     octet%to%nn(o_1) = octet%to%nn(o_2) implies o_1 = o_2)"
  (theory octets)
  (proof
   (

    (informal-justification 
     "Follows from the fact that two polynomials in a natural number n 
      with natural number coefficients less than n are equal iff their 
      coefficients are equal.")

    )))

(def-constant octet%lt
  "lambda(o_1,o_2:octet, octet%to%nn(o_1) < octet%to%nn(o_2))"
  (usages rewrite)
  (theory octets))

(def-constant octet%le
  "lambda(o_1,o_2:octet, octet%to%nn(o_1) < octet%to%nn(o_2) or o_1 =o_2)"
  (usages rewrite)
  (theory octets))

(def-theorem octet%lt-irreflexivity
  "forall(o:octet, not(octet%lt(o,o)))"
  (theory octets)
  (proof
   (

    (unfold-single-defined-constant-globally octet%lt)
    simplify

    )))

(def-theorem octet%lt-trichotomy
  "forall(o_1,o_2:octet, 
     octet%lt(o_1,o_2) or o_1 = o_2 or octet%lt(o_2,o_1))"
  (theory octets)
  (proof
   (


    (unfold-single-defined-constant-globally octet%lt)
    direct-inference
    (instantiate-theorem trichotomy ("octet%to%nn(o_2)" "octet%to%nn(o_1)"))
    direct-inference
    (block 
      (script-comment "`instantiate-theorem' at (0 1)") direct-inference
      (contrapose "with(o_2,o_1:octet,not(o_1=o_2));")
      (instantiate-theorem octet%to%nn-is-injective ("o_1" "o_2"))
      )
    direct-inference
    (block 
      (script-comment "`instantiate-theorem' at (1 1 0)")
      (unfold-single-defined-constant (0) octet%to%nn) simplify
      )
    (unfold-single-defined-constant (0) octet%to%nn)
    )))

;    (unfold-single-defined-constant-globally octet%lt)
;    direct-inference
;    (instantiate-theorem 
;     trichotomy 
;     ("octet%to%nn(o_2)" "octet%to%nn(o_1)"))
;    direct-inference
;    (block 
;      (script-comment "`instantiate-theorem' at (0 1)")
;      direct-inference
;      (contrapose "with(o_2,o_1:octet,not(o_1=o_2));")
;      (instantiate-theorem octet%to%nn-is-injective ("o_1" "o_2")))
;    direct-inference


(def-theorem octet%lt-transitivity
  "forall(o_1,o_2,o_3:octet, 
     octet%lt(o_1,o_2) and octet%lt(o_2,o_3) implies octet%lt(o_1,o_3))"
  (theory octets)
  (proof
   (

    (unfold-single-defined-constant-globally octet%lt)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises transitivity)
    auto-instantiate-existential

    )))



(comment

 (def-parse-syntax logand
   (left-method infix-operator-method)
   (binding 100))

 (def-print-syntax logand
   (token " logand ")
   (method present-binary-infix-operator) 
   (binding 100))

 (def-print-syntax logand
   tex
   (token " logand ")
   (method present-tex-binary-infix-operator) 
   (binding 100))

 (def-parse-syntax logxor
   (left-method infix-operator-method)
   (binding 120))

 (def-print-syntax logxor
   (token " logxor ")
   (method present-binary-infix-operator) 
   (binding 120))

 (def-print-syntax logxor
   tex
   (token " logxor ")
   (method present-tex-binary-infix-operator) 
   (binding 120))

)