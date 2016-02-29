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


(herald reals)


;; This file illustrates the various levels of the IMPS system:
;;   (I) Theory = Language + Axioms
;;  (II) Processors handle lower level routines that allow the user 
;;       to do things with theories.


;; (I) THE THEORY

;; A theory is a complex object. Mathematically it consists of a language
;; and axioms.  We shall see that as a software entity a theory has more
;; structure.


;; (a) Definition of Languages

;; Mathematically a language is a class of well-formed expressions.
;; Implementing a language in software, means at the very least providing
;; the facility for building and inspecting expressions.  The
;; syntactically correct IMPS expressions are in 1-1 correspondence to
;; certain s-expressions.

(def-language pre-numerical-structures
  (extensible 
   (*integer-type* zz)
   (*rational-type* qq))
  (sorts 
   (rr ind) 
   (qq rr) 
   (zz qq))
  (constants
   (+ (rr rr rr))
   (* (rr rr rr))
   (- (rr rr))
   (/ (rr rr rr))	
   (< (rr rr prop))))

(def-language numerical-structures
  (embedded-language pre-numerical-structures)
  (constants
   (^ (rr zz rr))	 ;; partial function (0 with negative exps)
   (sub (rr rr rr))
   (<= (rr rr prop))))


;; (b) Definition of the Theory

(def-theory h-o-real-arithmetic
  (language numerical-structures)
  (axioms
   (trichotomy "forall(y,x:rr,x<y or x=y or y<x)")
   ("forall(y,x:rr,x<=y iff (x=y or x<y))")
   ("not(0<0)")
   (positivity-for-products "forall(y,x:rr,(0<=x and 0<=y) implies 0<=x*y)")
   ("forall(z,y,x:rr,x<=y iff x+z<=y+z)")
   (transitivity-of-<= "forall(z,y,x:rr,(x<=y and y<=z) implies x<=z)")
   (strict-positivity-for-products 
    "forall(y,x:rr,(0<x and 0<y) implies 0<x*y)")
   ("forall(z,y,x:rr,x<y iff x+z<y+z)")
   (transitivity "forall(z,y,x:rr,(x<y and y<z) implies x<z)")
   ("forall(x:rr,x+(-x)=0)")
   ("forall(x:rr,x+0=x)")
   ("forall(y,x:rr,x-y=x+(-y))")
   ("forall(y,x:rr, x/y==x*y^[-1])")
   ("forall(n,m:zz, x:rr ,#((x^m)^n,rr) implies (x^m)^n=x^(m*n))")
   ("forall(n,m:zz, x:rr ,((#(x^m,rr) and #(x^n,rr)) iff #((x^m)^n,rr)))")
   ("forall(m:zz, #(0^m,rr) implies 0^m=0)")
   ("forall(n:zz, #(1^n,rr) implies 1^n=1)")
   ("forall(x:rr,#(x^0,rr) implies x^0=1)")
   ("forall(x:rr,x^1=x)")
   ("forall(m:zz ,y,x:rr, (#(x^m*y^m,rr) or #((x*y)^m,rr)) implies x^m*y^m=(x*y)^m)")
   (sum-of-exponents-law
    "forall(n,m:zz, x:rr,#(x^m*x^n,rr) implies x^(m+n)=x^m*x^n)")
   (associative-law-for-multiplication "forall(z,y,x:rr,(x*y)*z=x*(y*z))")
   (left-distributive-law "forall(z,y,x:rr,x*(y+z)=x*y+x*z)")
   (multiplicative-identity "forall(x:rr,1*x=x)")
   (commutative-law-for-multiplication "forall(y,x:rr,x*y=y*x)")
   (associative-law-for-addition "forall(z,y,x:rr,(x+y)+z=x+(y+z))")
   (commutative-law-for-addition "forall(y,x:rr,x+y=y+x)")
   (order-discreteness "forall(m,n:zz, m<n iff m+1<=n)")
   (cancel "forall(a,b:rr,a*b=0 iff (a=0 or b=0))")

   (completeness
    "forall(p:[rr,prop], 
       nonvacuous_q{p} 
        and 
       forsome(alpha:rr, forall(theta:rr, p(theta) implies theta<=alpha)) 
         implies
       forsome(gamma:rr,
         forall(theta:rr, p(theta) implies theta<=gamma) 
          and 
         forall(gamma_1:rr, 
           forall(theta:rr, p(theta) implies theta<=gamma_1) 
            implies 
           gamma<=gamma_1)))")

   (induct
    "forall(s:[zz,prop],m:zz,
       forall(t:zz, m<=t implies s(t)) 
        iff 
       (s(m) and forall(t:zz,m<=t implies (s(t) implies s(t+1)))))")

   (zz-quotient-field "forall(x:qq, forsome(a,b:zz,x=a/b))")

   ("total_q(+,[rr,rr,rr])" d-r-convergence)
   ("total_q(*,[rr,rr,rr])" d-r-convergence)
   ("total_q(sub,[rr,rr,rr])" d-r-convergence)
   ("total_q(-,[rr,rr])" d-r-convergence)

   ("forall(x,y:rr,not(y=0) implies #(x/y))" d-r-convergence)
   ("forall(x,y:ind,y=0 implies not(#(x/y)))" d-r-convergence)

   ("forall(x:rr,y:zz,(0<y or not(x=0)) implies #(x^y))" d-r-convergence)
   ("forall(x,y:ind,#(y,zz) and x=0 and not(0<y) implies not(#(x^y)))"
    d-r-convergence)

   ("forall(x,y: zz, #(x+y,zz))" d-r-convergence)
   ("forall(x,y: zz, #(x*y,zz))" d-r-convergence)
   ("forall(x,y: zz, #(x-y,zz))" d-r-convergence)
   ("forall(x: zz, #(-x,zz))" d-r-convergence)

   ("forall(x,y: qq, #(x+y,qq))" d-r-convergence)
   ("forall(x,y: qq, #(x*y,qq))" d-r-convergence)
   ("forall(x,y: qq, #(x-y,qq))" d-r-convergence)
   ("forall(x: qq, #(-x,qq))" d-r-convergence)

   ("forall(x,y:ind,#(x,zz) and #(y,zz) implies #(x+y,zz))" d-r-convergence)
   ("forall(x,y:ind,#(x,zz) and #(y,zz) implies #(x*y,zz))" d-r-convergence)
   ("forall(x,y:ind,#(x,zz) and #(y,zz) implies #(x-y,zz))" d-r-convergence)
   ("forall(x:ind,#(x,zz) implies #(-x,zz))" d-r-convergence)
   ("forall(x,y:ind,
       #(x,zz) and #(y,zz) and (0<y or not(x=0)) implies #(x^y,qq))" 
    d-r-convergence)

   ("forall(x,y:ind,#(x,qq) and #(y,qq) implies #(x+y,qq))" d-r-convergence)
   ("forall(x,y:ind,#(x,qq) and #(y,qq) implies #(x*y,qq))" d-r-convergence)
   ("forall(x,y:ind,#(x,qq) and #(y,qq) implies #(x-y,qq))" d-r-convergence)
   ("forall(x:ind,#(x,qq) implies #(-x,qq))" d-r-convergence)
   ("forall(x,y:ind,
       #(x,qq) and #(y,zz) and (0<y or not(x=0)) implies #(x^y,qq))" 
    d-r-convergence)))


;; (II) ALGEBRAIC AND ORDER SIMPLIFICATION

;; We want the theory to allow the user to transform expressions. This
;; is done by procedures at various levels.


;; (a) Processors

;; Note that the processors are theory independent.

(def-algebraic-processor rr-algebraic-processor
  cancellative
  (language numerical-structures)
  (base ((scalars *rational-type*)
	  
	 ;; This declaration means that the map from rationals (elements 
         ;; of *rational-type*) to IMPS objects is a homomorphism for the 
         ;; operations below.
	  
	 (operations
	  (+ +)
	  (* *)
	  (- -)
	  (^ ^)
	  (/ /)
	  (sub sub))
	 use-numerals-for-ground-terms
	 commutes)))

(def-order-processor rr-order
  (algebraic-processor rr-algebraic-processor)
  (operations (< <) (<= <=))
  (discrete-sorts zz))


;; (b) Definition and Initialization of the Algebraic Transforms
  
(def-theory-processors h-o-real-arithmetic
 (algebraic-simplifier (rr-algebraic-processor * ^ + - / sub))
 (algebraic-order-simplifier (rr-order < <=))
 (algebraic-term-comparator rr-order))


;; (III) DEFINITION OF THE NATURAL NUMBERS

(def-atomic-sort nn
  "lambda(x:zz, 0<=x)"
  (theory h-o-real-arithmetic)
  (witness "0"))


;; (V) SOME DEFINITIONS

;; No mention has been made of parsing of expressions.

(def-recursive-constant sum
  "lambda(sigma:[zz,zz,[zz,rr],rr],
     lambda(m,n:zz,f:[zz,rr], if(m<=n,sigma(m,n-1,f)+f(n),0)))"
  (theory h-o-real-arithmetic)
  (definition-name sum))

(def-recursive-constant prod
  "lambda(pi:[zz,zz,[zz,rr],rr],
     lambda(m,n:zz,f:[zz,rr], if(m<=n,pi(m,n-1,f)*f(n),1)))"
  (theory h-o-real-arithmetic)
  (definition-name prod))

(def-constant factorial
  "lambda(n:zz,prod(1,n,lambda(j:zz,j)))"
  (theory h-o-real-arithmetic))

(def-constant >
  "lambda(x,y:rr,y<x)"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-constant >=
  "lambda(x,y:rr,y<=x)"
  (theory h-o-real-arithmetic)
  (usages rewrite))

(def-constant comb
  "lambda(m,k:zz,m!/(k! * (m-k)!))"
  (theory h-o-real-arithmetic))

(def-constant abs
  "lambda(r:rr,if(0<=r,r,-r))"
  (theory h-o-real-arithmetic))

(def-constant max
  "lambda(x,y:rr,if(x<=y,y,x))"
  (theory h-o-real-arithmetic))

(def-constant min
  "lambda(x,y:rr,if(x<=y,x,y))"
  (theory h-o-real-arithmetic))

(def-constant sqrt
  "lambda(x:rr, iota([[[y],rr]], 0<=y and y*y=x))"
  (theory h-o-real-arithmetic))

(def-constant ub_rr
  "lambda(s:[rr,prop],theta:rr,forall(rho:rr,s(rho) implies rho<=theta))"
  (theory h-o-real-arithmetic))

(def-constant lub_rr
  "lambda(s:[rr,prop],mu:rr,
     ub_rr(s,mu) and forall(eta:rr,ub_rr(s,eta)  implies mu<=eta))"
  (theory h-o-real-arithmetic))


;; (IV) INITIALIZATIONS

(set (current-theory) (name->theory 'h-o-real-arithmetic))
(set (current-language) '#f)
(define (cc) (theory-null-context (current-theory)))
(define *ho* (name->theory 'h-o-real-arithmetic))
(set (fixed-theories-set) (list (name->theory 'h-o-real-arithmetic)
				(name->theory 'the-kernel-theory)))

(define NN
  (name->sort (theory-language *ho*) 'nn))

(define ZZ
  (name->sort (theory-language *ho*) 'zz))

(define QQ
  (name->sort (theory-language *ho*) 'qq))

(define RR
  (name->sort (theory-language *ho*) 'rr))

 