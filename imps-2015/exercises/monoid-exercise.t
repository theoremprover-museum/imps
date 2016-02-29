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


(herald monoid-exercise)

;                          MONOIDS EXERCISE
;
;A monoid is a set with an associative binary operation for which there is an identity.
;A group is an example of a monoid.
;We can define in monoids the "product" of a finite sequence of elements. Instances 
;of this product are the "Sigma" and "Pi" operators of arithmetic. 
;
;
(def-language monoid-language
   (embedded-languages h-o-real-arithmetic)
   (base-types uu)
   (constants
    (e uu)
    (** (uu uu uu))))

;Definition of the theory.

(def-theory monoid-theory
   (component-theories h-o-real-arithmetic)
   (language monoid-language)
   (axioms
    (associative-law-for-multiplication-for-monoids
     "forall(z,y,x:uu, x**(y**z)=(x**y)**z)" rewrite)
    (right-multiplicative-identity-for-monoids
     "forall(x:uu,x**e=x)" rewrite)
    (left-multiplicative-identity-for-monoids
     "forall(x:uu,e**x=x)" rewrite)

    ("total_q(**,[uu,uu,uu])" d-r-convergence)))
			  
(def-recursive-constant monoid%prod
 "lambda(pi:[zz,zz,[zz,uu],uu],lambda(m,n:zz,f:[zz,uu],
 if(m<=n,pi(m,n-1,f) ** f(n),e)))"
 (theory monoid-theory))

;Fancy TeX printing:

(def-print-syntax monoid%prod tex
    (token " \\prod ")
    (method present-tex-interval-iteration-operator)
    (binding 50))

;An "imps" convention is that double letters are printed out in TeX as boldface.

(make-tex-correspondence "uu" " \{ \\bf U \}")

(def-language GROUP-AS-MONOID-LANGUAGE
  (embedded-languages monoid-language)
  (constants (inv (uu uu ))))

(def-theory GROUPS-AS-MONOIDS
  (language group-as-monoid-language)
  (component-theories monoid-theory)
  (axioms
   (left-mul-inv
    "forall(x:uu, inv(x) ** x = e)" 
    rewrite)
   (right-mul-inv
    "forall(x:uu, x ** inv(x) = e)" 
    rewrite)
    ))

(set (current-theory) (name->theory 'groups-as-monoids))

(def-theorem INV-IS-TOTAL
  "total_q{inv,[uu,uu]}"
  (theory groups-as-monoids)
  (proof
   (


    insistent-direct-inference
    (cut-with-single-formula "x_0 ** inv(x_0) = e")
    (apply-macete-with-minor-premises right-mul-inv)
    ))

  (usages d-r-convergence transportable-macete))

(def-constant MINUS
  "lambda(x,y:uu,inv(y) ** x)"
  (theory groups-as-monoids)
  (usages rewrite))

(def-constant DELTA
  "lambda(f:[zz,uu],lambda(n:zz,minus(f(n+1),f(n))))"
  (theory groups-as-monoids)
  (usages rewrite))

;;(!)
;Prove

(def-theorem TELESCOPING-PROD-FORMULA
  "forall(f:[zz,uu],m,n:zz,m<=n and
                forall(j:zz,(m<=j and j<=n+1) implies #(f(j)))
                   implies monoid%prod(m,n,delta(f))=minus(f(n+1),f(m)))"
  (theory groups-as-monoids)
  (usages transportable-macete)
  (proof
   (
   


    (induction integer-inductor ())
    (prove-by-logic-and-simplification 3)
    (backchain "with(p:prop,p implies p);")
    direct-and-antecedent-inference-strategy
    simplify
    (force-substitution "((inv(f(m))**f(1+t))**inv(f(1+t)))**f(2+t)"
			"inv(f(m))**(f(1+t)**inv(f(1+t)))**f(2+t)"
			(0))
    (move-to-sibling 1)
    (apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)
    (apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)
    (apply-macete-with-minor-premises right-mul-inv)
    simplify
    simplify
    ))
)


(def-translation monoid-theory-to-additive-rr
  (source groups-as-monoids)
  (target h-o-real-arithmetic)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (uu rr))
  (constant-pairs
   (e 0)
   (inv -)
   (minus sub)
   (** +))
  (theory-interpretation-check using-simplification))

(set (current-theory) *ho*)

(def-renamer monoids-to-additive-rr-renamer
  (pairs (delta rr%delta)))

(def-transported-symbols (delta)
  (translation monoid-theory-to-additive-rr)
  (renamer monoids-to-additive-rr-renamer)
  )

(def-overloading delta
  (groups-as-monoids delta) (h-o-real-arithmetic rr%delta))


;;(!) Prove.

(def-theorem 1stnsquares
  "forall(n:zz,
     0<=n implies 
     sum(0,n,lambda(j:zz,j^2))=n*(n+1)*((2*n+1)/6))"
  (theory h-o-real-arithmetic)
  (proof
   (
  
    (cut-with-single-formula "lambda(j:zz,j^2)==delta(lambda(n:zz,(n-1)*n*((2*n-1)/6)))")
    (backchain "with(a,b:[zz,rr], a==b)")
    (apply-macete-with-minor-premises tr%telescoping-prod-formula)
    simplify
    (unfold-single-defined-constant (0) rr%delta)
    simplify
    )))

;;(!) Prove:

(def-theorem telescoping-example
  "forall(n:zz, 1<=n implies sum(1,n,lambda(i:zz,1/((3*i-2)*(3*i+1))))=(1/3)*(1- 1/(3*n+1)))"
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "lambda(i:zz,1/((3*i-2)*(3*i+1)))=delta(lambda(n:zz,-(1/3)*(1/(3*(n-1)+1))))")
    (move-to-sibling 1)
    (unfold-single-defined-constant (0) rr%delta)
    extensionality
    direct-and-antecedent-inference-strategy
    beta-reduce-repeatedly
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises fractional-expression-manipulation)
    (incorporate-antecedent "with(p:prop,p or p);")
    simplify
    (apply-macete-with-minor-premises definedness-manipulations)
    (force-substitution "3*x_0^2=[2/3]+x_0" "(x_0-[2/3])*(x_0+[1/3])=0" (0 1))
    (apply-macete-with-minor-premises cancel)
    simplify
    simplify
    simplify
    (backchain "with(f:[zz,rr],f=f);")
    (apply-macete-with-minor-premises tr%telescoping-prod-formula)
    beta-reduce-repeatedly
    simplify

    )))
