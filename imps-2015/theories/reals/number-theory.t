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


(herald NUMBER-THEORY)

(load-section reals)

;;; Even and odd

(def-constant EVEN
  "lambda(i:zz, forsome(j:zz, i=2*j))"
  (theory h-o-real-arithmetic))

(def-constant ODD
  "lambda(i:zz, forsome(j:zz, i=2*j+1))"
  (theory h-o-real-arithmetic))

(def-theorem EVEN-IFF-SUC-IS-ODD
  "forall(n:zz, even(n) iff odd(n+1))"
  reverse
  (theory h-o-real-arithmetic)
  (proof
   (
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("j"))
    (instantiate-existential ("j"))
    simplify
    )))

(def-theorem ODD-IFF-SUC-IS-EVEN
  "forall(n:zz, odd(n) iff even(n+1))"
  reverse
  (theory h-o-real-arithmetic)
  (proof
   (
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("j+1"))
    simplify
    (instantiate-existential ("j-1"))
    simplify
    )))

(def-theorem NATURAL-NUMBERS-ARE-EVEN-OR-ODD
  "forall(n:nn, even(n) or odd(n))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (cut-with-single-formula 
     "forall(n:zz, 0<=n implies forall(m:nn, m<=n implies (even(m) or odd(m))))")
    direct-inference
    (backchain "with(p:prop, p)")
    (instantiate-existential ("n"))
    (apply-macete-with-minor-premises nn-in-quasi-sort_h-o-real-arithmetic)
    simplify
    (induction integer-inductor ("n"))
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, forall(j:zz,p))")
    (instantiate-existential ("0"))
    simplify
    (cut-with-single-formula "m<=t or m=1+t")
    (antecedent-inference "with(p,q:prop, p or q)")
    (backchain "with(p:prop, forall(m:nn,p))")
    (cut-with-single-formula "even(t) or odd(t)")
    (force-substitution "m" "t+1" (0 1))
    (incorporate-antecedent "with(p,q:prop, p or q)")
    (apply-macete-locally even-iff-suc-is-odd (0) "even(t)")
    (apply-macete-locally odd-iff-suc-is-even (0) "odd(t)")
    direct-and-antecedent-inference-strategy
    simplify
    (instantiate-universal-antecedent "with(p:prop, forall(m:nn,p))" ("t"))
    (simplify-antecedent "with(p:prop, not(p))")
    simplify
    )))

(def-theorem EVEN-AND-ODD-NATURAL-NUMBERS-ARE-DISJOINT
  "forall(n:nn, odd(n) iff not even(n))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(p:prop, p)")
    unfold-defined-constants
    simplify
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop, p)")
    (weaken (0))
    (instantiate-theorem trichotomy ("j" "j_$0"))
    simplify
    simplify
    simplify
    (instantiate-theorem natural-numbers-are-even-or-odd ("n"))
    )))


;;; Integer quotient and modularity

(def-recursive-constant NN%QUOTIENT
  "lambda(f:[rr,rr,rr],
     lambda(m,n:rr,if(n=0, ?rr, if(m<n,0,1+f(m-n,n)))))"
  (theory h-o-real-arithmetic)
  (definition-name nn%quotient))

(def-constant ZZ%QUOTIENT
  "lambda(m,n:zz,
     if(m*n<0,
        nn%quotient(abs(m),abs(n))-1,
        nn%quotient(abs(m),abs(n))))"
  (theory h-o-real-arithmetic))

(comment
 (def-constant MOD
  "lambda(m,n:zz,abs(m-n*zz%quotient(m,n)))"
  (theory h-o-real-arithmetic)))


