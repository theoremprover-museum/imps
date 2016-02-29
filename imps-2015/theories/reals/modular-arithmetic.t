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


(herald modular-arithmetic)

(include-files
 (files    (imps theories/reals/primes)))

(def-theorem relatively%prime-characterization
  "forall(a,b:zz, relatively%prime(a,b) iff forsome(k,l:zz, k*a+l*b=1))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant-globally relatively%prime)
    (unfold-single-defined-constant-globally gcd)
    (apply-macete-with-minor-premises iota-free-characterization-of-generator)
    direct-and-antecedent-inference-strategy

      
    (incorporate-antecedent "with(f:sets[zz],f=f);")
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (unfold-single-defined-constant (1) princ%ideal)
    simplify
    (unfold-single-defined-constant (0) divides)
    simplify
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(f:[zz,prop],pred_to_indic(f) subseteq pred_to_indic(f));")
    (move-to-ancestor 1)
    (contrapose "with(f:[zz,prop],pred_to_indic(f) subseteq pred_to_indic(f));")
    (instantiate-existential ("1"))
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    (contrapose "with(p:prop,forall(k,l:zz,p));")
    (instantiate-existential ("r" "s"))
    (unfold-single-defined-constant (0) princ%ideal)
    simplify

    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (unfold-single-defined-constant (0) princ%ideal)
    direct-and-antecedent-inference-strategy
    simplify
    (unfold-single-defined-constant (0) divides)
    simplify
    (unfold-single-defined-constant (0) princ%ideal)
    simplify
    (unfold-single-defined-constant (0) divides)
    simplify
    insistent-direct-inference
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("k*x_$1" "l*x_$1"))
    (cut-with-single-formula "x_$1<0 or x_$1=0 or 0<x_$1")
    (move-to-sibling 1)
    simplify
    (antecedent-inference "with(p:prop,p or p or p);")
    simplify
    simplify
    simplify
    )))


(def-theorem relative-primality-symmetry
  "forall(a,b:zz, relatively%prime(a,b) iff relatively%prime(b,a))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (apply-macete-with-minor-premises relatively%prime-characterization)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("l" "k"))
    simplify
    (instantiate-existential ("l" "k"))
    simplify
    )))



(def-theorem mod-characterization
  "forall(a,c,r:zz, 0<a implies (c mod a =r  iff (a divides c-r and 0<=r and r <a)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    (script-comment "Let's back up a little bit")

    (block 

     (backchain-backwards "with(r:rr,r)=with(r:zz,r);")
     (backchain-backwards "with(r:rr,r)=with(r:zz,r);")
     (backchain-backwards "with(r:rr,r)=with(r:zz,r);")
     (apply-macete-with-minor-premises division-with-remainder))

    (block

     (unfold-single-defined-constant-globally mod)
     (force-substitution "c-a*floor(c/a)=r" "floor(c/a)=(c-r)/a" (0))
     (block
       (script-comment "Prove the minor premise first.")
       (move-to-sibling 1)
       (apply-macete-with-minor-premises fractional-expression-manipulation)
       simplify
       )
     (apply-macete-with-minor-premises floor-characterization)
     (apply-macete-with-minor-premises fractional-expression-manipulation)
     (incorporate-antecedent "with(r:rr,a:zz,a divides r);")
     (apply-macete-with-minor-premises divisibility-lemma)
     direct-and-antecedent-inference-strategy
     simplify
     simplify

     (block
       (script-comment "Floor characterization produced a minor
                        premise that someting is an integer.")
       (incorporate-antecedent "with(r:rr,a:zz,a divides r);")
       (unfold-single-defined-constant (0) divides)
       simplify)
     )
    ))) 

; The following has been moved to reals-supplements

;(def-theorem mod-of-integer-is-integer
;  "forall(a,b:zz, not(b=0) implies #(a mod b,zz))"
;  (theory h-o-real-arithmetic)
;  (proof
;   (


;    direct-and-antecedent-inference-strategy
;    (unfold-single-defined-constant (0) mod)
;    sort-definedness

;    )))

(def-theorem relatively-prime-mod-characterization
  "forall(a,b:zz, 1<a implies (relatively%prime(a,b) iff forsome(k:zz, (k*b) mod a = 1)))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (apply-macete-with-minor-premises relatively%prime-characterization)
    (apply-macete-with-minor-premises mod-characterization)
    (apply-macete-with-minor-premises divisibility-lemma)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("l"))
    (instantiate-existential ("-k"))
    simplify
    simplify
    (instantiate-existential ("-k_$0" "k"))
    simplify
    )))



(def-constant congruent
  "lambda(a,b,m:zz, m divides b-a)"
  (theory h-o-real-arithmetic))

(def-theorem congruence-characterization
  "forall(a,b,k:zz, 0<k implies (congruent(a,b,k) iff a mod k = b mod k))"
  reverse
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant-globally congruent)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    (cut-with-single-formula "forsome(l:zz, b mod k = l)")
    (antecedent-inference "with(p:prop,forsome(l:zz,p));")
    (backchain "with(l:zz,r:rr,r=l);")
    (incorporate-antecedent "with(l:zz,r:rr,r=l);")
    (apply-macete-with-minor-premises mod-characterization)
    (apply-macete-with-minor-premises divisibility-lemma)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("-k_$0+k_$1"))
    simplify
    (instantiate-existential ("k_$1-k_$0"))
    simplify
    (instantiate-existential ("b mod k"))
    simplify
    (unfold-single-defined-constant (0) mod)
    simplify
    (unfold-single-defined-constant (0) mod)
    simplify

    )))


(def-theorem congruence-symmetric
  "forall(a,b,k:zz, congruent(a,b,k) iff congruent(b,a,k))"
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant-globally congruent)
    direct-and-antecedent-inference-strategy
    (let-script replace 2
		(
		 (force-substitution (% "~A-~A" $1 $2) (% "[-1]*(~A-~A)" $2 $1) (0))
		 (move-to-sibling 1)
		     
		 simplify
		 (apply-macete-with-minor-premises multiplication-preserves-divisibility)

		 ))
    ($replace "a" "b")
    ($replace "b" "a")
    )))

(def-theorem congruence-transitive
  "forall(a,b,c,k:zz, congruent(a,b,k) and congruent(b,c,k) implies  congruent(a,c,k))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant-globally congruent)
    (force-substitution "c-a" "(c-b)+(b-a)" (0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises addition-preserves-divisibility)
    direct-and-antecedent-inference-strategy
    )))

(def-theorem congruence-reflexive
  "forall(a,k:zz, not(k=0) implies congruent(a,a,k))"
  (theory h-o-real-arithmetic)
  (proof
   (

    (unfold-single-defined-constant (0) congruent)
    (unfold-single-defined-constant (0) divides)
    simplify

    )))


(def-theorem multiplication-congruence-invariance-lemma
  "forall(a,b,c,k:zz, congruent(a,b,k) implies congruent(c*a,c*b,k))" 
  (theory h-o-real-arithmetic)
  (proof
   (


    (unfold-single-defined-constant-globally congruent)
    direct-and-antecedent-inference-strategy
    (force-substitution "c*b-c*a" "c*(b-a)" (0))
    (move-to-sibling 1)
    simplify
    (apply-macete-with-minor-premises multiplication-preserves-divisibility)
    )))
  


(def-theorem addition-congruence-invariance-lemma
  "forall(a,b,c,k:zz, congruent(a,b,k) implies congruent(c+a,c+b,k))" 
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant-globally congruent)
    simplify
    
    )))
  
;;(set (proof-log-port) (standard-output))


(def-language arithmetic-mod-n
  (embedded-languages h-o-real-arithmetic)
  (constants (modulus zz)))

(def-theory arithmetic-mod-n
  (language arithmetic-mod-n)
  (component-theories h-o-real-arithmetic)
  (axioms
    
    (proper-generator "1<modulus")))


(def-atomic-sort zz_mod
  "lambda(k:zz, 0<=k and k<modulus)"
  (theory arithmetic-mod-n)
  (witness "0"))


(def-theorem mod-n-range-in-zz_mod
  "forall(a:zz, #(a mod modulus ,zz_mod))"
  (theory arithmetic-mod-n)
  (proof
   (


    (apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (apply-macete-with-minor-premises mod-of-integer-is-integer)
    simplify
    direct-inference
    (cut-with-single-formula "forsome(k:zz, a mod modulus =k)")
    (move-to-sibling 1)
    (instantiate-existential ("a mod modulus"))
    simplify
    (cut-with-single-formula "#(a mod modulus,zz)")
    (apply-macete-with-minor-premises mod-of-integer-is-integer)
    simplify
    (antecedent-inference "with(p:prop,p);")
    (backchain "with(p:prop,p);")
    (backchain "with(p:prop,p);")
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises mod-characterization)
    direct-and-antecedent-inference-strategy
    )))

(def-constant *_mod
  "lambda(a,b:zz_mod, a * b mod modulus)"
  (theory arithmetic-mod-n))

(def-theorem *_mod-characterization
  "forall(a,b,c:zz_mod, *_mod(a,b)=c iff (0<=c and c<modulus and congruent(a*b,c,modulus)))"
  (theory arithmetic-mod-n)
  (proof
   (


    (unfold-single-defined-constant-globally *_mod)
    (apply-macete-with-minor-premises congruence-characterization)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises mod-characterization)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(c:zz_mod,r:rr,r=c);")
    (apply-macete-with-minor-premises mod-characterization)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "c mod modulus = c")
    (apply-macete-with-minor-premises mod-characterization)
    (unfold-single-defined-constant (0) divides)
    simplify
    (cut-with-single-formula "c mod modulus = c")
    (apply-macete-with-minor-premises mod-characterization)
    (unfold-single-defined-constant (0) divides)
    simplify

    )))

(def-theorem *_mod-identity
  "forall(a:zz_mod, *_mod(a,1)=a)"
  (theory arithmetic-mod-n)
  (proof
   (


    (unfold-single-defined-constant-globally *_mod)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises mod-characterization)
    (unfold-single-defined-constant (0) divides)
    simplify
    (apply-macete-with-minor-premises zz_mod-in-quasi-sort_arithmetic-mod-n)

    )))

(def-theorem *_mod-total
  "forall(a,b:zz_mod, #(*_mod(a,b),zz_mod))"
  (theory arithmetic-mod-n)
  (proof
   (


    (unfold-single-defined-constant (0) *_mod)
    (apply-macete-with-minor-premises mod-n-range-in-zz_mod)
    )))


(def-theorem mult_mod-associative-lemma-1
  "forall(a,b,c:zz_mod, *_mod(a,*_mod(b,c))= a*(b*c) mod modulus)"
  (theory arithmetic-mod-n)
  lemma
  (proof
   (


    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally *_mod)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (apply-macete-with-minor-premises mod-n-range-in-zz_mod)
    (apply-macete-with-minor-premises rev%congruence-characterization)
    (unfold-single-defined-constant (0) congruent)
    beta-reduce-with-minor-premises
    (apply-macete-with-minor-premises divisibility-lemma)
    (move-to-sibling 1)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)") sort-definedness
      (apply-macete-with-minor-premises mod-of-integer-is-integer) simplify
      )
    (cut-with-single-formula "forsome(k:zz, b*c mod modulus=k)")
    (move-to-sibling 1)
    (instantiate-existential ("b*c mod modulus"))
    (antecedent-inference "with(p:prop,p);")
    (backchain "with(p:prop,p);")
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises mod-characterization)
    (apply-macete-with-minor-premises divisibility-lemma)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("k_$0*a"))
    (block 
      (script-comment "`instantiate-existential' at (0)")
      (force-substitution "a*(b*c)-a*k" "a*(b*c-k)" (0)) (move-to-sibling 1) simplify
      (block 
	(script-comment "`force-substitution' at (0)") (backchain "with(r:rr,r=r);")
	simplify
	) )
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0 0 1)")
      direct-and-antecedent-inference-strategy sort-definedness
      (apply-macete-with-minor-premises mod-of-integer-is-integer)
      )

    )))


(def-theorem mult_mod-associative-lemma-2
  "forall(a,b,c:zz_mod, *_mod(*_mod(b,c),a)= (b*c)*a mod modulus)"
  (theory arithmetic-mod-n)
  lemma
  (proof
   (


    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally *_mod)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (apply-macete-with-minor-premises mod-n-range-in-zz_mod)
    (block 
      (script-comment "`beta-reduce-with-minor-premises' at (0)")
      (apply-macete-with-minor-premises rev%congruence-characterization)
      (unfold-single-defined-constant (0) congruent) beta-reduce-with-minor-premises
      (block 
	(script-comment "`beta-reduce-with-minor-premises' at (0)")
	(apply-macete-with-minor-premises divisibility-lemma) (move-to-sibling 1)
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)") sort-definedness
	  (apply-macete-with-minor-premises mod-of-integer-is-integer) simplify
	  )
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  (cut-with-single-formula "forsome(k:zz, b*c mod modulus=k)") (move-to-sibling 1)
	  (instantiate-existential ("b*c mod modulus"))
	  (block 
	    (script-comment "`cut-with-single-formula' at (0)")
	    (antecedent-inference "with(p:prop,p);") (backchain "with(p:prop,p);")
	    (incorporate-antecedent "with(p:prop,p);")
	    (apply-macete-with-minor-premises mod-characterization)
	    (apply-macete-with-minor-premises divisibility-lemma)
	    direct-and-antecedent-inference-strategy
	    (force-substitution "b*c*a-k*a" "a*(b*c-k)" (0)) (move-to-sibling 1) simplify
	    (block 
	      (script-comment "`force-substitution' at (0)")
	      (instantiate-existential ("k_$0*a")) (backchain "with(r:rr,r=r);") simplify
	      ) ) ) )
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0 0 1)")
	direct-and-antecedent-inference-strategy sort-definedness
	(apply-macete-with-minor-premises mod-of-integer-is-integer)
	) )

    )))

(def-theorem mult_mod-associative
  "forall(a,b,c:zz_mod, *_mod(a,*_mod(b,c))=*_mod(*_mod(a,b),c))"
  (theory arithmetic-mod-n)
  (proof
   (


    (apply-macete-with-minor-premises mult_mod-associative-lemma-1)
    (apply-macete-with-minor-premises mult_mod-associative-lemma-2)
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(c*b*a mod modulus,zz_mod)")
    simplify
    (apply-macete-with-minor-premises mod-n-range-in-zz_mod)
    )))

;;Modular addition almost verbatim.

(def-constant +_mod
  "lambda(a,b:zz_mod, a + b mod modulus)"
  (theory arithmetic-mod-n))

(def-theorem +_mod-characterization
  "forall(a,b,c:zz_mod, +_mod(a,b)=c iff (0<=c and c<modulus and congruent(a+b,c,modulus)))"
  (theory arithmetic-mod-n)
  (proof
   (


    (unfold-single-defined-constant-globally +_mod)
    (apply-macete-with-minor-premises congruence-characterization)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises mod-characterization)
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(c:zz_mod,r:rr,r=c);")
    (apply-macete-with-minor-premises mod-characterization)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "c mod modulus = c")
    (apply-macete-with-minor-premises mod-characterization)
    (unfold-single-defined-constant (0) divides)
    simplify
    (cut-with-single-formula "c mod modulus = c")
    (apply-macete-with-minor-premises mod-characterization)
    (unfold-single-defined-constant (0) divides)
    simplify

    )))

(def-theorem +_mod-identity
  "forall(a:zz_mod, +_mod(a,0)=a)"
  (theory arithmetic-mod-n)
  (proof
   (


    (unfold-single-defined-constant-globally +_mod)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises mod-characterization)
    (unfold-single-defined-constant (0) divides)
    simplify
    (apply-macete-with-minor-premises zz_mod-in-quasi-sort_arithmetic-mod-n)

    )))

(def-theorem +_mod-total
  "forall(a,b:zz_mod, #(+_mod(a,b),zz_mod))"
  (theory arithmetic-mod-n)
  (proof
   (


    (unfold-single-defined-constant (0) +_mod)
    (apply-macete-with-minor-premises mod-n-range-in-zz_mod)
    )))


(def-theorem plus_mod-associative-lemma-1
  "forall(a,b,c:zz_mod, +_mod(a,+_mod(b,c))= a+(b+c) mod modulus)"
  (theory arithmetic-mod-n)
  lemma
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally +_mod)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (apply-macete-with-minor-premises mod-n-range-in-zz_mod)
    (apply-macete-with-minor-premises rev%congruence-characterization)
    (unfold-single-defined-constant (0) congruent)
    beta-reduce-with-minor-premises
    (apply-macete-with-minor-premises divisibility-lemma)
    (move-to-sibling 1)
    sort-definedness
    (apply-macete-with-minor-premises mod-of-integer-is-integer)
    simplify
    (cut-with-single-formula "forsome(k:zz, b+c mod modulus=k)")
    (move-to-sibling 1)
    (instantiate-existential ("b+c mod modulus"))
    (antecedent-inference "with(p:prop,p);")
    (backchain "with(p:prop,p);")
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises mod-characterization)
    (apply-macete-with-minor-premises divisibility-lemma)
    simplify
    (apply-macete-with-minor-premises mod-of-integer-is-integer)
    direct-and-antecedent-inference-strategy
    sort-definedness
    (apply-macete-with-minor-premises mod-of-integer-is-integer)

    )))


(def-theorem plus_mod-associative-lemma-2
  "forall(a,b,c:zz_mod, +_mod(+_mod(b,c),a)= (b+c)+a mod modulus)"
  (theory arithmetic-mod-n)
  lemma
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally +_mod)
    beta-reduce-with-minor-premises
    (move-to-sibling 1)
    (apply-macete-with-minor-premises mod-n-range-in-zz_mod)
    (apply-macete-with-minor-premises rev%congruence-characterization)
    (unfold-single-defined-constant (0) congruent)
    beta-reduce-with-minor-premises
    (apply-macete-with-minor-premises divisibility-lemma)
    (move-to-sibling 1)
    sort-definedness
    (apply-macete-with-minor-premises mod-of-integer-is-integer)
    simplify
    (cut-with-single-formula "forsome(k:zz, b+c mod modulus=k)")
    (move-to-sibling 1)
    (instantiate-existential ("b+c mod modulus"))
    (antecedent-inference "with(p:prop,p);")
    (backchain "with(p:prop,p);")
    (incorporate-antecedent "with(p:prop,p);")
    (apply-macete-with-minor-premises mod-characterization)
    (apply-macete-with-minor-premises divisibility-lemma)
    simplify
    (apply-macete-with-minor-premises mod-of-integer-is-integer)
    direct-and-antecedent-inference-strategy
    sort-definedness
    (apply-macete-with-minor-premises mod-of-integer-is-integer)

    )))

(def-theorem plus_mod-associative
  "forall(a,b,c:zz_mod, +_mod(a,+_mod(b,c))=+_mod(+_mod(a,b),c))"
  (theory arithmetic-mod-n)
  (proof
   (

    

    (apply-macete-with-minor-premises plus_mod-associative-lemma-1)
    (apply-macete-with-minor-premises plus_mod-associative-lemma-2)
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(a+b+c mod modulus,zz_mod)")
    simplify
    (apply-macete-with-minor-premises mod-n-range-in-zz_mod)
    )))


(def-constant -_mod
  "lambda(a:zz_mod, (-a) mod modulus)"
  (theory arithmetic-mod-n))

(def-theorem -_mod-computation-non-zero
  "forall(a:zz_mod, not(a=0) implies -_mod(a)=modulus-a)"
  (theory arithmetic-mod-n)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) -_mod)
    (apply-macete-with-minor-premises mod-characterization)
    simplify
    (cut-with-single-formula "#(a,zz_mod)")
    (incorporate-antecedent "with(a:zz_mod,#(a,zz_mod));")
    (apply-macete-with-minor-premises zz_mod-defining-axiom_arithmetic-mod-n)
    (apply-macete-with-minor-premises multiplication-preserves-divisibility)
    (apply-macete-with-minor-premises self-divisibility)
    simplify
    )))

(def-theorem -_mod-computation-zero
  "-_mod(0)=0"
  (theory arithmetic-mod-n)
  (proof
   (


    (unfold-single-defined-constant (0) -_mod)
    (apply-macete-with-minor-premises mod-characterization)
    simplify
    (unfold-single-defined-constant (0) divides)
    simplify

    )))



(load-section basic-monoids)


;;obligations

(def-theorem ()
  "#(lambda(a,b:zz_mod,*_mod(a,b)),[zz_mod,zz_mod,zz_mod])"
  (theory arithmetic-mod-n)
  lemma
  (proof
   (


    sort-definedness
    direct-and-antecedent-inference-strategy
    beta-reduce-with-minor-premises
    (apply-macete-with-minor-premises *_mod-total)

    )))


(def-theorem ()
  "forall(z,y,x:zz_mod,
     lambda(a,b:zz_mod,*_mod(a,b))(x,*_mod(y,z))
     =lambda(a,b:zz_mod,*_mod(a,b))(*_mod(x,y),z))"
  (theory arithmetic-mod-n)
  lemma
  (proof
   (


    beta-reduce-with-minor-premises
    (apply-macete-with-minor-premises mult_mod-associative)
    simplify
    direct-inference
    (cut-with-single-formula "#(*_mod(*_mod(x,y),z), zz_mod)")
    (apply-macete-with-minor-premises *_mod-total)
    (apply-macete-with-minor-premises *_mod-total)
    (apply-macete-with-minor-premises *_mod-total)
    (apply-macete-with-minor-premises zz_mod-in-quasi-sort-domain_arithmetic-mod-n)
    (apply-macete-with-minor-premises *_mod-total)
    (apply-macete-with-minor-premises zz_mod-in-quasi-sort-domain_arithmetic-mod-n)
    (apply-macete-with-minor-premises *_mod-total)
    (apply-macete-with-minor-premises zz_mod-in-quasi-sort-domain_arithmetic-mod-n)    

)))


(def-theorem ()
  "forall(x:zz_mod,*_mod(1,x)=x)"
  (theory arithmetic-mod-n)
  lemma
  (proof
   (


    (unfold-single-defined-constant-globally *_mod)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises mod-characterization)
    (unfold-single-defined-constant (0) divides)
    simplify
    (apply-macete-with-minor-premises zz_mod-in-quasi-sort_arithmetic-mod-n)
    )))

(def-theorem ()
  "total_q{*_mod,[zz_mod,zz_mod,rr]}"
  (theory arithmetic-mod-n)
  (usages d-r-convergence)
  (proof
   (


    insistent-direct-inference
    (cut-with-single-formula "#(*_mod(x_0,x_1),zz_mod)")
    (apply-macete-with-minor-premises *_mod-total)
    )))


(def-theorem ()
  "forall(x,y:zz_mod,*_mod(x,y)=*_mod(y,x))"
  (theory arithmetic-mod-n)
  lemma
  (proof
   (

    (unfold-single-defined-constant-globally *_mod)
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(y*x mod modulus,zz_mod)")
    (apply-macete-with-minor-premises mod-n-range-in-zz_mod)

    )))



(def-translation commutative-monoid-theory-to-multiplicative-mod-n
  (source commutative-monoid-theory)
  (target arithmetic-mod-n)
  (sort-pairs (uu zz_mod))
  (constant-pairs (e 1) (** "lambda(a,b:zz_mod, *_mod(a,b))" ))
  (fixed-theories h-o-real-arithmetic)
  (theory-interpretation-check using-simplification))

   

(comment
 (def-theorem some-relatively-prime-to-generator
  "forsome(k:zz, 0<=k and k<modulus and relatively%prime(k,modulus))"
  (theory arithmetic-mod-n)
  (proof
   (



    (apply-macete-with-minor-premises relatively%prime-characterization)
    (instantiate-existential ("1"))
    simplify
    simplify
    (instantiate-existential ("1" "0"))
    simplify
    )))

 (def-atomic-sort zz_mod_ast
  "lambda(k:zz, 0<=k and k<modulus and relatively%prime(k,modulus))"
  (theory arithmetic-mod-n))


 (def-theorem closure
  "forall(a,b:mm, #(mult_mm(a,b),mm))"
  (theory arithmetic-mod-n)
  (proof
   (


direct-and-antecedent-inference-strategy
(apply-macete-with-minor-premises mm-defining-axiom_arithmetic-mod-n)
beta-reduce-with-minor-premises
(move-to-sibling 1)
(unfold-single-defined-constant-globally mult_mm)
(apply-macete-with-minor-premises mod-of-integer-is-integer)
direct-and-antecedent-inference-strategy
simplify
(cut-with-single-formula "#(a,mm) and #(b,mm)")
(cut-with-single-formula "forsome(z:zz, mult_mm(a,b)=z)")
(antecedent-inference "with(p:prop,forsome(z:zz,p));")
(backchain "with(z:zz,r:rr,r=z);")
(backchain "with(z:zz,r:rr,r=z);")
(backchain "with(z:zz,r:rr,r=z);")
(incorporate-antecedent "with(z:zz,r:rr,r=z);")
(incorporate-antecedent "with(p:prop,p);")
(apply-macete-with-minor-premises mm-defining-axiom_arithmetic-mod-n)
beta-reduce-repeatedly
(apply-macete-with-minor-premises relative-primality-symmetry)
(apply-macete-with-minor-premises relatively-prime-mod-characterization)
(unfold-single-defined-constant-globally mult_mm)
(apply-macete-with-minor-premises mod-characterization)
(move-to-ancestor 1)
direct-inference
(move-to-ancestor 1)
direct-and-antecedent-inference-strategy
(incorporate-antecedent "with(z:zz,b,a:mm,a*b mod modulus=z);")
(apply-macete-with-minor-premises mod-characterization)
direct-and-antecedent-inference-strategy
(incorporate-antecedent "with(z:zz,b,a:mm,a*b mod modulus=z);")
(apply-macete-with-minor-premises mod-characterization)
direct-and-antecedent-inference-strategy
(incorporate-antecedent "with(z:zz,b,a:mm,a*b mod modulus=z);")
(apply-macete-with-minor-premises mod-characterization)
(apply-macete-with-minor-premises divisibility-lemma)
direct-and-antecedent-inference-strategy

    )))

  (def-translation groups-to-arithmetic-mod-n
  (source-theory groups)
  (target-theory ))



  (def-constant exp
  "lambda(x:uu, n:zz, monoid%prod(1,modulus,lambda(j:zz,x)))"
  (theory monoid-theory))


  (def-theory finite-abelian-group
  (component-theories commutative-monoid-theory)
  (axioms 
   (cancellatio  "forall(a,b,c:uu, a**b=a**c iff b=c)")))

)
