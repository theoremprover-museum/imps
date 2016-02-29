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


(herald fields-supplements)

(include-files
 (files (imps theories/algebra/fields)
	(imps theories/groups/cyclic-groups)
        (imps theories/reals/mutual-interp)))

(def-theorem ()
  "forall(x:kk, not(x=o_kk) implies #(inv(x)))"
  (theory fields)
  (usages d-r-convergence)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem multiplicative-inverse-for-fields ("x"))
    )))

(def-overloading + (h-o-real-arithmetic +) (fields +_kk))
(def-overloading * (h-o-real-arithmetic *) (fields *_kk))
(def-overloading - (h-o-real-arithmetic -) (fields -_kk))

(def-theorem ()
  "forall(x:kk,o_kk+x=x)"
  (theory fields)
  (proof
   (
    (apply-macete-with-minor-premises commutative-law-for-addition-for-fields)
    (apply-macete-with-minor-premises additive-identity-for-fields)

    )))

(def-theorem ()
  "forall(x:kk,-x+x=o_kk)"
  (theory fields)
  (proof
   (
    (apply-macete-with-minor-premises commutative-law-for-addition-for-fields)
    (apply-macete-with-minor-premises additive-inverse-for-fields)

    )))

(def-translation groups-to-additive-kk
  (fixed-theories h-o-real-arithmetic)
  (source abelian-groups)
  (target fields)
  (sort-pairs
   (gg kk))
  (constant-pairs
   (inv -_kk)
   (mul +_kk)
   (e o_kk)))

(def-theorem o_kk-times-is-o_kk
  "forall(x:kk, x*o_kk=o_kk)"
  (theory fields)
  (proof
   (

    direct-inference
    (cut-with-single-formula "x*o_kk=x*o_kk+x*o_kk")
    (incorporate-antecedent "with(x:kk,x*o_kk=x*o_kk+x*o_kk);")
    (apply-macete-with-minor-premises tr%right-trivial-cancellation-law-left)
    simplify
    (cut-with-single-formula "o_kk=o_kk+o_kk")
    (backchain "o_kk=o_kk+o_kk;")
    (apply-macete-with-minor-premises left-distributive-law-for-fields)
    (apply-macete-with-minor-premises additive-identity-for-fields)

    )))

(def-constant sub_kk
 "lambda(x,y:kk,x+(-y))"
 (theory fields))

(def-constant /_kk
  "lambda(x,y:kk, if(y=o_kk,?kk,inv(y)*x))"
  (theory fields))


(def-overloading sub (h-o-real-arithmetic sub) (fields sub_kk))
(def-overloading / (h-o-real-arithmetic /) (fields /_kk))

(def-theorem ()
  "forall(y,x:kk,x-y=x+-y)"
  (proof

   (
    unfold-defined-constants
    simplify
    ))
  (theory fields))

(def-theorem ()
  "total_q{sub_kk,[kk,kk,kk]}"
  (theory fields)
  (proof
   (
    unfold-defined-constants
    insistent-direct-inference-strategy
    beta-reduce-repeatedly

    ))
  (usages d-r-convergence))

(def-theorem division-characterization-fields
  "forall(a,b:kk, not(b=o_kk) implies b*(a/b)=a)"
  (theory fields)
  (proof
   (
    (unfold-single-defined-constant (0) /_kk)
    simplify
    (force-substitution "b*(inv(b)*a)" "(b*inv(b))*a" (0))
    (apply-macete-with-minor-premises multiplicative-inverse-for-fields)
    (apply-macete-with-minor-premises multiplicative-identity-for-fields)
    (apply-macete-with-minor-premises associative-law-for-multiplication-for-fields)

    )))

(def-theorem non-o_kk-is-closed-under-inv
  "forall(x:kk, not(x=o_kk) implies not(inv(x)=o_kk))"
  (theory fields)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "i_kk=x*inv(x)")
    (contrapose "with(x:kk,not(x=o_kk));")
    (contrapose "with(x:kk,i_kk=x*inv(x));")
    (backchain "with(x:kk,inv(x)=o_kk);")
    (apply-macete-with-minor-premises o_kk-times-is-o_kk)
    (contrapose "with(x:kk,not(x=o_kk));")
    (apply-macete-with-minor-premises multiplicative-inverse-for-fields)

    )))
  
(def-theorem  non-o_kk-is-closed-under-*_kk
  "forall(x,y:kk, not(x=o_kk) and not(y=o_kk) implies not(x*y=o_kk))"
  (theory fields)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (contrapose "with(x:kk,not(x=o_kk));")
    (cut-with-single-formula "x=x*y*inv(y)")
    (backchain "with(y,x:kk,x=x*y*inv(y));")
    (backchain "with(y,x:kk,x*y=o_kk);")
    (apply-macete-with-minor-premises commutative-law-for-multiplication-for-fields)
    (apply-macete-with-minor-premises o_kk-times-is-o_kk)
    (apply-macete-with-minor-premises associative-law-for-multiplication-for-fields)
    (apply-macete-with-minor-premises multiplicative-inverse-for-fields)
    (apply-macete-with-minor-premises commutative-law-for-multiplication-for-fields)
    (apply-macete-with-minor-premises multiplicative-identity-for-fields)

    )))

;;Obligations for translation:

(def-theorem ()
  "forsome(x:kk,not(x=o_kk))"
  lemma
  (theory fields)
  (proof
   (
    (instantiate-existential ("i_kk"))
    simplify
    )))

(def-theorem ()
  "forall(x,y:kk,
     not(x=o_kk) implies y=o_kk or not(x*y=o_kk))"
  lemma
  (theory fields)
  (proof
   (
    (apply-macete-with-minor-premises non-o_kk-is-closed-under-*_kk)
    simplify
    )))

(def-theorem ()
  "forall(x:kk,not(x=o_kk) implies inv(x)*x=i_kk)"
  lemma
  (theory fields)
  (proof
   (
    (apply-macete-with-minor-premises commutative-law-for-multiplication-for-fields)
    (apply-macete-with-minor-premises multiplicative-inverse-for-fields)

    )))

(def-theorem () 
  "forall(x,y,z:kk,
  not(x=o_kk) and not(y=o_kk) and not(z=o_kk)
   implies 
  not(x *_kk y=o_kk)
   and 
  (not(y *_kk z=o_kk) and x *_kk y *_kk z=x *_kk (y *_kk z)))"
  lemma
  (theory fields)
  (proof
   (


    (apply-macete-with-minor-premises non-o_kk-is-closed-under-*_kk)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises associative-law-for-multiplication-for-fields)
    )))


;;used to be:


(comment
 (def-theorem ()
   "forall(x,y,z:kk,
     not(x=o_kk) and not(y=o_kk) and not(z=o_kk)
      implies 
     if(x*y=o_kk, ?kk, x*y*z)=if(y*z=o_kk, ?kk, x*(y*z)))"
   lemma
   (theory fields)
   (proof
    (
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "not(x*y=o_kk) and not(y*z=o_kk)")
     simplify
     (apply-macete-with-minor-premises associative-law-for-multiplication-for-fields)
     (apply-macete-with-minor-premises non-o_kk-is-closed-under-*_kk)
     direct-and-antecedent-inference-strategy
     )))
 )

(def-theorem ()
  "forall(x,y:kk,not(x=o_kk) and not(y=o_kk) implies x*y=y*x)"
  lemma
  (theory fields)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (assume-theorem commutative-law-for-multiplication-for-fields)
    (backchain "forall(y,x:kk,x*y=y*x);")

    )))

(def-theorem ()
  "forall(x:kk,not(x=o_kk) implies x*i_kk=x)"
  lemma
  (theory fields)
  (proof
   (
    (apply-macete-with-minor-premises commutative-law-for-multiplication-for-fields)
    (apply-macete-with-minor-premises multiplicative-identity-for-fields)
    )))


(def-theorem ()
  "forall(x:kk,
     not(x=o_kk)
      implies 
     not(inv(x)=o_kk) and inv(x) *_kk x=i_kk)"
  lemma
  (theory fields)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises non-o_kk-is-closed-under-inv)
    (apply-macete-with-minor-premises commutative-law-for-multiplication-for-fields)
    (apply-macete-with-minor-premises multiplicative-inverse-for-fields)

    )))

;;;used to be

(comment
 (def-theorem ()
  "forall(x:kk,
     not(x=o_kk)
      implies 
     if(inv(x)=o_kk, ?kk, inv(x)*x)=i_kk)"
  lemma
  (theory fields)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not(inv(x)=o_kk)")
    simplify
    (apply-macete-with-minor-premises commutative-law-for-multiplication-for-fields)
    (apply-macete-with-minor-premises multiplicative-inverse-for-fields)
    (apply-macete-with-minor-premises non-o_kk-is-closed-under-inv)

    ))))

(def-theorem ()
  "forall(x:kk,
    not(x=o_kk)
      implies 
    not(inv(x)=o_kk) and x *_kk inv(x)=i_kk)"
  lemma
  (theory fields)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises non-o_kk-is-closed-under-inv)
    (apply-macete-with-minor-premises multiplicative-inverse-for-fields)

    )))

;;used to be

(comment
 (def-theorem ()
  "forall(x:kk,
    not(x=o_kk)
     implies 
    if(inv(x)=o_kk, ?kk, x * inv(x))=i_kk)"
  lemma
  (theory fields)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "not(inv(x)=o_kk)")
    simplify
    (apply-macete-with-minor-premises multiplicative-inverse-for-fields)
    (apply-macete-with-minor-premises non-o_kk-is-closed-under-inv)

    ))))

(def-theorem ()
  "forall(x:kk,x=o_kk or not(inv(x)=o_kk))"
  lemma
  (theory fields)
  (proof
   (
    (apply-macete-with-minor-premises non-o_kk-is-closed-under-inv)
    direct-and-antecedent-inference-strategy
    )))


(def-translation groups-to-multiplicative-kk
  force-under-quick-load
  (source abelian-groups)
  (target fields)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs 
   (gg (pred "lambda(x:kk, not(x=o_kk))")))
  (constant-pairs
   (e i_kk)
   (inv "lambda(x:kk, if(x=o_kk,?kk,inv(x)))")
   (mul "lambda(x,y:kk,if(x=o_kk or y=o_kk,?kk,x*y))"))
  (theory-interpretation-check using-simplification))

(def-renamer groups-multiplicative-kk-renamer
  (pairs 
   (multiple pexp)))

(def-transported-symbols (multiple)
  (renamer groups-multiplicative-kk-renamer)
  (translation groups-to-multiplicative-kk)
  )

(def-constant ^_kk
  "lambda(x:kk,n:zz, if(not(x=o_kk),pexp(n,x),0<n,o_kk,?kk))"
  (theory fields))

(def-overloading ^ (h-o-real-arithmetic ^) (fields ^_kk))

;; Obligations for installing processors:

(def-theorem ()
  "forall(y,x:kk, x/y==x*y^[-1])"
  (theory fields)
  (proof

   (
    (unfold-single-defined-constant (0) /_kk)
    direct-and-antecedent-inference-strategy
    (case-split ("y=o_kk"))
    simplify
    (unfold-single-defined-constant (0) ^_kk)
    simplify
    simplify
    (assume-theorem commutative-law-for-multiplication-for-fields)
    (backchain "forall(y,x:kk,x*y=y*x);")
    (cut-with-single-formula "inv(y)=y^[-1]")
    (unfold-single-defined-constant (0) ^_kk)
    simplify
    (instantiate-transported-theorem 
     multiple-commutes-with-negation-corollary groups-to-multiplicative-kk ("y"))
    simplify

    )))

(def-theorem o_kk-exponent
  "forall(m:zz, #(o_kk^m,kk) implies o_kk^m=o_kk)"
  (theory fields)
  (proof
   (
    unfold-defined-constants
    simplify
    )))

(def-theorem ()
  "forall(n:zz, #(i_kk^n,kk) implies i_kk^n=i_kk)"
  (theory fields)
  (proof
   (
    unfold-defined-constants
    simplify
    direct-and-antecedent-inference-strategy
    (instantiate-transported-theorem
     multiple-of-group-identity groups-to-multiplicative-kk ("n"))
    )))
  

(def-theorem ()
  "forall(x:kk,#(x^0,kk) implies x^0=i_kk)"
  (theory fields)
  (proof
   (
    unfold-defined-constants
    simplify
    direct-inference
    direct-and-antecedent-inference-strategy
    (instantiate-transported-theorem
     0-multiple-is-group-identity groups-to-multiplicative-kk ("x"))

    )))

(def-theorem ()
  "forall(x:kk,x^1=x)"
  (theory fields)
  (proof
   (
    (unfold-single-defined-constant (0) ^_kk)
    direct-inference
    (case-split ("x=o_kk"))
    simplify
    simplify
    (instantiate-transported-theorem 1-multiple-is-element groups-to-multiplicative-kk ("x"))
    )))

(def-theorem ()
  "forall(n,m:zz, x:kk ,#((x^m)^n,kk) implies (x^m)^n=x^(m*n))"
  (theory fields)
  (proof

   (


    direct-inference
    (case-split ("x=o_kk"))
    (block 
      (script-comment "`case-split' at (1)")
      (backchain-repeatedly ("with(x:kk,x=o_kk);")) direct-inference
      (cut-with-single-formula "0<m and 0<n and 0<m*n")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(apply-macete-with-minor-premises o_kk-exponent)
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  (apply-macete-with-minor-premises o_kk-exponent)
	  (unfold-single-defined-constant (0) ^_kk) simplify
	  )
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  (unfold-single-defined-constant (0) ^_kk) simplify
	  ) )
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(cut-with-single-formula "#(o_kk^m) and o_kk^m=o_kk")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (contrapose "with(k:kk,#(k,kk));") (backchain "with(p:prop,p and p);")
	  (contrapose "with(p:prop,p or p or p);")
	  (antecedent-inference "with(p:prop,p and p);")
	  (incorporate-antecedent "with(k:kk,#(k));")
	  (incorporate-antecedent "with(k:kk,#(k,kk));")
	  (unfold-single-defined-constant (0 1) ^_kk) simplify
	  )
	(apply-macete-with-minor-premises o_kk-exponent)
	) )
    (block 
      (script-comment "`case-split' at (2)")
      (cut-with-single-formula "not(pexp(m,x)=o_kk)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(apply-macete-with-minor-premises commutative-law-for-multiplication)
	(move-to-ancestor 1) unfold-defined-constants simplify
	beta-reduce-with-minor-premises
	(block 
	  (script-comment "`beta-reduce-with-minor-premises' at (0)") simplify
	  (instantiate-transported-theorem multiple-is-homogenuous
					   groups-to-multiplicative-kk ("n" "m" "x")
					   )
	  direct-inference
	  (apply-macete-with-minor-premises commutative-law-for-multiplication)
	  )
	(instantiate-transported-theorem multiple-totality
					 groups-to-multiplicative-kk ("m" "x")
					 ) )
      (instantiate-transported-theorem multiple-totality-with-range
				       groups-to-multiplicative-kk ("x" "m")
				       ) )

    )))

(def-theorem ()
  "forall(n,m:zz, x:kk ,((#(x^m,kk) and #(x^n,kk)) iff #((x^m)^n,kk)))"
  (theory fields)
  (proof
   (



    direct-inference
    unfold-defined-constants
    (case-split ("x=o_kk"))
    simplify
    (block 
     (script-comment "`case-split' at (2)")
     simplify
     (instantiate-transported-theorem multiple-totality-with-range
				      groups-to-multiplicative-kk
				      ("x" "m"))
     (cut-with-single-formula "not pexp(m,x)=o_kk")
     simplify
     (instantiate-transported-theorem multiple-totality-with-range
				      groups-to-multiplicative-kk
				      ("pexp(m,x)" "n"))
     direct-and-antecedent-inference-strategy
     (instantiate-transported-theorem multiple-totality-with-range
				      groups-to-multiplicative-kk
				      ("x" "n")))
    )))

(def-theorem ()
  "forall(m:zz ,y,x:kk,(#(x^m*y^m,kk) or #((x*y)^m,kk)) 
                          implies 
                        x^m*y^m=(x*y)^m)"
  (theory fields)
  (proof
   (

    direct-inference
    (case-split ("x=o_kk"))
    (block 
     (script-comment "`case-split' at (1)")
     simplify
     (apply-macete-with-minor-premises
      commutative-law-for-multiplication-for-fields)
     (apply-macete-with-minor-premises o_kk-times-is-o_kk)
     (unfold-single-defined-constant (1 2) ^_kk)
     simplify
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises o_kk-times-is-o_kk)
     (unfold-single-defined-constant (0) ^_kk)
     (case-split ("y=o_kk"))
     simplify
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      (instantiate-transported-theorem multiple-totality-with-range
				       groups-to-multiplicative-kk
				       ("y" "m"))))
    (block 
     (script-comment "`case-split' at (2)")
     (case-split ("y=o_kk"))
     (block 
      (script-comment "`case-split' at (1)")
      simplify
      (apply-macete-with-minor-premises o_kk-times-is-o_kk)
      (unfold-single-defined-constant (1 2) ^_kk)
      simplify
      direct-and-antecedent-inference-strategy
      (apply-macete-with-minor-premises o_kk-times-is-o_kk)
      (unfold-single-defined-constant (0) ^_kk)
      simplify
      (instantiate-transported-theorem multiple-totality-with-range
				       groups-to-multiplicative-kk
				       ("x" "m")))
     (block 
      (script-comment "`case-split' at (2)")
      direct-inference
      (unfold-single-defined-constant-globally ^_kk)
      (cut-with-single-formula "not(x*y=o_kk)")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       simplify
       (instantiate-transported-theorem multiple-is-additive-in-group
					groups-to-multiplicative-kk
					("m" "x" "y"))
       (contrapose "with(k:kk,k=k);")
       (cut-with-single-formula "not pexp(m,x)=o_kk and not pexp(m,y)=o_kk")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	simplify
	beta-reduce-with-minor-premises
	simplify
	(instantiate-transported-theorem multiple-totality-with-range
					 groups-to-multiplicative-kk
					 ("y" "m"))
	(instantiate-transported-theorem multiple-totality-with-range
					 groups-to-multiplicative-kk
					 ("x" "m")))
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(instantiate-transported-theorem multiple-totality-with-range
					 groups-to-multiplicative-kk
					 ("x" "m"))
	direct-inference
	(instantiate-transported-theorem multiple-totality-with-range
					 groups-to-multiplicative-kk
					 ("y" "m"))))
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises non-o_kk-is-closed-under-*_kk)
       direct-inference)))

    )))

(def-theorem ()
  "forall(n,m:zz, x:kk,#(x^m*x^n,kk) implies x^(m+n)=x^m*x^n)"
  (theory fields)
  (proof
   (
    direct-inference
    (case-split ("x=o_kk"))
    unfold-defined-constants
    simplify
    (apply-macete-with-minor-premises o_kk-times-is-o_kk)
    unfold-defined-constants
    simplify
    (instantiate-transported-theorem
     multiple-is-additive groups-to-multiplicative-kk ("m" "n" "x"))
    (cut-with-single-formula "not(pexp(m,x)=o_kk) and not(pexp(n,x)=o_kk)")
    (simplify-antecedent "with(x,y:kk, x=y)")
    (weaken (0))
    direct-inference
    (instantiate-transported-theorem
     multiple-totality-with-range groups-to-multiplicative-kk ("x" "m"))
    (instantiate-transported-theorem
     multiple-totality-with-range groups-to-multiplicative-kk ("x" "n"))

    )))

(def-algebraic-processor FIELD-ALGEBRAIC-PROCESSOR
  (language fields)
  (base ((operations
	  (+ +_kk)
	  (* *_kk)
	  (- -_kk)
	  (^ ^_kk)
	  (sub sub_kk)
	  (zero o_kk)
	  (unit i_kk))
	 commutes))
  (exponent rr-algebraic-processor))
	

(def-theory-processors fields
  (algebraic-simplifier (field-algebraic-processor ^_kk sub_kk *_kk +_kk -_kk))
  (algebraic-term-comparator field-algebraic-processor))

;; Try simplifying (qr "with(y,x:kk,(x+y)^2=x^2+(i_kk+i_kk)*x*y+y^2)") BEFORE evaluating the
;; following:

(def-theorem ()
  "forall(x:kk,y:zz,(0<y or not(x=o_kk)) implies #(x^y))"
  (proof
   (
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    simplify
    unfold-defined-constants
    simplify

    ))
  (theory fields)
  (usages d-r-convergence))

(def-theorem ()
  "forall(x:kk, y:zz, x=o_kk and not(0<y) implies not(#(x^y)))"
  (proof
   (
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    simplify

    ))
  (theory fields)
  (usages d-r-convergence))

(def-renamer groups-additive-kk-renamer
  (pairs 
   (multiple *_ext)))


(def-transported-symbols (multiple)
  (renamer groups-additive-kk-renamer)
  (translation groups-to-additive-kk)
  )

(def-overloading * (fields *_ext))

(def-theorem *_ext-totality
  "total_q{*_ext,[zz,kk,kk]}"
  (proof
   (
    (apply-macete-with-minor-premises tr%multiple-totality)
    ))
  (theory fields)
  (usages d-r-convergence))


(def-recursive-constant sum_kk
 "lambda(sigma:[zz,zz,[zz,kk],kk],lambda(m,n:zz,f:[zz,kk],
 if(m<=n,sigma(m,n-1,f)+f(n),o_kk)))"
  (definition-name sum_kk)
  (theory fields))

(def-recursive-constant prod_kk
   "lambda(pi:[zz,zz,[zz,kk],kk],lambda(m,n:zz,f:[zz,kk],
 if(m<=n,pi(m,n-1,f)*f(n),i_kk)))"
  (definition-name  prod_kk)
  (theory fields))

(def-overloading sum (h-o-real-arithmetic sum) (fields sum_kk))

(def-overloading prod (h-o-real-arithmetic prod) (fields prod_kk))

(include-files
  (files (imps theories/algebra/monoids)))

(def-theorem sum_kk-definedness
  "forall(m,n:zz,f:[zz,kk],forall(k:zz,m<=k and k<=n implies #(f(k))) 
             implies  
             #(sum(m,n,f)))"
  (theory fields)
  
  (proof
   
   (
    
    direct-inference
    (case-split ("m<=n"))
    (induction integer-inductor ())
    direct-and-antecedent-inference-strategy
    (prove-by-logic-and-simplification 3)
    (prove-by-logic-and-simplification 3)
    (unfold-single-defined-constant (0) sum_kk)
    simplify
    
    ))
  (usages d-r-convergence))

(def-translation monoids-to-additive-kk
  (fixed-theories h-o-real-arithmetic)
  (source commutative-monoid-theory)
  (target fields)
  (sort-pairs
   (uu kk))
  (constant-pairs
   (** +_kk)
   (e o_kk))
  (theory-interpretation-check using-simplification))

(def-theorem external-multiplication-conversion
  "forall(m:zz,x:kk,m*x=m*i_kk*x)"
  (theory fields)
  (proof

   (
    direct-inference
    (case-split ("0<=m"))
    (induction integer-inductor ("m"))
    (unfold-single-defined-constant (0 1) *_ext)
    simplify
    (cut-with-single-formula "forall(m:zz,x:kk,0<=m implies m*x=m*i_kk*x);")
    (backchain-backwards "forall(m:zz,x:kk,0<=m implies m*x=m*i_kk*x);")
    simplify
    (weaken (0))
    direct-and-antecedent-inference-strategy)))

(include-files
 (files (imps theories/reals/comb-ident)))

;;;(def-section comb-ident
;;;  (files (imps theories/reals/comb-ident)))
;;;
;;;(load-section comb-ident)

(def-theorem ()
   "forall(x:kk,m,n:zz, (m+n)*x=m*x+n*x)"
   (theory  fields)
   (usages rewrite)
   (proof
    (
     (apply-macete-with-minor-premises tr%multiple-is-additive)
     simplify

     )))

(def-theorem ()
   "forall(x:kk,0*x=o_kk)"
   (theory  fields)
   (usages rewrite)
   (proof
    (
     unfold-defined-constants
     simplify

     )))

(def-theorem ()
   "forall(x:kk,1*x=x)"
   (theory  fields)
   (usages rewrite)
   (proof
    (
     unfold-defined-constants
     simplify

     )))

(def-theorem uniqueness-of-exponentiation
  "forall(f:[kk,zz,kk], 
        (forall(x:kk, n:zz, not(x=o_kk) and 0<=n implies f(x,n+1)=f(x,n)*x)
    and forall(x:kk, not(x=o_kk)  implies f(x,0)=i_kk)
    and forall(x:kk, n:zz, not(x=o_kk) and 0<=n implies f(x,-n)=(f(x,n))^[-1])
    and forall(n:zz,1<=n implies f(o_kk,n)=o_kk) 
    and forall(n:zz, n<=0 implies not(#(f(o_kk,n)))))
     iff
    f=^_kk)"
  lemma
  (theory fields)
  (proof
   (

    direct-inference
    direct-inference
    (antecedent-inference-strategy (0))
    extensionality
    direct-and-antecedent-inference-strategy
    (case-split ("1<=x_1"))
    (induction trivial-integer-inductor ("x_1"))
    beta-reduce-repeatedly
    (instantiate-universal-antecedent "with(f:[kk,zz,kk],
  forall(x:kk,n:zz,
    not(x=o_kk) and 0<=n implies f(x,n+1)=f(x,n)*x));" ("x_0" "0"))
    simplify
    (simplify-antecedent "not(0<=0);")
    (incorporate-antecedent "with(x_0:kk,f:[kk,zz,kk],f(x_0,0+1)=f(x_0,0)*x_0);")
    simplify
    (case-split ("x_0=o_kk"))
    simplify
    simplify
    (case-split ("x_0=o_kk"))
    simplify
    (instantiate-universal-antecedent "with(f:[kk,zz,kk],
  forall(x:kk,n:zz,
    not(x=o_kk) and 0<=n implies f(x,n+1)=f(x,n)*x));" ("x_0" "t"))
    (simplify-antecedent "with(t:zz,not(0<=t));")
    (incorporate-antecedent "with(t:zz,x_0:kk,f:[kk,zz,kk],f(x_0,t+1)=f(x_0,t)*x_0);")
    simplify
    (case-split ("x_0=o_kk"))
    simplify
    (case-split ("x_1=0"))
    simplify
    (force-substitution "x_1" "-(-x_1)" (0))
    (backchain "with(f:[kk,zz,kk],
  forall(x:kk,n:zz,
    not(x=o_kk) and 0<=n implies f(x,-n)=f(x,n)^[-1]));")
    direct-and-antecedent-inference-strategy
    simplify
    (cut-with-single-formula "forall(x_1:zz, 1<=x_1 implies f(x_0,x_1)==x_0^x_1)")
    (backchain "with(x_0:kk,f:[kk,zz,kk],
  forall(x_1:zz,1<=x_1 implies f(x_0,x_1)==x_0^x_1));")
    simplify
    simplify
    simplify

    )))


(def-theorem uniqueness-of-exponentiation-corollary
  "forall(f:[kk,zz,kk], 
        (forall(x:kk, n:zz, not(x=o_kk) and 0<=n implies f(x,n+1)=f(x,n)*x)
    and forall(x:kk, not(x=o_kk)  implies f(x,0)=i_kk)
    and forall(x:kk, n:zz, not(x=o_kk) and 0<=n implies f(x,-n)*f(x,n)=i_kk)
    and forall(n:zz,1<=n implies f(o_kk,n)=o_kk) 
    and forall(n:zz, n<=0 implies not(#(f(o_kk,n)))))
     implies
    f=^_kk)"
  lemma
  (theory fields)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem uniqueness-of-exponentiation ("f"))
    (contrapose "with(n:zz,x:kk,f:[kk,zz,kk],not(f(x,-n)=f(x,n)^[-1]));")
    (instantiate-universal-antecedent "with(f:[kk,zz,kk],
  forall(x:kk,n:zz,
    not(x=o_kk) and 0<=n implies f(x,-n)*f(x,n)=i_kk));" ("x" "n"))
    (cut-with-single-formula "not(f(x,n)=o_kk) and #(f(x,n)) and #(f(x,-n))")
    (force-substitution "f(x,n)^[-1]" "f(x,n)^[-1]*(f(x,-n)*f(x,n))" (0))
    (weaken (1))
    simplify
    simplify
    direct-and-antecedent-inference-strategy
    (contrapose "with(n:zz,x:kk,f:[kk,zz,kk],f(x,-n)*f(x,n)=i_kk);")
    (case-split ("#(f(x,-n))"))
    simplify
    (contrapose "with(n:zz,x:kk,f:[kk,zz,kk],not(#(f(x,-n))));")

    )))

;; The following are translation obligations.

(def-theorem fields-to-rr-obligation-1
  "/=lambda(x,y:rr,if(y=0, ?rr, y^[-1]*x))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    extensionality
    simplify
    )))

(def-theorem fields-to-rr-obligation-2
  " ^=lambda(x:rr,n:zz,if(not(x=0), x^n, 0<n, 0, ?rr))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    extensionality
    direct-inference
    simplify
    (case-split ("x_0=0"))
    simplify
    simplify
    )))

(def-theorem fields-to-rr-obligation-3
  "forall(x_1:rr,x_1=0 or forall(x_0:zz,not(x_1^x_0=0)))
    and 
   lambda(m:zz,y:rr,if(not(y=0), y^m, ?rr))
   =lambda(k:zz,m:rr,
      if(not(m=0),
        if(0<k,
          if(m^([-1]+k)=0, ?rr, m^k),
          k=0,
          1,
          m^([-1]*k)=0,
          ?rr,
          m^k),
        ?rr))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    (assume-transported-theorem exponent-non-zero-lemma-1
				complete-ordered-field-interpretable)
    direct-and-antecedent-inference-strategy
    simplify
    (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      extensionality direct-inference simplify
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(x_1:rr,p));" ("x_1"))
      (case-split ("0<x_0")) simplify
      (block 
	  (script-comment "`case-split' at (2)") simplify
	  direct-and-antecedent-inference-strategy
	  (block 
	      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	    (instantiate-universal-antecedent "with(p:prop,forall(x_0:zz,p));" ("x_0"))
	    (contrapose "with(x_0:zz,x_1:rr,not(x_1^x_0=0));")
	    (backchain "with(p:prop,forall(n:zz,x:rr,p));") simplify)
	  (backchain "with(p:prop,forall(x_0:zz,p));")))
    )))

;; WMF: This obligation does not seem to be provable. Wed Aug 31 13:04:06 EDT 2005

(def-theorem fields-to-rr-obligation-4
  "forall(h_0:[zz,rr,rr],
     forall(u_0:zz,u_1:rr,
       forall(x_0:zz,x_1:rr,
         if_form(not(x_1=0),
           #(h_0(x_0,x_1)) implies not(h_0(x_0,x_1)=0),
           not(#(h_0(x_0,x_1)))))
        and 
       (not(u_1=0)
        and 
       #(if(0<u_0,
           lambda(x,y:rr,if(x=0 or y=0, ?rr, x*y))
            (u_1,h_0([-1]+u_0,u_1)),
           u_0=0,
           1,
           lambda(x:rr,if(x=0, ?rr, 1/x))(h_0([-1]*u_0,u_1)))))
        implies 
       if(0<u_0,
         lambda(x,y:rr,if(x=0 or y=0, ?rr, x*y))
          (u_1,h_0([-1]+u_0,u_1)),
         u_0=0,
         1,
         lambda(x:rr,if(x=0, ?rr, 1/x))(h_0([-1]*u_0,u_1)))
       =h_0(u_0,u_1))
      implies 
     forall(u_1:rr,
       not(u_1=0) implies forall(u_0:zz,u_1^u_0=h_0(u_0,u_1))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (

    )))

(def-theorem fields-to-rr-obligation-5
  "lambda(m:zz,y:rr,m*y)=lambda(k:zz,m:rr,if(0<k, k*m, k=0, 0, k*m))"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (case-split ("0<x_0"))
    simplify
    (block 
      (script-comment "`case-split' at (2)") simplify (case-split ("x_0=0"))
      simplify simplify
      )
    )))

(def-theorem fields-to-rr-obligation-5-permuted
  "lambda(m:zz,y:rr,y*m)=lambda(k:zz,m:rr,if(0<k, k*m, k=0, 0, k*m))"
  (theory h-o-real-arithmetic)
  lemma
  (proof
   (
    (assume-theorem fields-to-rr-obligation-5)
    simplify   
    )))

(def-theorem fields-to-rr-obligation-6
  "forall(h_0:[zz,rr,rr],
     forall(u_0:zz,u_1:rr,
       #(if(0<u_0,
           u_1+h_0([-1]+u_0,u_1),
           u_0=0,
           0,
           [-1]*h_0([-1]*u_0,u_1)))
        implies 
       if(0<u_0,
         u_1+h_0([-1]+u_0,u_1),
         u_0=0,
         0,
         [-1]*h_0([-1]*u_0,u_1))
       =h_0(u_0,u_1))
      implies 
     forall(u_0:zz,u_1:rr,u_1*u_0=h_0(u_0,u_1)))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula " forall(u_0:zz,u_1:rr,
          if(0<u_0, u_1+h_0([-1]+u_0,u_1), u_0=0, 0, [-1]*h_0([-1]*u_0,u_1)) =h_0(u_0,u_1))")
    (weaken (1))
    (case-split ("1<=u_0"))
    (induction trivial-integer-inductor ("u_0"))
    beta-reduce-repeatedly
    (backchain-backwards "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    simplify
    (backchain-backwards "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    simplify
    (instantiate-universal-antecedent "with(p:prop,  forall(u_0:zz,u_1:rr, p))" ("1+t" "u_1"))
    (incorporate-antecedent "with(a,b,c,d:rr,p,q:prop, if(p,a,q,b,c)=d)")
    simplify
    (case-split ("u_0=0"))
    (backchain-backwards "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    simplify
    (backchain-backwards "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    simplify
    (cut-with-single-formula "forall(u_0:zz,u_1:rr, 1<=u_0 implies u_1*u_0=h_0(u_0,u_1))")
    (backchain-backwards "with(h_0:[zz,rr,rr],
  forall(u_0:zz,u_1:rr,1<=u_0 implies u_1*u_0=h_0(u_0,u_1)));")
    simplify
    (weaken (0 1))
    direct-and-antecedent-inference-strategy
    direct-and-antecedent-inference-strategy
    (backchain "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    (cut-with-single-formula "forall(u_0:zz,u_1:rr, #(h_0(u_0,u_1)))")
    (case-split ("0<u_0"))
    simplify
    (case-split ("u_0=0"))
    simplify
    simplify
    insistent-direct-inference
    (case-split ("1<=u_0"))
    (induction trivial-integer-inductor ("u_0"))
    beta-reduce-repeatedly
    (backchain-backwards "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    simplify
    (backchain-backwards "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    simplify
    (backchain-backwards "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    simplify
    (case-split ("u_0=0"))
    (backchain-backwards "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    simplify
    (backchain-backwards "with(p:prop,  forall(u_0:zz,u_1:rr, p))")
    simplify
    (cut-with-single-formula "forall(u_0:zz,u_1:rr, 1<=u_0 implies #(h_0(u_0,u_1)))")
    (backchain "with(h_0:[zz,rr,rr],
  forall(u_0:zz,u_1:rr,1<=u_0 implies #(h_0(u_0,u_1))));")
    simplify
    (weaken (0 1))
    direct-and-antecedent-inference-strategy
    )))

(def-theorem fields-to-rr-obligation-6-permuted
  "forall(h_0:[zz,rr,rr],
     forall(u_0:zz,u_1:rr,
       #(if(0<u_0,
            u_1+h_0([-1]+u_0,u_1),
            u_0=0,
            0,
            [-1]*h_0([-1]*u_0,u_1)))
        implies 
       if(0<u_0,
          u_1+h_0([-1]+u_0,u_1),
          u_0=0,
          0,
          [-1]*h_0([-1]*u_0,u_1))
       =h_0(u_0,u_1))
      implies 
     forall(u_0:zz,u_1:rr,u_0*u_1=h_0(u_0,u_1)))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    (assume-theorem fields-to-rr-obligation-6)
    direct-and-antecedent-inference-strategy
    simplify
    )))


(def-translation fields-to-rr 
  force-under-quick-load
  (source fields)
  (target h-o-real-arithmetic)
  (core-translation fields-to-rr-core)
  (constant-pairs
   (sub_kk sub)
   (/_kk /)
   (pexp "lambda(m:zz,y:rr, if(not(y=0),y^m,?rr))")
   (^_kk ^)
   (*_ext "lambda(m:zz,y:rr, m*y)"))
  (theory-interpretation-check using-simplification))

