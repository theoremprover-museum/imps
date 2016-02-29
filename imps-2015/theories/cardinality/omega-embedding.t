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


(herald OMEGA-EMBEDDING)


;;; Definition of omega%embedding

(def-recursive-constant OMEGA%EMBEDDING
  "lambda(f:[nn,nn], a:sets[nn],
     lambda(k:nn, 
       if(k=0,
          iota(n:nn, n in a and forall(m:nn, m<n implies not(m in a))),
          lambda(z:nn,
            iota(n:nn, n in a and z<n and 
              forall(m:nn, (z<m and m<n) implies (not(m in a)))))(f(k-1)))))"
  (theory h-o-real-arithmetic)
  (definition-name omega%embedding))


;;; Facts about omega%embedding

(def-theorem OMEGA%EMBEDDING-IS-TOTAL
  "total_q{omega%embedding,[sets[nn],[nn,nn]]}"
  (theory h-o-real-arithmetic)
  (usages d-r-convergence)
  (proof
   (
    (unfold-single-defined-constant-globally omega%embedding)
    insistent-direct-inference
    simplify
    )))

(def-theorem OMEGA%EMBEDDING-DEFINEDNESS
  "forall(a:sets[nn],k:nn, 
     #(omega%embedding(a)(k+1)) implies #(omega%embedding(a)(k)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant (0) omega%embedding)
    simplify
    )))

(def-theorem OMEGA%EMBEDDING-STRONG-DEFINEDNESS-LEMMA
  "forall(a:sets[nn],k:zz, 
     0<=k 
       implies 
     (#(omega%embedding(a)(k)) 
       implies 
      forall(m:nn, m<k implies #(omega%embedding(a)(m)))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    (induction integer-inductor ("k"))
    (cut-with-single-formula "m<t or m=t")
    (antecedent-inference "with(t:zz,m:nn,m<t or m=t)")
    (backchain "with(p,q:prop, p implies q)")
    simplify
    (backchain "with(t:zz,m:nn,m=t)")
    simplify
    )))

(def-theorem OMEGA%EMBEDDING-STRONG-DEFINEDNESS
  "forall(a:sets[nn],m,n:nn,
     m<=n and #(omega%embedding(a)(n)) implies #(omega%embedding(a)(m)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "m<n or m=n")
    (antecedent-inference "with(p,q:prop, p or q)")
    (apply-macete-with-minor-premises 
     omega%embedding-strong-definedness-lemma)
    auto-instantiate-existential
    simplify
    simplify
    simplify
    )))

(def-theorem OMEGA%EMBEDDING-DEFINED-AT-ZERO
  "forall(a:sets[nn],
     #(omega%embedding(a)(0))
      implies
     (omega%embedding(a)(0) in a 
       and
      forall(m:nn, m<omega%embedding(a)(0) implies not(m in a))))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (unfold-single-defined-constant-globally omega%embedding)
    simplify
    direct-inference
    direct-inference
    (eliminate-defined-iota-expression 0 w)
    simplify
    )))

(def-theorem OMEGA%EMBEDDING-AT-NONEMPTY-INDIC
  "forall(a:sets[nn],
     nonempty_indic_q{a} implies #(omega%embedding(a)(0)))"
  (theory h-o-real-arithmetic)
  (proof	
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem 
     well-ordering-for-natural-numbers ("lambda(x:nn,x in a)"))
    (instantiate-universal-antecedent "with(p:prop, forall(x_0:nn,p))" ("x"))
    (simplify-antecedent "with(p:prop, not(p))")
    (beta-reduce-antecedent "with(u:nn,p:prop, lambda(x:nn,p)(u))")
    (beta-reduce-antecedent "with(p:prop, forall(v:nn,p))")
    (unfold-single-defined-constant-globally omega%embedding)
    simplify
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (instantiate-existential ("u"))
    (antecedent-inference-strategy (0 1))
    (cut-with-single-formula "j<u or j=u or u<j")
    (antecedent-inference "with(u,j:nn,j<u or j=u or u<j)")
    (instantiate-universal-antecedent 
     "with(a:sets[nn],u:nn,forall(v:nn,v<u implies not(v in a)))" ("j"))
    (instantiate-universal-antecedent 
     "with(a:sets[nn],j:nn,forall(m:nn,m<j implies not(m in a)))" ("u"))
    simplify
    )))

(def-theorem MONOTONICITY-OF-OMEGA%EMBEDDING
  "forall(a:sets[nn],forall(k:zz, 
     0<=k
      implies 
     (#(omega%embedding(a)(k+1)) 
       implies 
      omega%embedding(a)(k) < omega%embedding(a)(k+1))))"
  (theory h-o-real-arithmetic)
  (proof				; 62 nodes
   (
    (apply-macete-with-minor-premises integer-induction)
    simplify
    direct-inference
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(omega%embedding(a)(0))")
    (incorporate-antecedent "with(a:sets[nn],#(omega%embedding(a)(1)))")
    (unfold-single-defined-constant (0 2) omega%embedding)
    simplify
    direct-inference
    (eliminate-defined-iota-expression 0 w)
    (apply-macete-with-minor-premises omega%embedding-definedness)
    (weaken (0))
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises omega%embedding-definedness)
    simplify
    (incorporate-antecedent "with(a:sets[nn],#(omega%embedding(a)(2+t)))")
    (unfold-single-defined-constant (0 2) omega%embedding)
    simplify
    direct-inference
    (eliminate-defined-iota-expression 0 w)
    )))

(def-theorem STRONG-MONOTONICITY-OF-OMEGA%EMBEDDING-LEMMA
  "forall(a:sets[nn],forall(k:zz,
     0<=k 
      implies 
     forall(m:nn, 
       m<k and #(omega%embedding(a)(k)) 
        implies 
       omega%embedding(a)(m) < omega%embedding(a)(k))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises integer-induction)
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "m<t or m=t")
    (antecedent-inference "with(p,q:prop, p or q)")
    (instantiate-universal-antecedent "with(p:prop, forall(m:nn,p))" ("m"))
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises omega%embedding-definedness)
    simplify
    (cut-with-single-formula "omega%embedding(a)(t)<omega%embedding(a)(t+1)")
    simplify
    (apply-macete-with-minor-premises monotonicity-of-omega%embedding)
    (weaken (0 2 3))
    simplify
    (backchain "with(t:zz,m:nn,m=t)")
    (force-substitution "1+t" "t+1" (0))
    (apply-macete-with-minor-premises monotonicity-of-omega%embedding)
    (weaken (0 2 3))
    simplify
    simplify
    )))

(def-theorem STRONG-MONOTONICITY-OF-OMEGA%EMBEDDING
  "forall(a:sets[nn],m,n:nn,
     m<n and #(omega%embedding(a)(n)) 
      implies 
     omega%embedding(a)(m) < omega%embedding(a)(n))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises 
     strong-monotonicity-of-omega%embedding-lemma)
    simplify
    )))

(def-theorem WEAK-MONOTONICITY-OF-OMEGA%EMBEDDING-LEMMA
  "forall(a:sets[nn],forall(k:zz, 
     0<=k
       implies 
     (#(omega%embedding(a)(k)) implies k <= omega%embedding(a)(k))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises integer-induction)
    simplify
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop, not(p))")
    (apply-macete-with-minor-premises omega%embedding-definedness)
    simplify
    (cut-with-single-formula "omega%embedding(a)(t)<omega%embedding(a)(t+1)")
    simplify
    (apply-macete-with-minor-premises monotonicity-of-omega%embedding)
    simplify
    )))

(def-theorem WEAK-MONOTONICITY-OF-OMEGA%EMBEDDING
  "forall(a:sets[nn],m:nn,
     #(omega%embedding(a)(m)) implies m <= omega%embedding(a)(m))"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises 
     weak-monotonicity-of-omega%embedding-lemma)
    simplify
    )))

(def-theorem INJECTIVENESS-OF-OMEGA%EMBEDDING
  "forall(a:sets[nn], injective_q{omega%embedding(a)})"
  (theory h-o-real-arithmetic)
  (proof
   (
    insistent-direct-inference-strategy
    (cut-with-single-formula "x_1=x_2 or x_1<x_2 or x_2<x_1")
    (antecedent-inference "with(p,q,r:prop, p or q or r)")
    (instantiate-theorem 
     strong-monotonicity-of-omega%embedding ("a" "x_1" "x_2"))
    (simplify-antecedent "with(x,y:nn, x<y)")
    (instantiate-theorem 
     strong-monotonicity-of-omega%embedding ("a" "x_2" "x_1"))
    (simplify-antecedent "with(x,y:nn, x<y)")
    simplify
    )))

(def-theorem RAN-OF-OMEGA%EMBEDDING-IS-SUBSET
  "forall(a:sets[nn], ran{omega%embedding(a)} subseteq a)"
  (theory h-o-real-arithmetic)
  (proof				; 56 nodes
   (
    direct-inference
    insistent-direct-inference
    beta-reduce-insistently
    (raise-conditional (0))
    simplify
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "#(omega%embedding(a)(x))")
    (contrapose "with(x,y:nn, x=y)")
    (unfold-single-defined-constant-globally omega%embedding)
    (raise-conditional (0))
    (contrapose "with(p:prop, not(p))")
    (antecedent-inference "with(p,q,r:prop, if_form(p,q,r))")
    (backchain "with(p:prop, x:nn, x=iota(y:nn,p))")
    (eliminate-defined-iota-expression 0 w)
    (cut-with-single-formula "#(omega%embedding(a)(x-1))")
    (beta-reduce-antecedent "with(x,y:nn, x=y)")
    (backchain "with(p:prop, x:nn, x=iota(y:nn,p))")
    (eliminate-defined-iota-expression 0 w)
    )))

(def-theorem OMEGA%EMBEDDING-AT-FINITE-SET-LEMMA
  "forall(a:sets[nn], n:nn,
     a subseteq omega(n) implies not(#(omega%embedding(a)(n))))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "ran{omega%embedding(a)} subseteq a")
    (instantiate-transported-theorem 
     subseteq-transitivity () ("ran{omega%embedding(a)}" "a" "omega(n)"))
    (weaken (1 2))
    (contrapose "with(a,b:sets[nn], a subseteq b)")
    (instantiate-existential ("omega%embedding(a)(n)"))
    beta-reduce-insistently
    simplify
    (instantiate-existential ("n"))
    (apply-macete-with-minor-premises finite-cardinal-members-are-<)
    (force-substitution 
     "not(omega%embedding(a)(n)<n)" "n<=omega%embedding(a)(n)" (0))
    (apply-macete-with-minor-premises weak-monotonicity-of-omega%embedding)
    direct-inference
    simplify
    (apply-macete-with-minor-premises ran-of-omega%embedding-is-subset)
    )))

(def-theorem DOM-OF-OMEGA%EMBEDDING-AT-FINITE-SET
  "forall(a:sets[nn], n:nn,
     a subseteq omega(n) 
      implies 
     forsome(m:nn, m<=n and dom{omega%embedding(a)}=omega(m)))"
  (theory h-o-real-arithmetic)
  (proof				; 128 nodes
   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem omega%embedding-at-finite-set-lemma ("a" "n"))
    (instantiate-theorem 
     induct
     ("lambda(k:zz, 0<=k implies #(omega%embedding(a)(k)))" "0"))
    (block 
     (script-comment "node added by `instantiate-theorem' at (0 0 0)")
     (instantiate-universal-antecedent 
      "with(f:[zz,prop],forall(t:zz,0<=t implies f(t)));"
      ("n"))
     (simplify-antecedent "with(n:nn,not(0<=n));")
     (simplify-antecedent 
      "with(n:nn,a:sets[nn], 
        lambda(k:zz,0<=k implies #(omega%embedding(a)(k)))(n));"))
    (block 
     (script-comment "node added by `instantiate-theorem' at (0 1 0 0 0)")
     (simplify-antecedent "with(f:[zz,prop],not(f(0)));")
     (weaken (1 2 3 4))
     (instantiate-existential ("0"))
     simplify
     (block 
      (script-comment "node added by `instantiate-existential' at (0 1)")
      (apply-macete-with-minor-premises omega-0-is-empty-indicator)
      extensionality
      direct-inference
      simplify
      (contrapose "with(p:prop,not(p));")
      (apply-macete-with-minor-premises omega%embedding-strong-definedness)
      (instantiate-existential ("x_0"))
      simplify))
    (block 
     (script-comment 
      "node added by `instantiate-theorem' at (0 1 1 0 0 0 0 0)")
     (weaken (0 1))
     (simplify-antecedent "with(t:zz,f:[zz,prop],f(t));")
     (simplify-antecedent "with(r:rr,f:[zz,prop],not(f(r)));")
     (instantiate-existential ("1+t"))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 0)")
      (cut-with-single-formula "n<1+t or 1+t<=n")
      (block 
       (script-comment "node added by `cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,p or p);")
       (cut-with-single-formula "n<t or n=t")
       (block 
	(script-comment "node added by `cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,p or p);")
	(instantiate-theorem strong-monotonicity-of-omega%embedding
			     ("a" "n" "t"))
	(simplify-antecedent 
	 "with(n:nn,a:sets[nn],not(#(omega%embedding(a)(n))));"))
       (block 
	(script-comment "node added by `cut-with-single-formula' at (1)")
	(weaken (1 2 3 4 5))
	simplify))
      (block 
       (script-comment "node added by `cut-with-single-formula' at (1)")
       (weaken (0 1 2 3 4))
       simplify))
     (block 
      (script-comment "node added by `instantiate-existential' at (0 1)")
      extensionality
      direct-inference
      simplify
      (cut-with-single-formula "x_0<=t or 1+t<=x_0")
      (block 
       (script-comment "node added by `cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,p or p);")
       (block 
	(script-comment "node added by `antecedent-inference' at (0)")
	direct-and-antecedent-inference-strategy
	(apply-macete-with-minor-premises finite-cardinal-application)
	(block 
	 (script-comment 
	  "node added by `direct-and-antecedent-inference-strategy' at (1)")
	 (contrapose 
	  "with(x_0:nn,a:sets[nn],not(#(omega%embedding(a)(x_0))));")
	 (apply-macete-with-minor-premises omega%embedding-strong-definedness)
	 (instantiate-existential ("t"))))
       (block 
	(script-comment "node added by `antecedent-inference' at (1)")
	direct-and-antecedent-inference-strategy
	(block 
	 (script-comment 
	  "node added by `direct-and-antecedent-inference-strategy' at (0)")
	 (contrapose "with(t:zz,a:sets[nn],not(#(omega%embedding(a)(1+t))));")
	 (apply-macete-with-minor-premises omega%embedding-strong-definedness)
	 (instantiate-existential ("x_0")))
	simplify))
      simplify))

    )))

(def-theorem RAN-OF-OMEGA%EMBEDDING-LEMMA-1
  "forall(a:sets[nn],
     forsome(x:nn,
       if_form(x=0,
         (0 in a implies omega%embedding(a)(x)=0)
          and 
         forall(m:nn,m<0 implies not(m in a)),
         (0 in a implies omega%embedding(a)(x)=0)
          and 
         omega%embedding(a)(x-1)<0
          and 
         forall(m:nn,
           omega%embedding(a)(x-1)<m and m<0
            implies 
           not(m in a)))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-inference
    (instantiate-existential ("0"))
    (unfold-single-defined-constant-globally omega%embedding)
    simplify
    (eliminate-iota 0)
    (instantiate-existential ("0"))
    (contrapose "with(m:nn,m<0)")
    (weaken (0 1 2))
    simplify
    (cut-with-single-formula "0<z%iota or z%iota=0 or 0<z%iota")
    (antecedent-inference "with(p,q,r:prop, p or q or r)")
    (weaken (2 4))
    (antecedent-inference "with(p,q:prop, p and q)")
    (instantiate-universal-antecedent "with(p:prop, forall(m:nn,p))" ("0"))
    (weaken (0 1 2 3))
    simplify
    (contrapose "with(m:nn,m<0)")
    )))

(def-theorem RAN-OF-OMEGA%EMBEDDING-LEMMA-2
  "forall(t:nn,a:sets[nn],
     not(t in a) and forall(m:nn,m<t implies not(m in a))
      implies
     forsome(x:nn,
       if_form(x=0,
         ((t+1) in a implies omega%embedding(a)(x)=t+1)
          and 
         forall(m:nn,m<t+1 implies not(m in a)),
         ((t+1) in a implies omega%embedding(a)(x)=t+1)
          and 
         omega%embedding(a)(x-1)<t+1
          and 
         forall(m:nn,
           omega%embedding(a)(x-1)<m and m<t+1
            implies 
           not(m in a)))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("0"))
    (instantiate-theorem omega%embedding-defined-at-zero ("a"))
    (contrapose "with(p:prop, p)")
    (apply-macete-with-minor-premises omega%embedding-at-nonempty-indic)
    (instantiate-existential ("t+1"))
    (cut-with-single-formula 
     "omega%embedding(a)(0)<t or omega%embedding(a)(0)=t or 
      omega%embedding(a)(0)=t+1 or t+1<omega%embedding(a)(0)")
    (antecedent-inference "with(p,q,r,s:prop, p or q or r or s)")
    (instantiate-universal-antecedent 
     "with(a:sets[nn],t:nn,forall(m:nn,m<t implies not(m in a)))" 
     ("omega%embedding(a)(0)"))
    (contrapose "with(p:prop, not(p))")
    (weaken (0 1 2 3 5))
    simplify
    (instantiate-universal-antecedent 
     "with(a:sets[nn], 
        forall(m:nn,m<omega%embedding(a)(0) implies not(m in a)))" 
     ("t+1"))
    (weaken (0 2 3 4 5))
    simplify
    (cut-with-single-formula "m<t or m=t")
    (antecedent-inference "with(p,q:prop, p or q)")
    (instantiate-universal-antecedent 
     "with(a:sets[nn],t:nn,forall(m:nn,m<t implies not(m in a)))" 
     ("m"))
    (weaken (1 2 3 4))
    simplify
    simplify
    )))

(def-theorem RAN-OF-OMEGA%EMBEDDING-LEMMA-3
  "forall(t:nn,a:sets[nn],
     omega%embedding(a)(0)=t and forall(m:nn,m<t implies not(m in a))
      implies
     forsome(x:nn,   
       if_form(x=0,
         ((t+1) in a implies omega%embedding(a)(x)=t+1)
          and 
         forall(m:nn,m<t+1 implies not(m in a)),
         ((t+1) in a implies omega%embedding(a)(x)=t+1)
          and 
         omega%embedding(a)(x-1)<t+1
          and 
         forall(m:nn,
           omega%embedding(a)(x-1)<m and m<t+1
            implies 
           not(m in a)))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("1"))
    (simplify-antecedent "1=0")
    (simplify-antecedent "1=0")
    (unfold-single-defined-constant-globally omega%embedding)
    simplify
    (eliminate-iota 0)
    (instantiate-existential ("t+1"))
    simplify
    (simplify-antecedent "with(p,q:prop, p and q)")
    (weaken (1 3))
    (antecedent-inference "with(p,q,r:prop, p and q and r)")
    (instantiate-universal-antecedent 
     "with(p:prop, forall(m_$1:nn,p))" ("t+1"))
    (simplify-antecedent "with(t:nn,not(t<t+1))")
    simplify
    simplify
    (simplify-antecedent "with(p,q:prop, p and q)")
    )))
    
(def-theorem RAN-OF-OMEGA%EMBEDDING-LEMMA-4
  "forall(x,t:nn,a:sets[nn],   
     not(t in a) 
      and 
     omega%embedding(a)(x)<t 
      and
     forall(m:nn, omega%embedding(a)(x)<m and m<t implies not(m in a))
      implies
     forsome(x:nn,
       if_form(x=0,
         ((t+1) in a implies omega%embedding(a)(x)=t+1)
          and 
         forall(m:nn,m<t+1 implies not(m in a)),
         ((t+1) in a implies omega%embedding(a)(x)=t+1)
          and 
         omega%embedding(a)(x-1)<t+1
          and 
         forall(m:nn,
           omega%embedding(a)(x-1)<m and m<t+1
            implies 
           not(m in a)))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x+1"))
    (simplify-antecedent "with(x:nn,x+1=0)")
    (simplify-antecedent "with(x:nn,x+1=0)")
    (unfold-single-defined-constant-globally omega%embedding)
    simplify
    (eliminate-iota 0)
    (instantiate-existential ("t+1"))
    simplify
    (instantiate-universal-antecedent "with(p:prop, forall(m:nn,p))" ("m_$1"))
    (cut-with-single-formula "m_$1=t")
    simplify
    simplify
    (weaken (3 4))
    (antecedent-inference 
     "with(t:nn,a:sets[nn],p,q:prop, (t+1) in a and p and q)")
    (instantiate-universal-antecedent 
     "with(p:prop, forall(m_$1:nn,p))" ("z%iota_$0"))
    (antecedent-inference "with(p,q,r:prop, p and q and r)")
    (instantiate-universal-antecedent 
     "with(p:prop, forall(m_$1:nn,p))" ("t+1"))
    (weaken (1 2 3 4 5 6))
    simplify
    simplify
    (cut-with-single-formula "not(m_$0=t+1)")
    (instantiate-universal-antecedent "with(p:prop, forall(m:nn,p))" ("m_$0"))
    (simplify-antecedent "with(p,q:prop, p and q)")
    (cut-with-single-formula "m_$0=t")
    simplify
    simplify
    simplify
    )))


(def-theorem RAN-OF-OMEGA%EMBEDDING-LEMMA-5
  "forall(t,x:nn,a:sets[nn],
     omega%embedding(a)(x)<t
      and
     omega%embedding(a)(x+1)=t
      and
     forall(m:nn,omega%embedding(a)(x)<m and m<t implies not(m in a))
      implies
     forsome(x:nn,
       if_form(x=0,
         ((t+1) in a implies omega%embedding(a)(x)=t+1)
          and 
         forall(m:nn,m<t+1 implies not(m in a)),
         ((t+1) in a implies omega%embedding(a)(x)=t+1)
          and 
         omega%embedding(a)(x-1)<t+1
          and 
         forall(m:nn,
           omega%embedding(a)(x-1)<m and m<t+1
            implies 
           not(m in a)))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("x+2"))
    (simplify-antecedent "with(x:nn,x+2=0)")
    (simplify-antecedent "with(x:nn,x+2=0)")
    (unfold-single-defined-constant-globally omega%embedding)
    simplify
    (force-substitution "1+x" "x+1" (0))
    beta-reduce-repeatedly
    (eliminate-iota 0)
    (instantiate-existential ("t+1"))
    simplify
    (contrapose "with(p,q:prop, p and q)")
    (weaken (0 1 2 3 4 6))
    simplify
    (weaken (3 4))
    (antecedent-inference 
     "with(t:nn,a:sets[nn],p,q:prop, (t+1) in a and p and q)")
    (instantiate-universal-antecedent 
     "with(p:prop, forall(m_$1:nn,p))" ("z%iota_$0"))
    (antecedent-inference "with(p,q,r:prop, p and q and r)")
    (instantiate-universal-antecedent 
     "with(p:prop, forall(m_$1:nn,p))" ("t+1"))
    (weaken (1 2 3 4 5 6))
    simplify
    (weaken (0 1 2 2 3 4))
    simplify
    (force-substitution "(x+2)-1" "x+1" (0))
    simplify
    (weaken (0 1 2 3 4))
    simplify
    (contrapose "with(p,q:prop, p and q)")
    (weaken (0 1 2 3 4 6))
    (force-substitution "(x+2)-1" "x+1" (0))
    simplify
    )))

(def-theorem RAN-OF-OMEGA%EMBEDDING-LEMMA
  "forall(a:sets[nn],
     forall(k:zz,
       0<=k 
        implies
       forsome(x:nn,
         if_form(x=0,
           (k in a implies omega%embedding(a)(x)=k) 
             and
           forall(m:nn, m<k implies not(m in a)),
           (k in a implies omega%embedding(a)(x)=k) 
             and
           omega%embedding(a)(x-1)<k 
            and
           forall(m:nn, 
             omega%embedding(a)(x-1)<m and m<k 
              implies 
             not(m in a))))))"
  lemma
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises integer-induction)
    beta-reduce-repeatedly
    direct-inference
    direct-inference
    (apply-macete-with-minor-premises ran-of-omega%embedding-lemma-1)
    (weaken (0))
    direct-inference
    direct-inference
    direct-inference
    (antecedent-inference "with(p:prop, p)")
    (antecedent-inference-strategy (0))
    (apply-macete-with-minor-premises ran-of-omega%embedding-lemma-2)
    simplify
    (apply-macete-with-minor-premises ran-of-omega%embedding-lemma-3)
    (backchain-backwards "with(x:nn,x=0)")
    simplify
    (apply-macete-with-minor-premises ran-of-omega%embedding-lemma-4)
    (instantiate-existential ("x-1"))
    (apply-macete-with-minor-premises ran-of-omega%embedding-lemma-5)
    (instantiate-existential ("x-1"))
    simplify
    )))
    
(def-theorem RAN-OF-OMEGA%EMBEDDING
  "forall(a:sets[nn], ran{omega%embedding(a)}=a)"
  (theory h-o-real-arithmetic)
  (proof
   (
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (apply-macete-with-minor-premises ran-of-omega%embedding-is-subset)
    insistent-direct-inference-strategy
    beta-reduce-insistently
    simplify
    (instantiate-theorem ran-of-omega%embedding-lemma ("a"))
    (instantiate-universal-antecedent "with(p:prop, forall(k:zz,p))" ("x_$1"))
    (simplify-antecedent "with(x_$1:nn,not(0<=x_$1))")
    (weaken (1 2 3))
    (instantiate-existential ("x"))
    (instantiate-universal-antecedent "with(p:prop, forall(m:nn,p))" ("x_$1"))
    (weaken (0 2 3 4))
    )))

(def-theorem BIJECTIVENESS-OF-OMEGA%EMBEDDING-AT-FINITE-SET
  "forall(a:sets[nn], n:nn,
     a subseteq omega(n) 
       implies 
     forsome(m:nn, m<=n and bijective_on_q{omega%embedding(a),omega(m),a}))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem dom-of-omega%embedding-at-finite-set ("a" "n"))
    auto-instantiate-existential
    insistent-direct-inference
    insistent-direct-inference
    (apply-macete-with-minor-premises ran-of-omega%embedding)
    (apply-macete-with-minor-premises tr%injective-implies-injective-on)
    (apply-macete-with-minor-premises injectiveness-of-omega%embedding)
    )))

(def-theorem SUBSET-OF-FINITE-CARDINAL-IS-EQUINUMEROUS
  "forall(a:sets[nn], n:nn,
     a subseteq omega(n) 
       implies 
     forsome(m:nn, m<=n and a equinumerous omega(m)))"
  (theory h-o-real-arithmetic)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (instantiate-theorem 
     bijectiveness-of-omega%embedding-at-finite-set ("a" "n"))
    auto-instantiate-existential
    (apply-macete-with-minor-premises tr%equinumerous-is-symmetric)
    auto-instantiate-existential
    insistent-direct-inference-strategy
    )))

