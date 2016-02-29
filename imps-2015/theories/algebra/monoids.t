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


(herald monoids)

(load-section foundation)

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

(def-print-syntax monoid%prod tex
  (token " \\prod ")
  (method present-tex-interval-iteration-operator)
  (binding 50))

(make-tex-correspondence "uu" " \{ \\bf U \}")

(def-theorem monoid-prod-out
  "forall(f:[zz,uu],m,n:zz,n<=m implies 
             monoid%prod(n,m,f)==monoid%prod(n,m-1,f)**f(m))"
  (theory monoid-theory)
  (proof

   (
   
    (induction integer-inductor ())

    )

   )
  (usages transportable-macete))

(def-theorem monoid-triv-prod
  "forall(f:[zz,uu],n,m:zz,m=n implies monoid%prod(n,m,f)==f(n))"
  (theory monoid-theory)

  (proof

   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) monoid%prod)
    (unfold-single-defined-constant (0) monoid%prod)
    simplify

    )
   )
  (usages transportable-macete))

(def-theorem monoid-null-prod
  "forall(f:[zz,uu],n,m:zz,m<n implies monoid%prod(n,m,f)=e)"
  (theory monoid-theory)

  (proof

   (

    (unfold-single-defined-constant (0) monoid%prod)
    simplify

    )
   )
  (usages transportable-macete))



(def-theorem locality-for-monoid-prod
  "forall(f,g:[zz,uu],p,m:zz,forall(x:zz, 
 p<=x and x<=m implies f(x)==g(x)) implies monoid%prod(p,m,f)==monoid%prod(p,m,g))"
  (theory monoid-theory)
  (usages transportable-macete)
  
  (proof 

   (

    direct-inference
    (case-split ("p<=m"))
    (induction integer-inductor ())
    (prove-by-logic-and-simplification 3)
    (apply-macete-with-minor-premises monoid-null-prod)


    )))

(def-theorem local-context-introduction-for-monoid-prod
  "forall(f:[zz,uu],m,n:zz,
monoid%prod(m,n,f)==monoid%prod(m,n,lambda(j:zz,if(m<=j and j<=n,f(j),e))))"
  (theory monoid-theory)
  (usages transportable-macete)

  (proof

   (

    direct-inference
    (instantiate-theorem locality-for-monoid-prod ("f" "lambda(j:zz,if(m<=j and j<=n, f(j), e))" "m" "n"))
    (contrapose "with(p:prop, not(p))")
    simplify
    (contrapose "with(p:prop, not(p))")
    simplify


    )

   ))

(def-theorem interval-multiplicativity
  "forall(m,n,p:zz, f:[zz,uu], m<=n and n<=p implies 
            monoid%prod(m,n,f) ** monoid%prod(n+1,p,f)
                ==
            monoid%prod(m,p,f))"

  (proof
   (
    
    (induction integer-inductor ("p"))

    )

   )
  (usages transportable-macete)
  (theory monoid-theory))



(def-theorem translation-invariance
  "forall(m,n,p:zz, f:[zz,uu],
            monoid%prod(m,n,f) == monoid%prod(m+p,n+p, lambda(n:zz, f(n-p))))"
  
  
  (proof

   (

    direct-inference
    (case-split ("m<=n"))
    (induction integer-inductor ())
    (unfold-single-defined-constant (1) monoid%prod)
    simplify
    (apply-macete-with-minor-premises monoid-null-prod)


    )

   )

  (usages transportable-macete)
  (theory monoid-theory))

(def-theory commutative-monoid-theory
  (component-theories monoid-theory)
  (axioms
   (commutative-law-for-monoids "forall(x,y:uu, x ** y = y **x)")))

(set (current-theory) (name->theory 'commutative-monoid-theory))

(def-constant zz%interval
  "lambda(a,b:zz, indic{k:zz, a<=k and k<=b})"
  (theory h-o-real-arithmetic))

(def-print-syntax zz%interval
  tex
  (token (" [ " " ] "))
  (method present-tex-delimited-expression)
  (binding 80))


(def-theorem reordering-lemma
  "forall(a,b,d:zz, f:[zz,uu], a<=d and d<=b implies 
     monoid%prod(a,b,f)==monoid%prod(a,d-1,f)**monoid%prod(d+1,b,f)**f(d))"
  
  (proof
   (
    (force-substitution "monoid%prod(a,d+1,f)**f(d)" "monoid%prod(a,d+1,f)**f(d)" ())
    (force-substitution "monoid%prod(d+1,b,f)**f(d)" "f(d)**monoid%prod(d+1,b,f)" (0))
    (force-substitution "monoid%prod(a,b,f)" "monoid%prod(a,d,f) ** monoid%prod(d+1,b,f)" (0))
    (unfold-single-defined-constant (0) monoid%prod)
    simplify
    (apply-macete-with-minor-premises interval-multiplicativity)
    (apply-macete-locally-with-minor-premises commutative-law-for-monoids (0) " monoid%prod(d+1,b,f)**f(d) ")

    ))

  (theory commutative-monoid-theory))

(def-constant nullify%on%set
  "lambda(f:[zz,uu],a:sets[zz], lambda(x:zz, if(x in a, e,f(x))))"
  (theory monoid-theory))

(def-print-syntax nullify%on%set
  TEX
  (token " { \\cal N } ")
  (method present-tex-prefix-operator)
  (binding 80))

(def-theorem reordering-lemma-corollary
  "forall(a,b,d:zz, f:[zz,uu], a<=d and d<=b implies 
           monoid%prod(a,b,f)==monoid%prod(a,b,nullify%on%set(f,singleton{d})) ** f(d))"

  (proof


   (

    (unfold-single-defined-constant (0) nullify%on%set)
    (apply-macete-with-minor-premises tr%singleton-equality-conversion)
    (force-substitution "monoid%prod(a,b,lambda(j:zz,if(j=d, e, f(j))))"
			"monoid%prod(a,d-1,lambda(j:zz,if(j=d, e, f(j))))**
                         monoid%prod(d+1,b,lambda(j:zz,if(j=d, e, f(j))))** 
                         lambda(j:zz,if(j=d, e, f(j)))(d)" (0))
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "monoid%prod(a,d-1,lambda(j:zz,if(j=d, e, f(j)))) == 
                              monoid%prod(a,d-1,f) and  
                              monoid%prod(d+1,b,lambda(j:zz,if(j=d, e, f(j))))==monoid%prod(d+1,b,f)")
    (backchain "with(b:zz,f:[zz,uu],d,a:zz,
monoid%prod(a,d-1,lambda(j:zz,if(j=d, e, f(j))))
  ==monoid%prod(a,d-1,f)
   and 
  monoid%prod(d+1,b,lambda(j:zz,if(j=d, e, f(j))))
  ==monoid%prod(d+1,b,f));")
    (backchain "with(b:zz,f:[zz,uu],d,a:zz,
  monoid%prod(a,d-1,lambda(j:zz,if(j=d, e, f(j))))
  ==monoid%prod(a,d-1,f)
   and 
  monoid%prod(d+1,b,lambda(j:zz,if(j=d, e, f(j))))
  ==monoid%prod(d+1,b,f));")
    beta-reduce-repeatedly
    (force-substitution "monoid%prod(d+1,b,f)**if(d=d, e, f(d))" "monoid%prod(d+1,b,f)" (0))
    (force-substitution "(monoid%prod(a,d-1,f)**monoid%prod(d+1,b,f))**f(d)" "monoid%prod(a,d-1,f)**(monoid%prod(d+1,b,f)**f(d))" (0))
    (apply-macete-with-minor-premises reordering-lemma)
    (apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)
    simplify
    direct-inference
    (apply-macete-with-minor-premises locality-for-monoid-prod)
    (prove-by-logic-and-simplification 3)
    (apply-macete-with-minor-premises locality-for-monoid-prod)
    (prove-by-logic-and-simplification 3)
    (apply-macete-with-minor-premises reordering-lemma)


    ))

  (theory commutative-monoid-theory))

(def-theorem nullify%incrementally
  "forall(c,t:zz,f:[zz,uu], phi:[zz,zz], c<=t implies 
       nullify%on%set(f,image{phi,zz%interval(c,t)})=
       nullify%on%set(nullify%on%set(f,image{phi,zz%interval(c,t-1)}),singleton{phi(t)}))"
  (proof

   (
   

    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    extensionality
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
      (case-split-on-conditionals (0 1))
      (antecedent-inference "with(p:prop,p and p);")
      (cut-with-single-formula "not(forsome(x:zz,c<=x and x<=t and x_0=phi(x)))")
      (block 
	(script-comment "cut-with-single-formula' at (0)")
	simplify
	(contrapose "with(phi:[zz,zz],x_0,t,c:zz,
  not(forsome(x:zz,c<=x and 1+x<=t and x_0=phi(x))));")
	(instantiate-existential ("x"))
	(cut-with-single-formula "not(x=t)")
	simplify
	(block 
	  (script-comment "node added by `cut-with-single-formula' at (1)")
	  (contrapose "with(z,x_0:zz,not(x_0=z));")
	  simplify))
      (block 
	(script-comment "node added by `cut-with-single-formula' at (1)")
	(contrapose "with(p:prop,not(forsome(x:zz,p)));")
	(instantiate-existential ("x"))
	(cut-with-single-formula "not(x=t)")
	simplify
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (contrapose "with(p:prop,not(p));")
	  simplify)))
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0)")
      (contrapose "with(p:prop,not(p));")
      (instantiate-existential ("t"))
      simplify)
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 1 0 0 0)")
      (contrapose "with(p:prop,not(forsome(x:zz,p)));")
      (instantiate-existential ("x"))
      simplify)



    ))


  (theory monoid-theory))

;;used to be

(comment
    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    extensionality
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (0 0 0)")
     (case-split-on-conditionals (0 1))
     (antecedent-inference "with(p:prop,p and p);")
     (cut-with-single-formula "not(forsome(x:zz,c<=x and x<=t and x_0=phi(x)))")
     (block 
      (script-comment "node added by `cut-with-single-formula' at (0)")
      simplify
      (contrapose "with(phi:[zz,zz],x_0,t,c:zz,
  not(forsome(x:zz,c<=x and 1+x<=t and x_0=phi(x))));")
      (instantiate-existential ("x"))
      (cut-with-single-formula "not(x=t)")
      simplify
      (block 
       (script-comment "node added by `cut-with-single-formula' at (1)")
       (contrapose "with(z,x_0:zz,not(x_0=z));")
       simplify))
     (block 
      (script-comment "node added by `cut-with-single-formula' at (1)")
      (contrapose "with(p:prop,not(forsome(x:zz,p)));")
      (antecedent-inference "with(p:prop,forsome(x:zz,p));")
      (move-to-ancestor 1)
      (instantiate-existential ("x"))
      (cut-with-single-formula "not(x=t)")
      simplify
      (block 
       (script-comment "node added by `cut-with-single-formula' at (1)")
       (contrapose "with(p:prop,not(p));")
       simplify)))
    (block 
     (script-comment "node added by `direct-and-antecedent-inference-strategy' at (1)")
     (case-split-on-conditionals (0 1))
     (block 
      (script-comment "node added by `case-split-on-conditionals' at (1 0)")
      (antecedent-inference "with(p:prop,p and p);")
      (cut-with-single-formula "forsome(x:zz,c<=x and x<=t and x_0=phi(x))")
      (instantiate-existential ("x"))
      simplify)
     (block 
      (script-comment "node added by `case-split-on-conditionals' at (2 0)")
      (antecedent-inference "with(p:prop,p and p);")
      (cut-with-single-formula "forsome(x:zz,c<=x and x<=t and x_0=phi(x))")
      (instantiate-existential ("t"))
      simplify)
     (block 
      (script-comment "node added by `case-split-on-conditionals' at (3 0)")
      (antecedent-inference "with(p:prop,p and p);")
      (cut-with-single-formula "forsome(x:zz,c<=x and x<=t and x_0=phi(x))")
      (instantiate-existential ("x"))
      simplify))

    )

(def-theorem general-commutative-law-induction-step-lemma
  "forall(phi:[zz,zz],t,c:zz,f:[zz,uu],b,a:zz, 
        c<=t and 
        phi(t) in zz%interval(a,b) and
        injective_q{phi} 
          implies
         monoid%prod(a,
                     b,
                     nullify%on%set(f,image{phi,zz%interval(c,t)})) ** f(phi(t))
        ==monoid%prod(a,
                      b,
                      nullify%on%set(f,
                                     image{phi,
                                           zz%interval(c,t-1)})))"


  (proof
   
   (

    (unfold-single-defined-constant (0) zz%interval)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (apply-macete nullify%incrementally)
    (force-substitution "f(phi(t))" "nullify%on%set(f, image{phi, zz%interval(c, t- 1)})(phi(t))" (0))
    (apply-macete-with-minor-premises reordering-lemma-corollary)
    (unfold-single-defined-constant (0) nullify%on%set)
    (force-substitution "phi(t) in image{phi,zz%interval(c,t-1)}" "falsehood" (0))
    (unfold-single-defined-constant (0) zz%interval)
    simplify-insistently
    (contrapose "with(phi:[zz,zz],injective_q{phi});")
    (instantiate-existential ("t" "x_$2"))
    simplify

    ))

   (theory commutative-monoid-theory))



(def-theorem commutative-law-stack-lemma
  "forall(phi:[zz,zz],t,c:zz,f:[zz,uu],b,a:zz, 
        c<=t and 
        phi(t) in zz%interval(a,b) and
        injective_q{phi} 
          implies
         monoid%prod(a,
                     b,
                     nullify%on%set(f,image{phi,zz%interval(c,t)})) ** 
          monoid%prod(c,t,f oo phi)
        ==monoid%prod(a,
                      b,
                      nullify%on%set(f,
                                     image{phi,
                                           zz%interval(c,t-1)}))
          **
          monoid%prod(c,t-1,f oo phi))"

  (theory commutative-monoid-theory)

  (proof
   (

    direct-and-antecedent-inference-strategy
    (apply-macete monoid-prod-out)
    (force-substitution "monoid%prod(c,t-1,f oo phi)**f oo phi(t)" "f (phi(t)) ** monoid%prod(c,t-1,f oo phi)" (0))
    (apply-macete-with-minor-premises associative-law-for-multiplication-for-monoids)
    (apply-macete-with-minor-premises general-commutative-law-induction-step-lemma)
    simplify-insistently
    (apply-macete-locally commutative-law-for-monoids (0) " monoid%prod(c,[-1]+t,f oo phi)**f(phi(t)) ")


    )))

(def-theorem constant-function-lemma
  "forall(a,b,c:zz, f, g:[zz,ind_1], a<=b and forall(t:zz, a<=t and t<=b implies  f(t) == f(t-1)) and f(a-1)==g(c)
 implies
           f(b) == g(c))"
  (proof
   
   (

    (induction integer-inductor ())
    (prove-by-logic-and-simplification 3)
    (backchain "with(f:[zz,ind_1],t,a:zz,
  forall(t_$0:zz,
    a<=t_$0 and t_$0<=1+t implies f(t_$0)==f([-1]+t_$0)));")
    (prove-by-logic-and-simplification 3)


    ))
  (usages transportable-macete)
  (theory generic-theory-1))


(def-theorem general-commutative-law
  "forall(a,b,c,d:zz, phi:[zz,zz], f:[zz,uu],
         zz%interval(c,d) subseteq dom{phi} and
         injective_q{phi} and c<=d and
         image{phi,zz%interval(c,d)} subseteq zz%interval(a,b)
    implies
    monoid%prod(a,b,nullify%on%set(f,image{phi,zz%interval(c,d)})) **
     monoid%prod(c,d,f oo phi) 
    == monoid%prod(a,b,f))"

  (theory commutative-monoid-theory)

  (usages transportable-macete)
  lemma
  (proof 

   (

    (force-substitution "monoid%prod(a,
              b,
              nullify%on%set(f,image{phi,zz%interval(c,d)}))**
  monoid%prod(c,d,f oo phi)==monoid%prod(a,b,f)" "lambda(t:zz,monoid%prod(a,
              b,
              nullify%on%set(f,image{phi,zz%interval(c,t)}))**
  monoid%prod(c,t,f oo phi))(d)==lambda(x:zz,monoid%prod(a,x,f))(b)" (0))
    (apply-macete-with-minor-premises tr%constant-function-lemma)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("c"))
    (cut-with-single-formula "phi(t_$1) in zz%interval(a,b)")
    (apply-macete commutative-law-stack-lemma)
    (incorporate-antecedent "with(b,a:zz,phi:[zz,zz],d,c:zz,
  image{phi,zz%interval(c,d)} subseteq zz%interval(a,b));")
    (incorporate-antecedent "with(phi:[zz,zz],d,c:zz,zz%interval(c,d) subseteq dom{phi});")
    unfold-defined-constants
    direct-and-antecedent-inference-strategy
    (backchain "with(b,a:zz,phi:[zz,zz],d,c:zz,
  image{phi,indic{k:zz,  c<=k and k<=d}}
   subseteq indic{k:zz,  a<=k and k<=b});")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-with-minor-premises
    beta-reduce-repeatedly
    (instantiate-existential ("t_$1"))
    (incorporate-antecedent "with(phi:[zz,zz],d,c:zz,
  indic{k:zz,  c<=k and k<=d} subseteq dom{phi});")
    (weaken (0 3))
    simplify-insistently
    (weaken (0 4))
    (incorporate-antecedent "with(phi:[zz,zz],d,c:zz,
  indic{k:zz,  c<=k and k<=d} subseteq dom{phi});")
    (apply-macete monoid-null-prod)
    simplify
    (apply-macete-with-minor-premises locality-for-monoid-prod)
    direct-and-antecedent-inference-strategy
    (weaken (6 5 4 3 2 1 0))
    unfold-defined-constants
    simplify-insistently
    (unfold-single-defined-constant (0) nullify%on%set)
    beta-reduce-repeatedly


    )))




(def-theorem nullified-monoid%prod-lemma 
  "forall(a,b:zz, s:sets[zz], f:[zz,uu],
         zz%interval(a,b) subseteq s
          implies
	 monoid%prod(a,b,nullify%on%set(f,s))==e)"

  (theory monoid-theory)
  lemma
  (proof
   (

    (force-substitution "e" " monoid%prod(a, b,lambda(x:zz,e))" (0))
    (apply-macete-with-minor-premises locality-for-monoid-prod)
    beta-reduce-repeatedly
    (unfold-single-defined-constant (0) nullify%on%set)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "x in s")
    simplify
    (backchain "with(s:sets[zz],b,a:zz,zz%interval(a,b) subseteq s);")
    (unfold-single-defined-constant (0) zz%interval)
    simplify-insistently
    (unfold-single-defined-constant (0) nullify%on%set)
    (weaken (0))
    (case-split ("a<=b"))
    (induction integer-inductor ())
    (apply-macete-with-minor-premises monoid-null-prod)

    )))




(def-theorem general-commutative-law-corollary
  "forall(a,b,c,d:zz, phi:[zz,zz], f:[zz,uu],
         zz%interval(c,d) subseteq dom{phi} and
         injective_q{phi} and c<=d and
         image{phi,zz%interval(c,d)}=zz%interval(a,b)
    implies
     monoid%prod(c,d,f oo phi) == monoid%prod(a,b,f))"

  (theory commutative-monoid-theory)
  (usages transportable-macete)
  lemma
  (proof
   (

    direct-and-antecedent-inference-strategy
    (force-substitution "monoid%prod(c,d,f oo phi)" "monoid%prod(a,b,nullify%on%set(f,image{phi,zz%interval(c,d)}))**monoid%prod(c,d,f oo phi)" (0))
    (apply-macete-with-minor-premises general-commutative-law)
    (apply-macete-with-minor-premises nullified-monoid%prod-lemma)
    simplify


    )))



(def-translation commutative-monoid-theory-to-multiplicative-rr
  force-under-quick-load
  (source commutative-monoid-theory)
  (target h-o-real-arithmetic)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (uu rr))
  (constant-pairs
   (e 1)
   (** *)
   ;; (monoid%prod prod)
   )
  (theory-interpretation-check using-simplification))

(def-translation commutative-monoid-theory-to-additive-rr
   force-under-quick-load
   (source commutative-monoid-theory)
  (target h-o-real-arithmetic)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs
   (uu rr))
  (constant-pairs
   (e 0)
   (** +)
   ;; (monoid%prod sum)
   )
  (theory-interpretation-check using-simplification))

(def-renamer monoid-to-additive-rr-renamer
  (pairs 
   (nullify%on%set zero%on%set)))

(def-transported-symbols nullify%on%set
  (translation commutative-monoid-theory-to-additive-rr)
  (renamer monoid-to-additive-rr-renamer))



;;;applications:

(def-theorem sum-nonnegativity
  "forall(f:[zz,rr], a,b:zz, forall(z:zz,a<=z and z<=b implies 0<=f(z)) 
                   implies 0<=sum(a,b,f))"
  (theory h-o-real-arithmetic)
  (proof

   (
    
    direct-and-antecedent-inference-strategy
    (case-split ("a<=b"))
    (induction integer-inductor ())
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "0<=sum(a,t,f) and 0<=f(1+t)")
    simplify
    (prove-by-logic-and-simplification 3)
    (unfold-single-defined-constant (0) sum)
    simplify


    )

   ))

(def-theorem cardinality-definedness-lemma
  "forall(a,b,c,d:zz,phi:[zz,zz],
  zz%interval(c,d) subseteq dom{phi}
   and 
  injective_q{phi}
   and 
  c<=d
   and 
  image{phi,zz%interval(c,d)} subseteq zz%interval(a,b)
   implies 
  d-c<=b-a)"

  (theory h-o-real-arithmetic)

  (proof

   (
    direct-and-antecedent-inference-strategy
    (force-substitution "d-c<=b-a" "(d+1)-c<=(b+1)-a" (0))
    (force-substitution "(b+1)-a" "sum(a,b,zero%on%set(lambda(x:zz,1),
      image{phi,zz%interval(c,d)}))+sum(c,d,lambda(x:zz,1) oo phi)" (0))
    (cut-with-single-formula "(d+1)-c=sum(c,d,lambda(x:zz,1) oo phi) 
and 0<=sum(a, b, zero%on%set(lambda(x:zz,1), image{phi,zz%interval(c,d)}))")
    simplify
    direct-and-antecedent-inference-strategy
    (weaken (0 2))
    (induction integer-inductor ())
    simplify-insistently
    direct-and-antecedent-inference-strategy
    beta-reduce-with-minor-premises
    (backchain "with(phi:[zz,zz],c:zz,
  forall(x_$2:zz,c<=x_$2 and x_$2<=c implies #(phi(x_$2))));")
    simplify
    (backchain "with(phi:[zz,zz],t,c:zz,
  zz%interval(c,t) subseteq dom{phi}
   implies 
  1+t=c+sum(c,t,lambda(x:zz,1) oo phi));")
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-transitivity)
    (instantiate-existential ("zz%interval(c,1+t)"))
    unfold-defined-constants
    simplify-insistently
    (unfold-single-defined-constant (0) zz%interval)
    (unfold-single-defined-constant (0) zz%interval)
    (backchain-backwards "with(phi:[zz,zz],t,c:zz,
  zz%interval(c,t) subseteq dom{phi}
   implies 
  1+t=c+sum(c,t,lambda(x:zz,1) oo phi));")
    beta-reduce-with-minor-premises
    (antecedent-inference "with(phi:[zz,zz],t,c:zz,
  zz%interval(c,t) subseteq dom{phi}
   implies 
  1+t=c+sum(c,t,lambda(x:zz,1) oo phi));")
    simplify
    (incorporate-antecedent "with(phi:[zz,zz],t,c:zz,
  zz%interval(c,1+t) subseteq dom{phi});")
    (unfold-single-defined-constant (0) zz%interval)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(phi:[zz,zz],t,c:zz,
  forall(x_$0:zz,
    c<=x_$0 and x_$0<=1+t implies #(phi(x_$0))));")
    simplify
    (apply-macete-with-minor-premises sum-nonnegativity)
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) zero%on%set)
    (raise-conditional (0))
    direct-inference
    simplify
    simplify
    (unfold-single-defined-constant (0) zero%on%set)
    (apply-macete-with-minor-premises tr%general-commutative-law)
    (cut-with-single-formula "a<=b")
    (weaken (1 2 3 4))
    (induction integer-inductor ())
    (cut-with-single-formula "phi(c) in zz%interval(a,b)")
    (incorporate-antecedent "with(c:zz,phi:[zz,zz],b,a:zz,phi(c) in zz%interval(a,b));")
    (unfold-single-defined-constant (0) zz%interval)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    simplify
    (backchain "with(b,a:zz,phi:[zz,zz],d,c:zz,
  image{phi,zz%interval(c,d)} subseteq zz%interval(a,b));")
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-with-minor-premises
    (instantiate-existential ("c"))
    (unfold-single-defined-constant (0) zz%interval)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    simplify
    (incorporate-antecedent "with(phi:[zz,zz],d,c:zz,zz%interval(c,d) subseteq dom{phi});")
    (unfold-single-defined-constant (0) zz%interval)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(phi:[zz,zz],d,c:zz,
  forall(x_$0:zz,c<=x_$0 and x_$0<=d implies #(phi(x_$0))));")
    simplify
    (incorporate-antecedent "with(phi:[zz,zz],d,c:zz,zz%interval(c,d) subseteq dom{phi});")
    (unfold-single-defined-constant (0) zz%interval)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(phi:[zz,zz],d,c:zz,
  forall(x_$0:zz,c<=x_$0 and x_$0<=d implies #(phi(x_$0))));")
    simplify
    simplify

    )))
