

(comment "Develop a theory that leads to the recursive definition of collinear
  closure via iterations. In particular, always get closure after omega 
 iterations. Eventually show that if you start with n points, then need at
 most n-1 iterations. This will require some form of Pasch's Postulate. ")


(def-language three-place-predicate
  (embedded-language generic-theory-1)
   (constants (Rel "[ind_1,ind_1,ind_1 -> prop]")
  ))

(def-theory three-place-predicate-theory
  (language three-place-predicate)
  (component-theories generic-theory-1)
   )

(def-constant Rel%closed
  "lambda(s:sets[ind_1],forall(x,y,z:ind_1,x in s and y in s and Rel(x,y,z)
       implies z in s))"
  (theory three-place-predicate-theory))

(def-constant Rel%closure
  "lambda(s:sets[ind_1],iota(t:sets[ind_1],Rel%closed(t) and s subseteq t and
    forall(u:sets[ind_1], Rel%closed(u) and s subseteq u
       implies t subseteq u)))"
  (theory three-place-predicate-theory))

;; Has to be modified slightly!!

(def-theorem iota-free-characterization-of-Rel%closure
  "forall(s,t:sets[ind_1],Rel%closure(s)=t iff (s subseteq t and
     Rel%closed(t) and
    forall(u:sets[ind_1],s subseteq u and Rel%closed(u)
       implies t subseteq u)))"
  (theory three-place-predicate-theory)
  (proof
   (


    (unfold-single-defined-constant (0) rel%closure)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
     (contrapose "with(p:prop,p);")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     (contrapose "with(p:prop,p);"))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
     (contrapose "with(t,f:sets[ind_1],f=t);")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     (contrapose "with(p:prop,not(p));"))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2 0 0 0)")
     (contrapose "with(t,f:sets[ind_1],f=t);")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     (contrapose "with(p:prop,forsome(x:ind_1,p));")
     (antecedent-inference "with(p:prop,p and p);")
     simplify)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     direct-and-antecedent-inference-strategy
     simplify
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0 0 0)")
      (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
      direct-and-antecedent-inference-strategy
      simplify
      simplify)))))
  
(def-constant span
  "lambda(s:sets[ind_1],indic{y:ind_1, y in s or forsome(a,b:ind_1, a in s 
   and b in s and Rel(a,b,y))})"
  (theory three-place-predicate-theory)
  )

(include-files
 (files (imps theories/generic-theories/iterate)))

(def-translation iterate->three-place-predicate
  force-under-quick-load
  (source generic-theory-1)
  (target three-place-predicate-theory)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 "sets[ind_1]")))

; The recursively defined constant "iterate" is transported to the
; theory pre-csp-theory.

(def-renamer iterate-renamer
  (pairs (iterate span%iterate)))

(def-transported-symbols iterate
  (renamer iterate-renamer)
  (translation iterate->three-place-predicate))

(def-overloading iterate
  (generic-theory-1 iterate) (three-place-predicate-theory span%iterate))

(def-theorem span-definedness
  "total_q{span,[sets[ind_1],sets[ind_1]]}"
  (theory three-place-predicate-theory)
  (usages d-r-convergence)  
  (proof
   (
    

    (unfold-single-defined-constant-globally span)
    simplify
    insistent-direct-inference
    beta-reduce-repeatedly
    )))


(def-theorem span-includes-set
  "forall(s:sets[ind_1], s subseteq span(s))"
  (theory three-place-predicate-theory)
  (proof
   (

    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally span)
    simplify

    )))

(def-theorem monotonicity-of-span
  "forall(s,t:sets[ind_1], s subseteq t implies span(s) subseteq span(t))"
  (theory three-place-predicate-theory)
  (proof
   (

   
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally span)
    insistent-direct-inference
    simplify
    direct-and-antecedent-inference-strategy
    (simplify-antecedent "with(p:prop,not(p));")
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0)")
     (instantiate-existential ("b" "a"))
     simplify
     simplify)

    )))



(def-theorem Rel%closed-iff-fixed-under-span
  "forall(s:sets[ind_1],Rel%closed(s) iff span(s)=s)"
  (theory three-place-predicate-theory)
  (proof
   ( 
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (apply-macete-with-minor-premises span-includes-set)
    unfold-defined-constants
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy'")
     (backchain "with(p:prop,forall(z:ind_1,p));")
     auto-instantiate-existential)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy'")
     (backchain "with(p:prop,forall(x:ind_1,p));")
     direct-and-antecedent-inference-strategy
     auto-instantiate-existential)
    )))



;;  This is unnecessary:

(comment
 (def-theorem monotonicity-of-iterate
  "forall(s:sets[ind_1],n:zz,0<=n implies iterate(span,s)(n) subseteq
 iterate(span,s)(n+1))" 
  (theory three-place-predicate-theory)
  (usages transportable-macete)
  (proof
   (


    (unfold-single-defined-constant (1) span%iterate)
    simplify
    (apply-macete-with-minor-premises span-includes-set)
    (apply-macete-with-minor-premises tr%iterate-definedness)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises span-definedness)

    ))

  ))


(def-theorem strong-monotonicity-of-iterate
  "forall(s:sets[ind_1],n,m:zz, 0<=n and n<=m implies
        iterate(span,s)(n) subseteq iterate(span,s)(m))"
  (theory three-place-predicate-theory)
  (proof
   (


    (induction trivial-integer-inductor ("m"))
    simplify
    (block 
     (script-comment "`induction' at (0 0 0 0 0 0 0 1 0 0 0 0 0 0 0)")
     (apply-macete-with-minor-premises tr%subseteq-transitivity)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (antecedent-inference "with(p:prop,p implies p);")
      (instantiate-existential ("iterate(span,s)(t)"))
      (apply-macete-with-minor-premises span-includes-set)
      (apply-macete-with-minor-premises tr%iterate-definedness)
      simplify-insistently)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises tr%iterate-definedness)
      simplify-insistently)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (2)")
      (apply-macete-with-minor-premises tr%iterate-definedness)
      simplify-insistently))
    )))

(def-constant union%of%iterates
  "lambda(s:sets[ind_1],big_u{lambda(n:zz,iterate(span,s)(n))})"
  (theory three-place-predicate-theory))


(def-theorem span-invariance 
  "forall( s:sets[ind_1],  
           (span(s) subseteq s)
               iff 
           forall(x,y,z:ind_1, x in s and y in s and 
                               Rel(x,y,z) implies z in s))"
  (theory three-place-predicate-theory)
  (proof
   (
    

    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0)")
     (incorporate-antecedent "with(s,f:sets[ind_1],f subseteq s);")
     (unfold-single-defined-constant (0) span)
     insistent-direct-inference
     (backchain "with(s,f:sets[ind_1],f subseteq s);")
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     direct-and-antecedent-inference-strategy
     auto-instantiate-existential)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
     (unfold-single-defined-constant (0) span)
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (backchain "with(p:prop,forall(x,y,z:ind_1,p));")
     auto-instantiate-existential)

    )))


(def-theorem union%of%iterates-closed-under-span
  "forall(s:sets[ind_1],span(union%of%iterates(s))=union%of%iterates(s))"
  (theory three-place-predicate-theory)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    (move-to-sibling 1)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
     (apply-macete-with-minor-premises span-includes-set)
     (unfold-single-defined-constant (0) union%of%iterates))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
     (apply-macete-with-minor-premises span-invariance)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (unfold-single-defined-constant-globally union%of%iterates)
      (apply-macete-with-minor-premises tr%big-union-member)
      beta-reduce-repeatedly
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula "0<=i and 0<=i_$0")
      (move-to-sibling 1)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (cut-with-single-formula "#(iterate(span,s)(i)) and #( iterate(span,s)(i_$0))")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,p and p);")
	direct-and-antecedent-inference-strategy
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	 (contrapose "with(i:zz,s:sets[ind_1],#(iterate(span,s)(i)));")
	 (apply-macete-with-minor-premises tr%undefined-for-negative)
	 simplify)
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	 (contrapose "with(i_$0:zz,s:sets[ind_1],#(iterate(span,s)(i_$0)));")
	 (apply-macete-with-minor-premises tr%undefined-for-negative)
	 simplify))
       simplify)
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (cut-with-single-formula "0<=max(i,i_$0)")
       (move-to-sibling 1)
       simplify
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(instantiate-existential ("1+max(i,i_$0)"))
	(unfold-single-defined-constant (0) span%iterate)
	simplify
	(unfold-single-defined-constant (0) span)
	simplify
	beta-reduce-with-minor-premises
	(block 
	 (script-comment "`beta-reduce-with-minor-premises' at (0)")
	 (apply-macete-with-minor-premises indicator-facts-macete)
	 beta-reduce
	 direct-and-antecedent-inference-strategy
	 auto-instantiate-existential
	 (block 
	  (script-comment "`auto-instantiate-existential' at (0 0)")
	  (cut-with-single-formula "iterate(span,s)(i_$0) subseteq iterate(span,s)(max(i,i_$0))")
	  (block 
	   (script-comment "`cut-with-single-formula' at (0)")
	   (cut-with-single-formula "i_$0<=max(i,i_$0)")
	   (move-to-sibling 1)
	   simplify
	   (backchain "with(f:sets[ind_1],f subseteq f);"))
	  (block 
	   (script-comment "`cut-with-single-formula' at (1)")
	   (apply-macete-with-minor-premises strong-monotonicity-of-iterate)
	   simplify))
	 (block 
	  (script-comment "`auto-instantiate-existential' at (0 1)")
	  (cut-with-single-formula "iterate(span,s)(i) subseteq iterate(span,s)(max(i,i_$0))")
	  (block 
	   (script-comment "`cut-with-single-formula' at (0)")
	   (cut-with-single-formula "i<=max(i,i_$0)")
	   (move-to-sibling 1)
	   simplify
	   (backchain "with(f:sets[ind_1],f subseteq f);"))
	  (block 
	   (script-comment "`cut-with-single-formula' at (1)")
	   (apply-macete-with-minor-premises strong-monotonicity-of-iterate)
	   simplify)))
	(block 
	 (script-comment "`beta-reduce-with-minor-premises' at (1)")
	 (apply-macete-with-minor-premises tr%iterate-definedness)
	 simplify-insistently))))
     (unfold-single-defined-constant (0) union%of%iterates))

    )))

(def-theorem union%of%iterates-includes-s
  "forall(s:sets[ind_1],s subseteq union%of%iterates(s))"
  (theory three-place-predicate-theory)
  (proof
   (
    unfold-defined-constants
    insistent-direct-inference-strategy
    (apply-macete-with-minor-premises tr%big-union-member)
    (instantiate-existential ("0"))
    beta-reduce-insistently
    (unfold-single-defined-constant (0) span%iterate)

    )))

(def-theorem union%of%iterates-is-Rel%closure
  "forall(s:sets[ind_1],Rel%closure(s)=union%of%iterates(s))"
  (theory three-place-predicate-theory)
  (proof
   (

    (apply-macete-with-minor-premises iota-free-characterization-of-rel%closure)
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises union%of%iterates-includes-s)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
     (apply-macete-with-minor-premises rel%closed-iff-fixed-under-span)
     (apply-macete-with-minor-premises union%of%iterates-closed-under-span)
     simplify
     (unfold-single-defined-constant (0) union%of%iterates))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy'")
     (unfold-single-defined-constant (0) union%of%iterates)
     insistent-direct-inference
     (apply-macete-with-minor-premises tr%big-union-member)
     beta-reduce
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "forall(i:zz,0<=i implies iterate(span,s)(i) subseteq u)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (cut-with-single-formula "0<=i")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
      (backchain "with(p:prop,forall(i:zz,p));")
       auto-instantiate-existential)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (cut-with-single-formula "#(iterate(span,s)(i))")
       (contrapose "with(f:sets[ind_1],#(f));")
       (apply-macete-with-minor-premises tr%undefined-for-negative)
       simplify))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (induction trivial-integer-inductor ("i"))
      (block 
       (script-comment "`induction' at (0 0)")
       beta-reduce
       (unfold-single-defined-constant (0) span%iterate))
      (block 
       (script-comment "`induction' at (0 1 0 0 0 0 0 0)")
       (incorporate-antecedent "with(u:sets[ind_1],rel%closed(u));")
       (apply-macete-with-minor-premises rel%closed-iff-fixed-under-span)
       direct-and-antecedent-inference-strategy
       (backchain-backwards "with(u,f:sets[ind_1],f=u);")
       (apply-macete-with-minor-premises monotonicity-of-span)
       (apply-macete-with-minor-premises tr%iterate-definedness)
       simplify-insistently)))



    )))


(def-theorem Rel%closure-exists
  "forall(s:sets[ind_1],#(Rel%closure(s)))"
  (theory three-place-predicate-theory)
  (usages transportable-macete)
  (proof
   (
    insistent-direct-inference
    (apply-macete-with-minor-premises union%of%iterates-is-rel%closure)
    (unfold-single-defined-constant (0) union%of%iterates)
    )))