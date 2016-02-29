(include-files
 (files (imps theories/generic-theories/iterate-supplements)))

(def-constant flow%ext
  "lambda(f:[ind_1->ind_1], g:[ind_1->ind_2],x :ind_1, 
         g(first%entry(f,dom{g},x)))"
  (theory generic-theory-2))

(def-theorem flow%ext-definedness
  "forall(f:[ind_1 -> ind_1],g:[ind_1 -> ind_2], x:ind_1,
  #(flow%ext(f,g,x)) iff forsome(n:zz, #(g(iterate(f,x)(n)))))"
  (theory generic-theory-2)
  (proof
   (


    (unfold-single-defined-constant (0) flow%ext)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
     (cut-with-single-formula "#(first%entry(f,dom{g},x))")
     (incorporate-antecedent "with(i:ind_1,#(i));")
     (apply-macete-with-minor-premises first%entry-definedness)
     (apply-macete-with-minor-premises indicator-facts-macete)
     simplify)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
     (cut-with-single-formula "#(first%entry(f,dom{g},x))")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (cut-with-single-formula "forsome(y:ind_1,first%entry(f,dom{g},x)=y) ")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,forsome(y:ind_1,p));")
       (backchain "with(y,i:ind_1,i=y);")
       (incorporate-antecedent "with(y,i:ind_1,i=y);")
       (apply-macete-with-minor-premises first%entry-characterization)
       simplify)
      (instantiate-existential ("first%entry(f,dom{g},x)")))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises first%entry-definedness)
      (apply-macete-with-minor-premises indicator-facts-macete)
      simplify
      auto-instantiate-existential))

    )))


(def-theorem flow%ext-minimality-lemma
  "forall(g:[ind_1 -> ind_2], f:[ind_1,ind_1], h :[ind_1->ind_2], 
     forall(x:ind_1, g(x)==if(#(h(x)), h(x), g(f(x))))
      implies
     forall(x:ind_1,
         #(flow%ext(f,h,x)) implies flow%ext(f,h,x)=g(x)))"

  (theory generic-theory-2)
  lemma
  (proof

   (

    (unfold-single-defined-constant-globally flow%ext)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(p:ind_1, first%entry(f,dom{h},x)=p)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,forsome(p:ind_1,with(p:prop,p)));")
     (backchain "with(p,i:ind_1,i=p);")
     (incorporate-antecedent "with(p,i:ind_1,i=p);")
     (apply-macete-with-minor-premises first%entry-characterization)
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "0<=n")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (cut-with-single-formula "#(iterate(f,x)(n))")
      (contrapose "with(i:ind_1,#(i));")
      (apply-macete-with-minor-premises undefined-for-negative)
      simplify)
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (cut-with-single-formula "forall(n:zz, 0<=n implies forall(p,x:ind_1, p in dom{h} and iterate(f,x)(n)=p and forall(m:zz,m<n implies not(iterate(f,x)(m) in dom{h})) implies h(p)=g(x)))")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (backchain "with(p:prop,
  forall(n:zz,
    0<=n implies forall(p,x:ind_1,with(p:prop,p))));")
       auto-instantiate-existential)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (weaken (0 1 2 3 4))
       (induction trivial-integer-inductor ("n"))
       (block 
	(script-comment "`induction' at (0 0)")
	beta-reduce-repeatedly
	(unfold-single-defined-constant (0) iterate)
	simplify)
       (block 
	(script-comment "`induction' at (0 1 0 0 0 0 0 0 0 0 0)")
	(instantiate-universal-antecedent "with(p:prop,forall(p,x:ind_1,with(p:prop,p)));"
					  ("p" "f(x)"))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 0 1)")
	 (contrapose "with(p:prop,not(p));")
	 (apply-macete-with-minor-premises rev%iterate-front-back-lemma))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 0 2 0 0)")
	 (contrapose "with(i:ind_1,f:sets[ind_1],i in f);")
	 (apply-macete-with-minor-premises rev%iterate-front-back-lemma)
	 (contrapose "with(p:prop,forall(m:zz,p));")
	 (unfold-single-defined-constant (0) iterate)
	 (instantiate-existential ("m_$0+1"))
	 simplify
	 (block 
	  (script-comment "`instantiate-existential' at (0 1)")
	  (cut-with-single-formula "0<=m_$0")
	  simplify
	  (block 
	   (script-comment "`cut-with-single-formula' at (1)")
	   (cut-with-single-formula "#(iterate(f,x)(m_$0))")
	   (contrapose "with(i:ind_1,#(i));")
	   (apply-macete-with-minor-premises undefined-for-negative)
	   simplify)))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	 (backchain "with(p:prop,forall(x:ind_1,p));")
	 simplify
	 (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
                                                                 
					   ("0"))
	 (simplify-antecedent "with(p:prop,not(p));")
	 (block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	  (contrapose "with(p:prop,not(p));")
	  (unfold-single-defined-constant (0)
                                                                 
					  iterate)
	  simplify
	  (contrapose "with(p:prop,not(p));")
	  simplify))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (1 2 0)")
	 (cut-with-single-formula "#(iterate(f,x)(1))")
	 (block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (incorporate-antecedent "with(i:ind_1,#(i));")
	  (unfold-single-defined-constant (0)
                                                                 
					  iterate)
	  simplify
	  (unfold-single-defined-constant (0)
                                                                 
					  iterate))
	 (block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises iterate-definedness-refinement)
	  (instantiate-existential ("t+1"))
	  simplify
	  simplify
	  (block 
	   (script-comment "`instantiate-existential' at (0 2)")
	   (unfold-single-defined-constant (0)
                                                                 
					   iterate)
	   simplify)))))))
    (instantiate-existential ("first%entry(f,dom{h},x)"))

    )))

(def-theorem flow%ext-minimality
  "forall(g:[ind_1 -> ind_2], f:[ind_1,ind_1], h :[ind_1->ind_2], 
     forall(x:ind_1, g(x)==if(#(h(x)), h(x), g(f(x))))
      implies
     forall(x:ind_1,
         #(flow%ext(f,h,x)) implies flow%ext(f,h,x)==g(x)))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    insistent-direct-inference
    (apply-macete-with-minor-premises flow%ext-minimality-lemma)
    direct-and-antecedent-inference-strategy

    )))

(def-theorem first%entry-iteration
  "forall(f:[ind_1,ind_1],x:ind_1, a,s :sets[ind_1], 
     first%entry(f,indic{x:ind_1, #(first%entry(f,s,x))},x)==
     if(#(first%entry(f,s,x)), x, ?ind_1))"
  (theory generic-theory-1)
  lemma
  (proof
   (

    direct-and-antecedent-inference-strategy
    (raise-conditional (0))
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
     (apply-macete-with-minor-premises first%entry-equation)
     simplify)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0)")
     (apply-macete-with-minor-premises first%entry-equation)
     simplify)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
     (contrapose "with(p:prop,not(p));")
     (weaken (0))
     (incorporate-antecedent "with(p:prop,p);")
     (apply-macete-with-minor-premises first%entry-definedness)
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "#(iterate(f,x)(n))")
     (incorporate-antecedent "with(i:ind_1,s:sets[ind_1],f:[ind_1,ind_1],
  #(first%entry(f,s,i)));")
     (apply-macete-with-minor-premises first%entry-definedness)
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "0<=n and 0<=n_$0")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(i:ind_1,s:sets[ind_1],i in s);")
      (apply-macete-with-minor-premises iterate-additivity)
      direct-and-antecedent-inference-strategy
      (instantiate-existential ("n+n_$0")))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (cut-with-single-formula "#(iterate(f,x)(n)) and #(iterate(f,iterate(f,x)(n))(n_$0))")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,p and p);")
       direct-inference
       (block 
	(script-comment "`direct-inference' at (0)")
	(contrapose "with(n:zz,x:ind_1,f:[ind_1,ind_1],#(iterate(f,x)(n)));")
	(apply-macete-with-minor-premises undefined-for-negative)
	simplify)
       (block 
	(script-comment "`direct-inference' at (1)")
	(contrapose "with(n_$0,n:zz,
  #(iterate(with(f:[ind_1,ind_1],f),with(f:[zz,ind_1],f(n)))
     (n_$0)));")
	(apply-macete-with-minor-premises undefined-for-negative)
	simplify))
      simplify))

    )))

(def-theorem domain-of-flow%ext-lemma
  "forall(f:[ind_1->ind_1], g:[ind_1->ind_2],x :ind_1,
     dom{lambda(x:ind_1, flow%ext(f,g,x))}=
     indic{x:ind_1, #(first%entry(f,dom{g},x))})"
  (theory generic-theory-2)
  lemma
  (proof
   (


    (unfold-single-defined-constant (0) flow%ext)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    simplify-insistently
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
     insistent-direct-inference
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "forsome(y:ind_1, first%entry(f,dom{g},x_$1)=y)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(y:ind_1,p));")
      (backchain "with(y,i:ind_1,i=y);")
      (incorporate-antecedent "with(y,i:ind_1,i=y);")
      (apply-macete-with-minor-premises first%entry-characterization)
      simplify)
     (instantiate-existential ("first%entry(f,dom{g},x_$1)")))

    )))

(def-theorem flow%ext-idempotency
  "forall(f:[ind_1->ind_1], g:[ind_1->ind_2], x:ind_1, 
        flow%ext(f,lambda(x:ind_1, flow%ext(f,g,x)),x)==
        flow%ext(f,g,x))"
  (theory generic-theory-2)
  lemma
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) flow%ext)
    (apply-macete-with-minor-premises domain-of-flow%ext-lemma)
    (apply-macete-with-minor-premises first%entry-iteration)
    (unfold-single-defined-constant-globally flow%ext)
    (case-split ("#(first%entry(f,dom{g},x))"))
    simplify
    simplify
    )))

(def-theorem locality-of-flow%ext
  "forall(f:[ind_1,ind_1],g:[ind_1->ind_2], x:ind_1, a,s :sets[ind_1], 
     forall(m:ind_1, m in a and #(f(m)) implies f(m) in a)
      and
     x in a
      implies
     flow%ext(f,g,x)==flow%ext(restrict{f,a},restrict{g,a},x))"
  (theory generic-theory-2)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally flow%ext)
    (cut-with-single-formula "first%entry(f,dom{g},x)==first%entry(restrict{f,a},dom{restrict{g,a}},x)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (backchain-backwards "with(i:ind_1,i==i);")
     simplify
     (case-split ("#(first%entry(f,dom{g},x))"))
     (block 
      (script-comment "`case-split' at (1)")
      simplify
      direct-and-antecedent-inference-strategy
      (contrapose "with(p:prop,not(p));")
      (cut-with-single-formula "forsome(u:ind_1, first%entry(f,dom{g},x)=u)")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,forsome(u:ind_1,p));")
       (backchain "with(u,i:ind_1,i=u);")
       (incorporate-antecedent "with(u,i:ind_1,i=u);")
       (apply-macete-with-minor-premises first%entry-characterization)
       direct-and-antecedent-inference-strategy
       (backchain-backwards "with(u,i:ind_1,i=u);")
       (apply-macete-with-minor-premises iterate-invariance)
       direct-and-antecedent-inference-strategy
       (cut-with-single-formula "#(iterate(f,x)(n))")
       (contrapose "with(n:zz,f:[zz,ind_1],#(f(n)));")
       (apply-macete-with-minor-premises undefined-for-negative)
       simplify)
      (instantiate-existential ("first%entry(f,dom{g},x)")))
     simplify)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises first%entry-locality)
     (cut-with-single-formula "dom{restrict{g,a}}=dom{g} inters a")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
      simplify-insistently)
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (backchain "with(f:sets[ind_1],f=f);")
      (apply-macete-with-minor-premises first%entry-restriction-lemma)))



    )))

(def-theorem locality-of-flow%ext-corollary
  "forall(f,f_1:[ind_1,ind_1],g,g_1:[ind_1->ind_2], x:ind_1, a,s :sets[ind_1], 
     forall(m:ind_1, m in a and #(f(m)) implies f(m) in a) 
      and
     forall(m:ind_1, m in a implies f(m)==f_1(m) and g(m)==g_1(m))
      and
     x in a
      implies
     flow%ext(f,g,x)==flow%ext(f_1,g_1,x))"
  (theory generic-theory-2)
  lemma
  (proof
   (
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "flow%ext(f,g,x)==flow%ext(restrict{f,a},restrict{g,a},x)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises locality-of-flow%ext)
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (cut-with-single-formula "flow%ext(f_1,g_1,x)==flow%ext(restrict{f_1,a},restrict{g_1,a},x)")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises locality-of-flow%ext)
      insistent-direct-inference
      direct-and-antecedent-inference-strategy
      (incorporate-antecedent "with(i:ind_1,#(i));")
      (backchain-backwards "with(p:prop,a:sets[ind_1],
  forall(m:ind_1,m in a implies p and p));")
      (backchain-backwards "with(p:prop,a:sets[ind_1],
  forall(m:ind_1,m in a implies p and p));")
      direct-and-antecedent-inference-strategy
      (backchain "with(f:[ind_1,ind_1],a:sets[ind_1],invariant{a,f});")
      simplify)
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      simplify
      (backchain "with(a:sets[ind_1],x:ind_1,g_1:[ind_1,ind_2],f_1:[ind_1,ind_1],
  flow%ext(f_1,g_1,x)
  ==flow%ext(restrict{f_1,a},restrict{g_1,a},x));")
      (backchain "with(a:sets[ind_1],x:ind_1,g:[ind_1,ind_2],f:[ind_1,ind_1],
  flow%ext(f,g,x)
  ==flow%ext(restrict{f,a},restrict{g,a},x));")
      (cut-with-single-formula "restrict{f,a}=restrict{f_1,a} and restrict{g,a}=restrict{g_1,a} ")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       direct-and-antecedent-inference-strategy
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	extensionality
	simplify-insistently)
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	extensionality
	simplify-insistently))))
    )))


(def-theorem flow%ext-recursive-equation
  "forall(f:[ind_1->ind_1], g:[ind_1->ind_2],x :ind_1, 
     flow%ext(f,g,x)==if(#(g(x)), g(x), flow%ext(f,g,f(x))))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) flow%ext)
    (apply-macete-with-minor-premises first%entry-equation)
    (unfold-single-defined-constant (0) flow%ext)
    (case-split ("#(g(x))"))
    simplify
    simplify

    )))

(def-theorem flow%ext-restriction-lemma
  "forall(f:[ind_1->ind_1], g:[ind_1->ind_2],x :ind_1, 
     flow%ext(f,g,x)==flow%ext(restrict{f,dom{g}^^},g,x))"
  (theory generic-theory-2)
  lemma
  (proof
   (

    (unfold-single-defined-constant-globally flow%ext)
    (apply-macete-with-minor-premises rev%first%entry-restriction-lemma-2)

    )))


(def-theorem flow%ext-restricted-invariance
  "forall(f:[ind_1->ind_1], g:[ind_1->ind_2], 
        invariant{dom{lambda(x:ind_1, flow%ext(f,g,x))}, 
                  restrict{f, dom{g}^^}})"
  (theory generic-theory-2)
  lemma
  (proof
   (


    direct-and-antecedent-inference-strategy
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (contrapose "with(i:ind_2,#(i));")
    (apply-macete-with-minor-premises flow%ext-recursive-equation)
    simplify

    )))

(def-theorem flow%ext-complement-invariance
  "forall(f:[ind_1->ind_1], g:[ind_1->ind_2], 
        invariant{dom{lambda(x:ind_1, flow%ext(f,g,x))}^^, f})"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (



    direct-and-antecedent-inference-strategy
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
     (contrapose "with(p:prop,not(p));")
     (apply-macete-with-minor-premises flow%ext-recursive-equation)
     simplify)
    )))


(def-theorem strong-locality-of-flow%ext
  "forall(f,f_1:[ind_1,ind_1],g,g_1:[ind_1->ind_2], x:ind_1, a,s :sets[ind_1], 
     invariant{a, restrict{f, dom{g}^^}}
      and
     forall(m:ind_1, m in a implies f(m)==f_1(m) and g(m)==g_1(m))
      and
     x in a
      implies
     flow%ext(f,g,x)==flow%ext(f_1,g_1,x))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (


    (apply-macete-with-minor-premises flow%ext-restriction-lemma)
    (apply-macete-with-minor-premises locality-of-flow%ext-corollary)
    direct-and-antecedent-inference-strategy
    auto-instantiate-existential
    (block 
     (script-comment "`auto-instantiate-existential' at (0 1 0 0 0)")
     simplify
     direct-and-antecedent-inference-strategy
     (simplify-antecedent "with(p:prop,not(p));")
     (simplify-antecedent "with(p:prop,not(not(p)));"))
    simplify
    )))


(def-theorem strong-locality-of-flow%ext-corollary
  "forall(f,f_1:[ind_1,ind_1],g,g_1:[ind_1->ind_2], x:ind_1, a,s :sets[ind_1], 
     forall(m:ind_1, #(flow%ext(f,g,m)) implies f(m)==f_1(m) and g(m)==g_1(m))
      and
     #(flow%ext(f,g,x))
      implies
     flow%ext(f,g,x)==flow%ext(f_1,g_1,x))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises strong-locality-of-flow%ext)
    (instantiate-existential ("dom{lambda(x:ind_1, flow%ext(f,g,x))}"))
    (apply-macete-with-minor-premises flow%ext-restricted-invariance)
    (block 
     (script-comment "`instantiate-existential' at (0 1 0 0 0)")
     (backchain "with(p:prop,i:ind_2,forall(m:ind_1,#(i) implies p and p));")
     (simplify-antecedent "with(m_$1:ind_1,f:sets[ind_1],m_$1 in f);"))
    (backchain "with(p:prop,i:ind_2,forall(m:ind_1,#(i) implies p and p));")
    simplify

    )))


;(def-theorem flow%ext-extension-lemma-1
;  "forall(f,f_1:[ind_1,ind_1],g:[ind_1,ind_2],x:ind_1,
;     forall(x:ind_1,#(flow%ext(f,g,x)) implies f(x)==f_1(x)) and #(flow%ext(f,g,x))
;       implies 
;     flow%ext(f_1,lambda(x:ind_1,flow%ext(f,g,x)),x)==flow%ext(f_1,g,x))"
;  (theory generic-theory-2)
;  (proof
;   (
;    direct-and-antecedent-inference-strategy
;    (force-substitution "flow%ext(f_1,g,x)"
;			"flow%ext(f_1,lambda(x:ind_1,flow%ext(f_1,g,x)),x)"
;			(0))
;    (move-to-sibling 1)
;    (apply-macete-with-minor-premises flow%ext-idempotency)
;    (block 
;     (script-comment "`force-substitution' at (0)")
;     (apply-macete-with-minor-premises strong-locality-of-flow%ext)
;     simplify
;     (instantiate-existential ("indic{x:ind_1, #(flow%ext(f,g,x))}"))
;     simplify-insistently
;     (block 
;      (script-comment "`instantiate-existential' at (0 1 0 0)")
;      (apply-macete-with-minor-premises strong-locality-of-flow%ext-corollary)
;      direct-and-antecedent-inference-strategy
;      (simplify-antecedent "with(m_$1:ind_1,f:sets[ind_1],m_$1 in f);"))
;     simplify))))


(def-theorem flow%ext-extension-theorem-1
  "forall(f,f_1:[ind_1,ind_1],g:[ind_1,ind_2],x:ind_1, n:zz,
   forall(x:ind_1,#(flow%ext(f,g,x)) implies f(x)==f_1(x)) 
    and 
   #(flow%ext(f,g,iterate(f_1,x)(n)))
      and  
   forall(k:zz, k<n implies not(#(g(iterate(f_1,x)(k)))))
      implies 
   flow%ext(f_1,g,x)==flow%ext(f,g,iterate(f_1,x)(n)))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (
  

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "flow%ext(f,g,iterate(f_1,x)(n))==flow%ext(f_1,g,iterate(f_1,x)(n))")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises strong-locality-of-flow%ext-corollary)
     direct-and-antecedent-inference-strategy)
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (backchain "with(i:ind_2,i==i);")
     (unfold-single-defined-constant-globally flow%ext)
     (cut-with-single-formula "first%entry(f_1,dom{g},x)==first%entry(f_1,dom{g},iterate(f_1,x)(n))")
     simplify
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (incorporate-antecedent "with(i:ind_2,#(i));")
      (backchain "with(i:ind_2,i==i);")
      (unfold-single-defined-constant (0) flow%ext)
      direct-and-antecedent-inference-strategy
      simplify
      (cut-with-single-formula "forsome(y:ind_1, first%entry(f_1,dom{g},iterate(f_1,x)(n))=y)")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,forsome(y:ind_1,p));")
       (backchain "with(y,i:ind_1,i=y);")
       (incorporate-antecedent "with(y,i:ind_1,i=y);")
       (apply-macete-with-minor-premises first%entry-characterization)
       simplify
       (apply-macete-with-minor-premises indicator-facts-macete)
       beta-reduce-repeatedly
       direct-and-antecedent-inference-strategy
       (cut-with-single-formula "0<=n and 0<=n_$0")
       (move-to-sibling 1)
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(cut-with-single-formula "#(iterate(f_1,x)(n)) and #(iterate(f_1,iterate(f_1,x)(n))(n_$0))")
	(block 
	 (script-comment "`cut-with-single-formula' at (0)")
	 (antecedent-inference "with(p:prop,p and p);")
	 direct-and-antecedent-inference-strategy
	 (block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	  (contrapose "with(n_$0,n:zz,f:[zz,ind_1],f_1:[ind_1,ind_1],
  #(iterate(f_1,f(n))(n_$0)));")
	  (contrapose "with(i:ind_1,#(i));")
	  (apply-macete-with-minor-premises undefined-for-negative)
	  simplify)
	 (block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	  (contrapose "with(n_$0,n:zz,f:[zz,ind_1],f_1:[ind_1,ind_1],
  #(iterate(f_1,f(n))(n_$0)));")
	  (apply-macete-with-minor-premises undefined-for-negative)
	  simplify))
	simplify)
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(incorporate-antecedent "with(y,i:ind_1,i=y);")
	(apply-macete-with-minor-premises iterate-additivity)
	direct-and-antecedent-inference-strategy
	(instantiate-existential ("n+n_$0"))
	(case-split ("n<=m_$0"))
	(block 
	 (script-comment "`case-split' at (1)")
	 (instantiate-universal-antecedent "with(n:zz,f:[zz,ind_1],f_1:[ind_1,ind_1],g:[ind_1,ind_2],n_$0:zz,
  forall(m_$0:zz,
    m_$0<n_$0 implies not(#(g(iterate(f_1,f(n))(m_$0))))));"
                                                                 
					   ("m_$0-n"))
	 (simplify-antecedent "with(p:prop,not(p));")
	 (block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1)")
	  (incorporate-antecedent "with(p:prop,not(p));")
	  (apply-macete-with-minor-premises iterate-additivity)
	  simplify))
	simplify))
      (instantiate-existential (" first%entry(f_1,dom{g},iterate(f_1,x)(n))"))))


    )))


(def-theorem flow%ext-extension-theorem-2
  "forall(f,f_1:[ind_1,ind_1],g:[ind_1,ind_2],x:ind_1,
     forall(k:zz, not #(flow%ext(f,g,iterate(f_1,x)(k))))
         implies 
     not(#(flow%ext(f_1,g,x))))"
  (theory generic-theory-2)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises flow%ext-definedness)
    (contrapose "with(p:prop,forall(k:zz,p));")
    (antecedent-inference "with(p:prop,forsome(n:zz,p));")
    (cut-with-single-formula "#(flow%ext(f,g,iterate(f_1,x)(n)))")
    auto-instantiate-existential
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises flow%ext-recursive-equation)
     simplify)

    )))

(def-theorem flow%ext-extension-theorem-3
  "forall(f,f_1:[ind_1,ind_1],g:[ind_1,ind_2],x:ind_1, n:zz,
   forall(x:ind_1,#(flow%ext(f,g,x)) implies f(x)==f_1(x)) implies
      
   flow%ext(f_1,g,x)==flow%ext(f,g,first%entry(f_1, indic{x:ind_1, #(flow%ext(f,g,x))}, x)))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("#(first%entry(f_1, indic{x:ind_1,  #(flow%ext(f,g,x))}, x))"))
    (cut-with-single-formula "forsome(y:ind_1, first%entry(f_1,indic{x:ind_1,  #(flow%ext(f,g,x))},x)=y)")
    (antecedent-inference "with(p:prop,forsome(y:ind_1,p));")
    (backchain "with(y,i:ind_1,i=y);")
    (incorporate-antecedent "with(y,i:ind_1,i=y);")
    (apply-macete-with-minor-premises first%entry-characterization)
    (block 
     (script-comment "`apply-macete-with-minor-premises' at (0)")
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     direct-and-antecedent-inference-strategy
     (backchain-backwards "with(y,i:ind_1,i=y);")
     (apply-macete-with-minor-premises flow%ext-extension-theorem-1)
     direct-and-antecedent-inference-strategy
     (contrapose "with(p:prop,forall(m:zz,p));")
     auto-instantiate-existential
     (apply-macete-with-minor-premises flow%ext-recursive-equation)
     simplify)
    (instantiate-existential ("first%entry(f_1,indic{x:ind_1,  #(flow%ext(f,g,x))},x)"))
    simplify
    insistent-direct-inference
    (antecedent-inference "with(p:prop,p or p);")
    (contrapose "with(i:ind_2,#(i));")
    (apply-macete-with-minor-premises flow%ext-extension-theorem-2)
    (instantiate-existential ("f"))
    (contrapose "with(i:ind_1,not(#(i)));")
    (block 
     (script-comment "`contrapose' at (0)")
     (apply-macete-with-minor-premises first%entry-definedness)
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     (instantiate-existential ("k")))



    )))

(def-theorem flow%ext-domain-monotonicity
  "forall(g:[ind_1 -> ind_2], f:[ind_1,ind_1], h:[ind_1->ind_2], x:ind_1,
             dom{g} subseteq dom{h} and #(flow%ext(f,g,x)) 
                implies 
             #(flow%ext(f,h,x)))"
  (theory generic-theory-2)
  (usages transportable-macete)
  (proof
   (

    (apply-macete-with-minor-premises flow%ext-definedness)
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("n"))
    (instantiate-universal-antecedent "with(f:sets[ind_1],f subseteq f);"
				      ("iterate(f,x)(n)"))
    (simplify-antecedent "with(p:prop,not(p));")
    (simplify-antecedent "with(i:ind_1,f:sets[ind_1],i in f);")


    )))

