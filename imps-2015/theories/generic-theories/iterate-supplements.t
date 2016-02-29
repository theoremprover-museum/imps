(include-files
 (files (imps theories/generic-theories/iterate)))

(def-theorem iterate-front-back-lemma
  "forall(f:[ind_1,ind_1],x:ind_1,z:zz,
     f(iterate(f,x)(z))==iterate(f,f(x))(z))"
  (theory generic-theory-1)
  lemma
  reverse
  (proof 

   (


    direct-and-antecedent-inference-strategy
    (case-split ("0<=z"))
    (block 
     (script-comment "`case-split' at (1)")
     (induction trivial-integer-inductor ("z"))
     (block 
      (script-comment "`induction' at (0 0 0 0)")
      beta-reduce-repeatedly
      (unfold-single-defined-constant-globally iterate)
      simplify
      (case-split ("#(f(x))"))
      simplify
      simplify)
     (block 
      (script-comment "`induction' at (0 0 0 1 0 0 0 0 0 0 0)")
      (case-split ("#(f(x))"))
      (block 
       (script-comment "`case-split' at (1)")
       beta-reduce-repeatedly
       simplify)
      simplify))
    (block 
     (script-comment "`case-split' at (2)")
     insistent-direct-inference
     (antecedent-inference "with(p:prop,p or p);")
     (block 
      (script-comment "`antecedent-inference' at (0)")
      (contrapose "with(i:ind_1,#(i));")
      (cut-with-single-formula "not#(iterate(f,x)(z))")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises undefined-for-negative)
       simplify))
     (block 
      (script-comment "`antecedent-inference' at (1)")
      (contrapose "with(i:ind_1,#(i));")
      (case-split ("#(f(x))"))
      (apply-macete-with-minor-premises undefined-for-negative)
      simplify))
    )))

(def-theorem iterate-definedness-refinement
  "forall(f:[ind_1,ind_1],x:ind_1,z,j:zz, 
     0<=j and j<=z and #(iterate(f,x)(z)) implies #(iterate(f,x)(j)))"
  (theory generic-theory-1)
  (proof 

   (


    (induction trivial-integer-inductor ("z"))
    simplify
    simplify

    )))


(def-theorem iterate-additivity
  "forall(m,n:zz,x:ind_1,f:[ind_1,ind_1],
    0<=n and 0<=m
      implies
    iterate(f,iterate(f,x)(n))(m)==iterate(f,x)(n+m))"
  (theory generic-theory-1)
  (proof
   (

    (induction trivial-integer-inductor ("m"))
    (block 
     (script-comment "`induction' at (0 0 0 0 0 0 0)")
     simplify
     (case-split ("#(iterate(f,x)(n))"))
     (move-to-sibling 2)
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      insistent-direct-inference
      (antecedent-inference "with(p:prop,p or p);"))
     (unfold-single-defined-constant (0) iterate))
    (block 
     (script-comment "`induction' at (0 0 0 0 0 0 1 0 0 0 0 0)")
     (case-split ("#(iterate(f,x)(n))"))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      simplify
      (backchain "with(i:ind_1,i==i);")
      (unfold-single-defined-constant (1) iterate)
      simplify)
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      (contrapose "with(p:prop,not(p));")
      (apply-macete-with-minor-premises iterate-definedness-refinement)
      auto-instantiate-existential
      simplify))

    )))

(def-quasi-constructor invariant
  "lambda(s:sets[ind_1], f:[ind_1 -> ind_1], 
       forall(m:ind_1, m in s and #(f(m)) implies f(m) in s))"
  (language pure-generic-theory-1))

(def-theorem iterate-invariance
  "forall(f:[ind_1,ind_1],x:ind_1,z:zz,a:sets[ind_1], 
     forall(m:ind_1, m in a and #(f(m)) implies f(m) in a)  and x in a and 0<=z and
     #(iterate(f,x)(z))
      implies  
    iterate(f,x)(z) in a)"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (

    (induction integer-inductor ("z"))
    simplify
    )))

(def-theorem iterate-restriction-lemma-1
  "forall(f:[ind_1->ind_1], x:ind_1,s:sets[ind_1], n:zz,
    #(iterate(restrict{f,s},x)(n)) implies 
       iterate(f,x)(n)=iterate(restrict{f,s},x)(n))"
  (theory generic-theory-1)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("0<=n"))
    (induction trivial-integer-inductor ("n"))
    (block 
     (script-comment "`induction' at (0 0 0 0 0)")
     (unfold-single-defined-constant-globally iterate))
    simplify
    direct-and-antecedent-inference-strategy
    (incorporate-antecedent "with(i:ind_1,#(i));")
    (move-to-ancestor 1)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
     (contrapose "with(i:ind_1,#(i));")
     simplify-insistently)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
     (backchain-backwards "with(p:prop,p implies p);")
     simplify)
    (block 
     (script-comment "`case-split' at (2)")
     (contrapose "with(i:ind_1,#(i));")
     (apply-macete-with-minor-premises undefined-for-negative)
     simplify)
    )))

(def-theorem iterate-restriction-lemma-2
  "forall(f:[ind_1->ind_1], x:ind_1,s:sets[ind_1], n:zz,
    forall(j:zz, 0<=j and j< n implies iterate(f,x)(j) in s) and
    #(iterate(f,x)(n)) 
       implies 
    iterate(f,x)(n)=iterate(restrict{f,s},x)(n))"
  (theory generic-theory-1)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("0<=n"))
    (block 
     (script-comment "`case-split' at (1)")
     (induction trivial-integer-inductor ("n"))
     (unfold-single-defined-constant-globally iterate)
     (block 
      (script-comment "`induction' at (0 0 0 0 0 1 0 0 0 0 0 0 0 0)")
      (backchain-backwards "with(p:prop,p implies p);")
      direct-and-antecedent-inference-strategy
      simplify
      simplify))
    (block 
     (script-comment "`case-split' at (2)")
     (contrapose "with(i:ind_1,#(i));")
     (apply-macete-with-minor-premises undefined-for-negative)
     simplify)
    )))

(def-theorem iterate-locality
  "forall(f:[ind_1,ind_1],x:ind_1,z:zz,a:sets[ind_1], 
     forall(m:ind_1, m in a and #(f(m)) implies f(m) in a)  and x in a 
      implies  
    iterate(f,x)(z)==iterate(restrict{f,a},x)(z))"

  (theory generic-theory-1)
  (proof 

   (


    direct-and-antecedent-inference-strategy
    (case-split ("#(iterate(restrict{f,a},x)(z))"))
    (apply-macete-with-minor-premises iterate-restriction-lemma-1)
    (block 
     (script-comment "`case-split' at (2)")
     insistent-direct-inference
     (antecedent-inference "with(p:prop,p or p);")
     (contrapose "with(p:prop,not(p));")
     (apply-macete-with-minor-premises iterate-restriction-lemma-2)
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises iterate-invariance)
     direct-and-antecedent-inference-strategy
     (apply-macete-with-minor-premises iterate-definedness-refinement)
     auto-instantiate-existential
     simplify)
    )))



(def-constant entry%index
  "lambda(f:[ind_1->ind_1], s:sets[ind_1], x:ind_1, set%min(indic{m:zz, iterate(f,x)(m) in s}))"
  (theory generic-theory-1))

(def-theorem entry%index-characterization
  "forall(f:[ind_1->ind_1], s:sets[ind_1], x:ind_1, n:zz,
     entry%index(f,s,x)=n iff 
     (iterate(f,x)(n) in s and forall(m:zz, m<n implies not iterate(f,x)(m) in s)))"
  
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof 

   (

    (unfold-single-defined-constant (0) entry%index)
    (apply-macete-with-minor-premises iota-free-characterization-of-set%min)
    simplify-insistently
    )))

(def-theorem entry%index-definedness
  "forall(f:[ind_1->ind_1], s:sets[ind_1], x:ind_1, 
     #(entry%index(f,s,x)) iff forsome(n:zz, iterate(f,x)(n) in s))"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof 
   (


    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
     (cut-with-single-formula "forsome(n:zz, entry%index(f,s,x)=n)")
     (move-to-sibling 1)
     (instantiate-existential ("entry%index(f,s,x)"))
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(n:zz,p));")
      (incorporate-antecedent "with(n,z:zz,z=n);")
      (apply-macete-with-minor-premises entry%index-characterization)
      direct-and-antecedent-inference-strategy
      auto-instantiate-existential))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
     (unfold-single-defined-constant-globally entry%index)
     (apply-macete-with-minor-premises definedness-of-set%min)
     simplify-insistently
     direct-and-antecedent-inference-strategy
     auto-instantiate-existential
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0)")
      (instantiate-existential ("[-1]"))
      (cut-with-single-formula "not #(iterate(f,x)(j))")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises undefined-for-negative)
       simplify)))
    )))


(def-constant first%entry
  "lambda(f:[ind_1->ind_1], s:sets[ind_1], x:ind_1, iterate(f,x)(entry%index(f,s,x)))"
  (theory generic-theory-1))


(def-theorem first%entry-locality
  "forall(f:[ind_1,ind_1],x:ind_1, a,s :sets[ind_1], 
     forall(m:ind_1, m in a and #(f(m)) implies f(m) in a)  and x in a 
      implies  
    first%entry(f,s,x)==first%entry(restrict{f,a},s,x))"

  (theory generic-theory-1)
  (usages transportable-macete)
  (proof 

   (


    (unfold-single-defined-constant-globally first%entry)
    direct-and-antecedent-inference-strategy
    (case-split ("#(entry%index(f,s,x))"))
    (block 
     (script-comment "`case-split' at (1)")
     (cut-with-single-formula "#(entry%index(restrict{f,a},s,x))")
     (move-to-sibling 1)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (incorporate-antecedent "with(z:zz,#(z));")
      (apply-macete-with-minor-premises entry%index-definedness)
      (apply-macete-with-minor-premises iterate-locality))
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (cut-with-single-formula "forsome(m,n:zz, entry%index(f,s,x)=m and entry%index(restrict{f,a},s,x)=n)")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,forsome(m,n:zz,p));")
       (backchain "with(p:prop,p and p);")
       (backchain "with(p:prop,p and p);")
       (incorporate-antecedent "with(p:prop,p and p);")
       (apply-macete-with-minor-premises entry%index-characterization)
       (apply-macete-with-minor-premises iterate-locality)
       direct-and-antecedent-inference-strategy
       (cut-with-single-formula "m=n")
       (instantiate-universal-antecedent "with(x:ind_1,f:[ind_1,ind_1],s:sets[ind_1],m:zz,
  forall(m_$0:zz,
    m_$0<m implies not(iterate(f,x)(m_$0) in s)));"
					 ("n"))
       (instantiate-universal-antecedent "with(p:prop,forall(m:zz,p));"
					 ("m"))
       simplify)
      (instantiate-existential ("entry%index(f,s,x)" "entry%index(restrict{f,a},s,x)"))))
    (block 
     (script-comment "`case-split' at (2)")
     (cut-with-single-formula "not(#(entry%index(restrict{f,a},s,x)))")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      insistent-direct-inference
      (antecedent-inference "with(p:prop,p or p);"))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (contrapose "with(p:prop,not(p));")
      (incorporate-antecedent "with(z:zz,#(z));")
      (apply-macete-with-minor-premises entry%index-definedness)
      (apply-macete-with-minor-premises iterate-locality)))

    )))



(def-theorem first%entry-restriction-lemma
  "forall(f:[ind_1,ind_1],x:ind_1, a,s :sets[ind_1], 
     forall(m:ind_1, m in a and #(f(m)) implies f(m) in a)  and x in a 
      implies  
    first%entry(f,s,x)==first%entry(f, s inters a, x))"
  (theory generic-theory-1)
  (proof
   (
    (unfold-single-defined-constant-globally first%entry)
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "entry%index(f,s,x)==entry%index(f,s inters a,x)")
    (unfold-single-defined-constant-globally entry%index)
    (cut-with-single-formula "forall(m:zz, iterate(f,x)(m) in s inters a iff iterate(f,x)(m) in s)")
    (backchain "with(p:prop,forall(m:zz,p));")
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      (simplify-antecedent "with(m:zz,f:[zz,ind_1],a,s:sets[ind_1],f(m) in s inters a);"))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
      (cut-with-single-formula "iterate(f,x)(m) in a")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (apply-macete-with-minor-premises iterate-invariance)
       direct-and-antecedent-inference-strategy
       (cut-with-single-formula "#(iterate(f,x)(m))")
       (contrapose "with(i:ind_1,#(i));")
       (apply-macete-with-minor-premises undefined-for-negative)
       simplify))))))

(def-theorem first%entry-characterization
  "forall(f:[ind_1->ind_1], s:sets[ind_1], x,y:ind_1, 
     first%entry(f,s,x)=y iff
     (y in s and 
      forsome(n:zz, iterate(f,x)(n)=y and
      forall(m:zz, m<n implies not iterate(f,x)(m) in s))))"
  
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof 

   (

    
    (unfold-single-defined-constant-globally first%entry)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
     (cut-with-single-formula "#(entry%index(f,s,x))")
     (cut-with-single-formula "forsome(n:zz, entry%index(f,s,x)=n)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(n:zz,p));")
      (incorporate-antecedent "with(y,i:ind_1,i=y);")
      (backchain "with(n,z:zz,z=n);")
      (incorporate-antecedent "with(n,z:zz,z=n);")
      (apply-macete-with-minor-premises entry%index-characterization)
      direct-and-antecedent-inference-strategy
      simplify)
     (instantiate-existential ("entry%index(f,s,x)")))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1)")
     (cut-with-single-formula "forsome(n:zz, entry%index(f,s,x)=n)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(n:zz,p));")
      (incorporate-antecedent "with(y,i:ind_1,i=y);")
      (backchain "with(n,z:zz,z=n);")
      (incorporate-antecedent "with(n,z:zz,z=n);")
      (apply-macete-with-minor-premises entry%index-characterization)
      direct-and-antecedent-inference-strategy
      auto-instantiate-existential)
     (instantiate-existential ("entry%index(f,s,x)")))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0 0 0)")
     (cut-with-single-formula "entry%index(f,s,x)=n")
     simplify
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises entry%index-characterization)
      simplify))
    )))


(def-theorem first%entry-minimality
  "forall(g:[ind_1 -> ind_1], f:[ind_1,ind_1], s :sets[ind_1],
     forall(x:ind_1, g(x)==if(x in s, x, g(f(x))))
      implies
     forall(x:ind_1,
         #(first%entry(f,s,x)) implies first%entry(f,s,x)=g(x)))"

  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (



    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(p:ind_1, first%entry(f,s,x)=p)")
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
      (contrapose "with(n:zz,f:[zz,ind_1],#(f(n)));")
      (apply-macete-with-minor-premises undefined-for-negative)
      simplify)
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (cut-with-single-formula "forall(n:zz, 0<=n implies forall(p,x:ind_1, p in s and iterate(f,x)(n)=p and forall(m:zz,m<n implies not(iterate(f,x)(m) in s)) implies p=g(x)))")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (backchain "with(p:prop,
  forall(n:zz,
    0<=n implies forall(p,x:ind_1,with(p:prop,p))));")
       auto-instantiate-existential)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (weaken (4 3 2 1 0))
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
	 (contrapose "with(m_$0:zz,f:[zz,ind_1],s:sets[ind_1],f(m_$0) in s);")
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
    (instantiate-existential ("first%entry(f,s,x)"))

    )))

(def-theorem first%entry-definedness
  "forall(f:[ind_1->ind_1], s:sets[ind_1], x,y:ind_1, 
     #(first%entry(f,s,x)) iff
      forsome(n:zz, iterate(f,x)(n) in s))"
  (theory generic-theory-1)
  lemma
  (proof 

   (

    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
     (cut-with-single-formula "forsome(y:ind_1, first%entry(f,s,x)=y)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(y:ind_1,p));")
      (incorporate-antecedent "with(y,i:ind_1,i=y);")
      (apply-macete-with-minor-premises first%entry-characterization)
      direct-and-antecedent-inference-strategy
      (instantiate-existential ("n"))
      simplify)
     (instantiate-existential ("first%entry(f,s,x)")))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
     (unfold-single-defined-constant-globally first%entry)
     (cut-with-single-formula "forsome(m:zz, entry%index(f,s,x)=m)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(m:zz,p));")
      (backchain "with(m,z:zz,z=m);")
      (incorporate-antecedent "with(m,z:zz,z=m);")
      (apply-macete-with-minor-premises entry%index-characterization)
      direct-and-antecedent-inference-strategy)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (instantiate-existential ("entry%index(f,s,x)"))
      simplify
      (apply-macete-with-minor-premises entry%index-definedness)
      auto-instantiate-existential))

    )))




(def-theorem first%entry-equation
  "forall(f:[ind_1,ind_1],x:ind_1, s :sets[ind_1], 
    first%entry(f,s,x)==if(x in s, x,  first%entry(f,s,f(x))))"

  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("#(first%entry(f,s,f(x)))"))
    (block 
     (script-comment "`case-split' at (1)")
     simplify
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      (apply-macete-with-minor-premises first%entry-characterization)
      direct-and-antecedent-inference-strategy
      (instantiate-existential ("0"))
      (unfold-single-defined-constant (0) iterate)
      (block 
       (script-comment "`instantiate-existential' at (0 1 0 0)")
       (cut-with-single-formula "not #(iterate(f,x)(m))")
       simplify
       (apply-macete-with-minor-premises undefined-for-negative)))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      (apply-macete-with-minor-premises first%entry-characterization)
      direct-and-antecedent-inference-strategy
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
       (cut-with-single-formula "forsome(y:ind_1, first%entry(f,s,f(x))=y)")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(y:ind_1,p));")
	(backchain "with(y,i:ind_1,i=y);")
	(incorporate-antecedent "with(y,i:ind_1,i=y);")
	(apply-macete-with-minor-premises first%entry-characterization)
	direct-and-antecedent-inference-strategy)
       (instantiate-existential ("first%entry(f,s,f(x))")))
      (block 
       (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
       (cut-with-single-formula "forsome(y:ind_1, first%entry(f,s,f(x))=y)")
       (antecedent-inference "with(p:prop,forsome(y:ind_1,p));")
       (backchain "with(y,i:ind_1,i=y);")
       (incorporate-antecedent "with(y,i:ind_1,i=y);")
       (apply-macete-with-minor-premises first%entry-characterization)
       (apply-macete-with-minor-premises rev%iterate-front-back-lemma)
       direct-and-antecedent-inference-strategy
       (instantiate-existential ("n+1"))
       (block 
	(script-comment "`instantiate-existential' at (0 0)")
	(unfold-single-defined-constant (0) iterate)
	(cut-with-single-formula "0<=n")
	simplify
	(block 
	 (script-comment "`cut-with-single-formula' at (1)")
	 (cut-with-single-formula "#(iterate(f,x)(n))")
	 (contrapose "with(n:zz,f:[zz,ind_1],#(f(n)));")
	 (apply-macete-with-minor-premises undefined-for-negative)
	 simplify))
       (block 
	(script-comment "`instantiate-existential' at (0 1 0 0)")
	(unfold-single-defined-constant (0) iterate)
	(case-split ("m_$0=0"))
	simplify
	simplify))))
    (block 
     (script-comment "`case-split' at (2)")
     simplify
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      (apply-macete-with-minor-premises first%entry-characterization)
      direct-and-antecedent-inference-strategy
      (instantiate-existential ("0"))
      (unfold-single-defined-constant (0) iterate)
      (block 
       (script-comment "`instantiate-existential' at (0 1 0 0)")
       (cut-with-single-formula "not #(iterate(f,x)(m))")
       simplify
       (apply-macete-with-minor-premises undefined-for-negative)))
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
      insistent-direct-inference
      (antecedent-inference "with(p:prop,p or p);")
      (contrapose "with(i:ind_1,not(#(i)));")
      (incorporate-antecedent "with(i:ind_1,#(i));")
      (apply-macete-with-minor-premises first%entry-definedness)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (0)")
       direct-and-antecedent-inference-strategy
       (apply-macete-with-minor-premises rev%iterate-front-back-lemma)
       (incorporate-antecedent "with(i:ind_1,s:sets[ind_1],i in s);")
       (unfold-single-defined-constant (0) iterate)
       (case-split ("n=0"))
       simplify
       (block 
	(script-comment "`case-split' at (2)")
	simplify
	direct-and-antecedent-inference-strategy
	(instantiate-existential ("n-1"))
	simplify))
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (1)")
       (antecedent-inference "with(p:prop,forsome(n:zz,p));")
       (incorporate-antecedent "with(i:ind_1,s:sets[ind_1],i in s);")
       (unfold-single-defined-constant (0) iterate)
       (case-split ("n=0"))
       simplify
       (block 
	(script-comment "`case-split' at (2)")
	simplify
	(apply-macete-with-minor-premises iterate-front-back-lemma)
	simplify))))
    )))

(def-theorem first%entry-restricted-invariance
  "forall(f:[ind_1->ind_1], s:sets[ind_1],
        invariant{dom{lambda(x:ind_1, first%entry(f,s,x))}, restrict{f, s^^}})"
  (theory generic-theory-1)
  (proof
   (


    
    direct-and-antecedent-inference-strategy
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (contrapose "with(m_$0:ind_1,s:sets[ind_1],f:[ind_1,ind_1],
  #(first%entry(f,s,m_$0)));")
    (apply-macete-with-minor-premises first%entry-equation)
    simplify
    )))


;(def-theorem repeated-first%entry
;  "forall(f:[ind_1,ind_1],x:ind_1, s,s_1 :sets[ind_1],
;     s_1 subseteq s implies
;     first%entry(f,s_1,first%entry(f,s,x))==first%entry(f,s_1,x))"
;  (theory generic-theory-1)
;  (usages transportable-macete)
;  (proof
;   (


;    direct-and-antecedent-inference-strategy
;    (case-split ("#(first%entry(f,s_1,x))"))
;    (block 
;     (script-comment "`case-split' at (1)")
;     (cut-with-single-formula "#(first%entry(f,s,x))")
;     (move-to-sibling 1)
;     (block 
;      (script-comment "`cut-with-single-formula' at (1)")
;      (incorporate-antecedent "with(i:ind_1,#(i));")
;      (apply-macete-with-minor-premises first%entry-definedness)
;      direct-and-antecedent-inference-strategy
;      (instantiate-existential ("n"))
;      simplify)
;     (block 
;      (script-comment "`cut-with-single-formula' at (0)")
;      simplify
;      (cut-with-single-formula "forsome(y,y_1:ind_1, first%entry(f,s,x)=y and  first%entry(f,s_1,x)=y_1)")
;      (block 
;       (script-comment "`cut-with-single-formula' at (0)")
;       (antecedent-inference "with(p:prop,forsome(y,y_1:ind_1,p));")
;       (backchain "with(p:prop,p and p);")
;       (backchain "with(p:prop,p and p);")
;       (incorporate-antecedent "with(p:prop,p and p);")
;       (apply-macete-with-minor-premises first%entry-characterization)
;       direct-and-antecedent-inference-strategy
;       (cut-with-single-formula "n_$0<=n")
;       (move-to-sibling 1)
;       (block 
;	(script-comment "`cut-with-single-formula' at (1)")
;	(instantiate-universal-antecedent "with(x:ind_1,f:[ind_1,ind_1],s:sets[ind_1],n_$0:zz,
;  forall(m:zz,m<n_$0 implies not(iterate(f,x)(m) in s)));"
;					  ("n"))
;	simplify
;	(simplify-antecedent "with(p:prop,not(p));"))
;       (block 
;	(script-comment "`cut-with-single-formula' at (0)")
;	(instantiate-existential ("n-n_$0"))
;	(block 
;	 (script-comment "`instantiate-existential' at (0 0)")
;	 (backchain-backwards "with(y:ind_1,n_$0:zz,x:ind_1,f:[ind_1,ind_1],
;  iterate(f,x)(n_$0)=y);")
;	 (apply-macete-with-minor-premises iterate-additivity)
;	 (move-to-sibling 1)
;	 (block 
;	  (script-comment "`apply-macete-with-minor-premises' at (1)")
;	  (cut-with-single-formula "#(iterate(f,x)(n_$0))")
;	  (contrapose "with(n_$0:zz,f:[zz,ind_1],#(f(n_$0)));")
;	  (apply-macete-with-minor-premises undefined-for-negative)
;	  simplify)
;	 simplify)
;	(block 
;	 (script-comment "`instantiate-existential' at (0 1 0 0)")
;	 simplify
;	 (case-split ("0<=m_$0"))
;	 (move-to-sibling 2)
;	 (block 
;	  (script-comment "`case-split' at (2)")
;	  (cut-with-single-formula "not(#(iterate(f,y)(m_$0)))")
;	  simplify
;	  (block 
;	   (script-comment "`cut-with-single-formula' at (1)")
;	   (apply-macete-with-minor-premises undefined-for-negative)
;	   simplify))
;	 (block 
;	  (script-comment "`case-split' at (1)")
;	  (backchain-backwards "with(y:ind_1,n_$0:zz,x:ind_1,f:[ind_1,ind_1],
;  iterate(f,x)(n_$0)=y);")
;	  (apply-macete-with-minor-premises iterate-additivity)
;	  simplify))))
;      (instantiate-existential ("first%entry(f,s,x)" "first%entry(f,s_1,x)"))))
;    (block 
;     (script-comment "`case-split' at (2)")
;     (case-split ("#(first%entry(f,s,x))"))
;     (move-to-sibling 2)
;     (block 
;      (script-comment "`case-split' at (2)")

;      insistent-direct-inference
;      (antecedent-inference "with(p:prop,p or p);"))
;     (block 
;      (script-comment "`case-split' at (1)")
;      (cut-with-single-formula "not(#( first%entry(f,s_1,first%entry(f,s,x))))")
;      simplify
;      (block 
;       (script-comment "`cut-with-single-formula' at (1)")
;       (incorporate-antecedent "with(p:prop,not(p));")
;       (apply-macete-with-minor-premises first%entry-definedness)
;       direct-and-antecedent-inference-strategy
;       (contrapose "with(p:prop,not(p));")
;       (antecedent-inference "with(p:prop,forsome(n:zz,p));")
;       (cut-with-single-formula "forsome(y:ind_1, first%entry(f,s,x)=y)")
;       (block 
;	(script-comment "`cut-with-single-formula' at (0)")
;	(antecedent-inference "with(p:prop,forsome(y:ind_1,p));")
;	(incorporate-antecedent "with(i:ind_1,s_1:sets[ind_1],i in s_1);")
;	(backchain "with(y,i:ind_1,i=y);")
;	(incorporate-antecedent "with(y,i:ind_1,i=y);")
;	(apply-macete-with-minor-premises first%entry-characterization)
;	direct-and-antecedent-inference-strategy
;	(cut-with-single-formula "0<=n_$0 and 0<=n")
;	(move-to-sibling 1)
;	(block 
;	 (script-comment "`cut-with-single-formula' at (1)")
;	 (cut-with-single-formula "#(iterate(f,x)(n_$0)) and #(iterate(f,y)(n))")
;	 (move-to-sibling 1)
;	 simplify
;	 (block 
;	  (script-comment "`cut-with-single-formula' at (0)")
;	  (contrapose "with(p:prop,p and p);")
;	  (apply-macete-with-minor-premises undefined-for-negative)
;	  simplify
;	  (antecedent-inference "with(p:prop,p or p);")
;	  simplify
;	  simplify))
;	(block 
;	 (script-comment "`cut-with-single-formula' at (0)")
;	 (incorporate-antecedent "with(n:zz,f:[zz,ind_1],s_1:sets[ind_1],f(n) in s_1);")
;	 (backchain-backwards "with(y,i:ind_1,i=y);")
;	 (apply-macete-with-minor-premises iterate-additivity)
;	 direct-and-antecedent-inference-strategy
;	 (instantiate-existential ("n_$0+n"))))
;       (instantiate-existential ("first%entry(f,s,x)")))))

;    )))

;(def-theorem first%entry-idempotency
;  "forall(f:[ind_1,ind_1],x:ind_1, s :sets[ind_1], 
;     first%entry(f,s,first%entry(f,s,x))==first%entry(f,s,x))"
;  (theory generic-theory-1)
;  (proof
;   (

    
;    (apply-macete-with-minor-premises repeated-first%entry))))

(def-theorem first%entry-restriction-lemma-2
  "forall(f:[ind_1,ind_1],x:ind_1, a,s :sets[ind_1], 
    first%entry(f,s,x)==first%entry(restrict{f,s^^}, s, x))"
  (theory generic-theory-1)
  lemma
  reverse
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("#(first%entry(f,s,x))"))
    (block 
     (script-comment "`case-split' at (1)")
     simplify
     (cut-with-single-formula "forsome(y:ind_1, first%entry(f,s,x)=y)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(y:ind_1,p));")
      (backchain "with(y,i:ind_1,i=y);")
      (incorporate-antecedent "with(y,i:ind_1,i=y);")
      (apply-macete-with-minor-premises first%entry-characterization)
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula "forall(j:zz, 0<=j and j<=n implies #(iterate(f,x)(j)))")
      (move-to-sibling 1)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       direct-and-antecedent-inference-strategy
       (apply-macete-with-minor-premises iterate-definedness-refinement)
       auto-instantiate-existential)
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (cut-with-single-formula "first%entry(restrict{f,s^^},s,x)=y")
       simplify
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises first%entry-characterization)
	direct-and-antecedent-inference-strategy
	(cut-with-single-formula "forall(j:zz, 0<=j and j<=n implies iterate(restrict{f,s^^},x)(j)=iterate(f,x)(j))")
	(move-to-sibling 1)
	(block 
	 (script-comment "`cut-with-single-formula' at (1)")
	 direct-and-antecedent-inference-strategy
	 (apply-macete-with-minor-premises iterate-restriction-lemma-2)
	 (move-to-sibling 1)
	 simplify
	 (move-to-sibling 3)
	 simplify
	 simplify
	 (block 
	  (script-comment "`apply-macete-with-minor-premises' at (2)")
	  simplify
	  direct-and-antecedent-inference-strategy
	  simplify))
	(block 
	 (script-comment "`cut-with-single-formula' at (0)")
	 (instantiate-existential ("n"))
	 (block 
	  (script-comment "`instantiate-existential' at (0 0)")
	  (backchain "with(i:ind_1,p:prop,forall(j:zz,p and p implies i=i));")
	  simplify
	  (weaken (5 4 2 1 0))
	  (cut-with-single-formula "#(iterate(f,x)(n))")
	  (weaken (1))
	  (contrapose "with(p:prop,p);")
	  (apply-macete-with-minor-premises undefined-for-negative)
	  simplify)
	 (block 
	  (script-comment "`instantiate-existential' at (0 1 0 0)")
	  (case-split ("0<=m"))
	  simplify
	  (block 
	   (script-comment "`case-split' at (2)")
	   (cut-with-single-formula "not(#(iterate(restrict{f,s^^},x)(m)))")
	   simplify
	   (block 
	    (script-comment "`cut-with-single-formula' at (1)")
	    (apply-macete-with-minor-premises undefined-for-negative)
	    simplify)))))))
     (instantiate-existential ("first%entry(f,s,x)")))
    (block 
     (script-comment "`case-split' at (2)")
     insistent-direct-inference
     (antecedent-inference "with(p:prop,p or p);")
     (contrapose "with(p:prop,not(p));")
     (incorporate-antecedent "with(i:ind_1,#(i));")
     (apply-macete-with-minor-premises first%entry-definedness)
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "#(iterate(restrict{f,s^^},x)(n) )")
     (incorporate-antecedent "with(i:ind_1,s:sets[ind_1],i in s);")
     (apply-macete-with-minor-premises iterate-restriction-lemma-1)
     direct-and-antecedent-inference-strategy
     auto-instantiate-existential)

    )))


