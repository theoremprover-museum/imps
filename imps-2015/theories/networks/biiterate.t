(include-files
 (files (imps theories/vmach/iterate-lemmas)))

(def-constant biiterate
  "lambda(f,g:[ind_1,ind_1],x:ind_1,
     lambda(n:zz, if(even(n), iterate(f oo g, x) (n/2),g(iterate(f oo g, x)((n-1)/2)))))"
  (theory generic-theory-1))

(def-theorem biiterate-undefined-for-negative
  "forall(n:zz,x:ind_1,f,g:[ind_1,ind_1],n<0 implies not(#(biiterate(f,g,x)(n))))"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant (0) biiterate)
    direct-and-antecedent-inference-strategy
    (case-split ("even(n)"))
    (block 
     (script-comment "`case-split' at (1)")
     simplify
     (apply-macete-with-minor-premises undefined-for-negative)
     simplify
     (block (script-comment "`apply-macete-with-minor-premises' at (1)")
	    (incorporate-antecedent "with(n:zz,even(n))")
	    (unfold-single-defined-constant (0) even)
	    direct-and-antecedent-inference-strategy
	    simplify
	    (backchain "with(r:rr,n:zz,n=r)")
	    (weaken (0))
	    simplify))
    simplify
    (cut-with-single-formula "with(n:zz,x:ind_1,f,g:[ind_1,ind_1],   not(#(iterate(f oo g,x)([-1/2]+[1/2]*n)))) ")
    simplify
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (case-split ("#([-1/2]+[1/2]*n,zz)"))
     (move-to-sibling 2)
     simplify
     (block 
      (script-comment "`case-split' at (1)")
      (apply-macete-with-minor-premises undefined-for-negative)
      simplify))



    )))


(def-theorem biiterate-recursive-unfolding
  "forall(f,g:[ind_1,ind_1],x:ind_1, n:zz,
         biiterate(f,g,x)(n)== if(n=0,x, 
                                 even(n), f( biiterate(f,g,x)(n-1)), 
                                 g(biiterate(f,g,x)(n-1))))"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    direct-and-antecedent-inference-strategy
    (case-split ("0<=n"))
    (move-to-sibling 2)
    (block
     (script-comment "`case-split' at (2)")
     simplify
     (cut-with-single-formula "with(n:zz,g,f:[ind_1,ind_1], not #( biiterate(f,g,x)(n)) and not #( biiterate(f,g,x)([-1]+n)))")
     (block (script-comment "`cut-with-single-formula' at (0)")
	    (case-split ("even(n)"))
	    (block (script-comment "`case-split' at (1)")
		   simplify
		   insistent-direct-inference
		   (antecedent-inference "with(p:prop,p or p)"))
	    (block (script-comment "`case-split' at (2)")
		   simplify
		   insistent-direct-inference
		   (antecedent-inference "with(p:prop,p or p)")))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises biiterate-undefined-for-negative)
      simplify))
    (block 
     (script-comment "`case-split' at (1)")
     (unfold-single-defined-constant-globally biiterate)
     (case-split ("n=0"))
     (block 
      (script-comment "`case-split' at (1)")
      simplify
      (unfold-single-defined-constant (0) even)
      (cut-with-single-formula "forsome(j:zz,0=2*j)")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       simplify
       (unfold-single-defined-constant (0) iterate))
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (instantiate-existential ("0"))
       simplify))
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      (case-split ("even(n)"))
      (block 
       (script-comment "`case-split' at (1)")
       simplify
       (cut-with-single-formula "with(n:zz,not even([-1]+n))")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	simplify
	(unfold-single-defined-constant (0) iterate)
	beta-reduce-with-minor-premises
	(move-to-sibling 1)
	(block 
	 (script-comment "`beta-reduce-with-minor-premises' at (1)")
	 (incorporate-antecedent "with(n:zz,even(n))")
	 (unfold-single-defined-constant (0) even)
	 direct-and-antecedent-inference-strategy
	 (backchain "with(r:rr,n:zz,n=r)")
	 (weaken (0))
	 simplify)
	(block 
	 (script-comment "`beta-reduce-with-minor-premises' at (0)")
	 (cut-with-single-formula "with(n:zz,not [1/2]*n=0)")
	 (move-to-sibling 1)
	 simplify
	 simplify))
       (block
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises even-iff-suc-is-odd)
	simplify
	(apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)))
      (block
       (script-comment "`case-split' at (2)")
       simplify
       (apply-macete-with-minor-premises even-iff-suc-is-odd)
       simplify
       (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
       simplify)))





    )))


(def-theorem invariance-composition
  "forall(f,g:[ind_1,ind_1], a:sets[ind_1], invariant{a,f} and invariant{a,g} implies invariant{a, f oo g})" 
  (theory generic-theory-1)
  (proof 
   (
    direct-and-antecedent-inference-strategy
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain "with(f:[ind_1,ind_1],a:sets[ind_1],invariant{a,f})")
    direct-and-antecedent-inference-strategy
    (backchain "with(g:[ind_1,ind_1],a:sets[ind_1],invariant{a,g})")
    direct-and-antecedent-inference-strategy

    )))

(def-theorem biiterate-invariance
  "forall(f,g:[ind_1,ind_1],x:ind_1,z:zz,a:sets[ind_1], 
     invariant{a,f} and invariant{a,g}  and x in a and 0<=z and
     #(biiterate(f,g,x)(z))
      implies  
    biiterate(f,g,x)(z) in a)"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (
    (unfold-single-defined-constant-globally biiterate)
    direct-and-antecedent-inference-strategy
    (case-split ("even(z)"))
    (block (script-comment "`case-split' at (1)")
	   simplify
	   (apply-macete-with-minor-premises iterate-invariance)
	   simplify
	   (apply-macete-with-minor-premises invariance-composition)
	   direct-and-antecedent-inference-strategy)
    (block (script-comment "`case-split' at (2)")
	   simplify
	   (simplify-antecedent "with(i:ind_1,#(i))")
	   (backchain "with(g:[ind_1,ind_1],a:sets[ind_1],invariant{a,g})")
	   direct-and-antecedent-inference-strategy
	   (apply-macete-with-minor-premises iterate-invariance)
	   simplify
	   direct-and-antecedent-inference-strategy
	   (block (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
		  (apply-macete-with-minor-premises invariance-composition)
		  direct-and-antecedent-inference-strategy)
	   (block (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
		  (cut-with-single-formula "not z=0")
		  simplify
		  (block (script-comment "`cut-with-single-formula' at (1)")
			 (contrapose "with(p:prop,not(p))")
			 (unfold-single-defined-constant (0) even)
			 (instantiate-existential ("0"))
			 simplify)))
    )))


(def-theorem iterate-additivity
  iterate-additivity
  reverse
  (theory generic-theory-1)
  (proof existing-theorem))

(def-theorem biiterate-additivity-case-1
  "forall(f,g:[ind_1,ind_1],x:ind_1,n,m:zz,  0<=n and 0<=m and even(n) and even(m)
      implies
      biiterate(f,g,biiterate(f,g,x)(n))(m)==biiterate(f,g,x)(n+m))"
  (theory generic-theory-1)
  reverse
  (proof
   (

    direct-and-antecedent-inference-strategy
    unfold-defined-constants
    (cut-with-single-formula "even(n+m)")
    simplify
    (apply-macete-with-minor-premises commutative-law-for-addition)
    (apply-macete-with-minor-premises rev%iterate-additivity)
    (move-to-sibling 1)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (incorporate-antecedent "with(m:zz,even(m));")
      (unfold-single-defined-constant-globally even)
      direct-and-antecedent-inference-strategy
      (backchain "with(r:rr,m:zz,m=r);")
      (weaken (0))
      simplify)
    (move-to-sibling 2)
    (incorporate-antecedent "with(n:zz,even(n));")
    (unfold-single-defined-constant-globally even)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      (backchain "with(r:rr,n:zz,n=r);")
      (weaken (0))
      simplify)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      insistent-direct-inference
      (antecedent-inference "with(p:prop,p or p);")
      simplify
      simplify)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (incorporate-antecedent "with(m:zz,even(m));")
      (incorporate-antecedent "with(n:zz,even(n));")
      unfold-defined-constants
      direct-and-antecedent-inference-strategy
      (backchain "with(j_$0,n:zz,n=2*j_$0);")
      (backchain "with(j,m:zz,m=2*j);")
      (weaken (0 1))
      (instantiate-existential ("j_$0+j"))
      simplify)

    )))

(def-theorem biiterate-additivity-case-2
  "forall(f,g:[ind_1,ind_1],x:ind_1,n,m:zz,  0<=n and 0<=m and even(n) and odd(m)
      implies
      biiterate(f,g,biiterate(f,g,x)(n))(m)==biiterate(f,g,x)(n+m))"
  (theory generic-theory-1)
  reverse
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("#(biiterate(f,g,x)(n))"))
    (block 
      (script-comment "`case-split' at (1)")
      (apply-macete-with-minor-premises biiterate-recursive-unfolding)
      (cut-with-single-formula "1<=m")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	simplify
	(cut-with-single-formula "not even(m) and not even(m+n)")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  simplify
	  (apply-macete-with-minor-premises biiterate-additivity-case-1)
	  simplify
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (1)")
	    (apply-macete-with-minor-premises even-iff-suc-is-odd)
	    simplify))
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  direct-and-antecedent-inference-strategy
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	    (incorporate-antecedent "with(m:zz,odd(m));")
	    (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint))
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	    (cut-with-single-formula "odd(m+n)")
	    (block 
	      (script-comment "`cut-with-single-formula' at (0)")
	      (incorporate-antecedent "with(n,m:zz,odd(m+n));")
	      (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint))
	    (block 
	      (script-comment "`cut-with-single-formula' at (1)")
	      (incorporate-antecedent "with(m:zz,odd(m));")
	      (apply-macete-with-minor-premises odd-iff-suc-is-even)
	      (incorporate-antecedent "with(n:zz,even(n));")
	      (unfold-single-defined-constant-globally even)
	      direct-and-antecedent-inference-strategy
	      (instantiate-existential ("j+j_$0"))
	      simplify))))
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(cut-with-single-formula "not m=0")
	simplify
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (contrapose "with(m:zz,odd(m));")
	  (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
	  simplify
	  (unfold-single-defined-constant-globally even)
	  (instantiate-existential ("0"))
	  simplify)))
    (block 
      (script-comment "`case-split' at (2)")
      insistent-direct-inference
      (antecedent-inference "with(p:prop,p or p);")
      (contrapose "with(i:ind_1,#(i));")
      (incorporate-antecedent "with(i:ind_1,not(#(i)));")
      (apply-macete-locally biiterate-recursive-unfolding
			    (0)
			    "biiterate(f,g,x)(n+m)")
      (cut-with-single-formula "1<=m")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	simplify
	(cut-with-single-formula "not even(m+n)")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  simplify
	  (force-substitution "[-1]+m+n" "n+([-1]+m)" (0))
	  (block 
	    (script-comment "`force-substitution' at (0)")
	    (apply-macete-with-minor-premises rev%biiterate-additivity-case-1)
	    simplify
	    (block 
	      (script-comment "`apply-macete-with-minor-premises' at (1)")
	      (apply-macete-with-minor-premises even-iff-suc-is-odd)
	      simplify))
	  simplify)
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (contrapose "with(m:zz,odd(m));")
	  (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
	  simplify
	  (incorporate-antecedent "with(n,m:zz,even(m+n));")
	  (incorporate-antecedent "with(n:zz,even(n));")
	  (unfold-single-defined-constant-globally even)
	  direct-and-antecedent-inference-strategy
	  (instantiate-existential ("j-j_$0"))
	  simplify))
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(cut-with-single-formula "not m=0")
	simplify
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (contrapose "with(m:zz,odd(m));")
	  (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
	  simplify
	  (unfold-single-defined-constant-globally even)
	  (instantiate-existential ("0"))
	  simplify)))

    )))


(def-theorem biiterate-switch
  "forall(f,g:[ind_1,ind_1],x:ind_1,n:zz,
    not(n=[-1])
       implies 
    biiterate(f,g,x)(n+1)==biiterate(g,f,g(x))(n))"
  (theory generic-theory-1)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (case-split ("0<=n"))
    (block (script-comment "`case-split' at (1)")
	   (induction trivial-integer-inductor ("n"))
	   (block (script-comment "`induction' at (0 0 0 0 0)")
		  simplify
		  (case-split ("#(g(x))"))
		  (block (script-comment "`case-split' at (1)")
			 (apply-macete-with-minor-premises biiterate-recursive-unfolding)
			 simplify
			 (cut-with-single-formula "not(even(1))")
			 (block (script-comment "`cut-with-single-formula' at (0)")
				simplify
				(apply-macete-with-minor-premises biiterate-recursive-unfolding))
			 (block (script-comment "`cut-with-single-formula' at (1)")
				(apply-macete-with-minor-premises even-iff-suc-is-odd)
				(apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
				simplify
				(unfold-single-defined-constant-globally even)
				(instantiate-existential ("1"))
				simplify))
		  (block (script-comment "`case-split' at (2)")
			 insistent-direct-inference
			 (antecedent-inference "with(p:prop,p or p)")
			 (contrapose "with(i:ind_1,#(i))")
			 (apply-macete-with-minor-premises biiterate-recursive-unfolding)
			 simplify
			 (cut-with-single-formula "not(even(1))")
			 (block (script-comment "`cut-with-single-formula' at (0)")
				simplify
				(apply-macete-with-minor-premises biiterate-recursive-unfolding))
			 (block (script-comment "`cut-with-single-formula' at (1)")
				(apply-macete-with-minor-premises even-iff-suc-is-odd)
				simplify
				(apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
				simplify
				(unfold-single-defined-constant-globally even)
				(instantiate-existential ("1"))
				simplify)))
	   (block (script-comment "`induction' at (0 0 0 0 1 0 0 0 0)")
		  (case-split ("#(g(x))"))
		  (block (script-comment "`case-split' at (1)")
			 (apply-macete-with-minor-premises biiterate-recursive-unfolding)
			 simplify
			 (case-split ("even(t)"))
			 (block (script-comment "`case-split' at (1)")
				(cut-with-single-formula "even(2+t) and not even(1+t)")
				simplify
				(block (script-comment "`cut-with-single-formula' at (1)")
				       direct-and-antecedent-inference-strategy
				       (block (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
					      (contrapose "with(t:zz,even(t))")
					      (apply-macete-with-minor-premises even-iff-suc-is-odd)
					      (apply-macete-with-minor-premises odd-iff-suc-is-even)
					      simplify)
				       (block (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
					      (apply-macete-with-minor-premises even-iff-suc-is-odd)
					      (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
					      simplify)))
			 (block (script-comment "`case-split' at (2)")
				(cut-with-single-formula "not even(2+t) and even(1+t)")
				simplify
				(block (script-comment "`cut-with-single-formula' at (1)")
				       direct-and-antecedent-inference-strategy
				       (block (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
					      (contrapose "with(p:prop,not(p))")
					      (apply-macete-with-minor-premises even-iff-suc-is-odd)
					      (apply-macete-with-minor-premises odd-iff-suc-is-even)
					      simplify)
				       (block (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
					      (apply-macete-with-minor-premises even-iff-suc-is-odd)
					      (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
					      simplify))))
		  (block (script-comment "`case-split' at (2)")
			 insistent-direct-inference
			 (antecedent-inference "with(p:prop,p or p)")
			 (antecedent-inference "with(i:ind_1,i==i)")
			 (antecedent-inference "with(p:prop,p and p)")
			 (contrapose "with(x:ind_1,g:[ind_1,ind_1],not(#(g(x))))")
			 (move-to-ancestor 1)
			 (contrapose "with(i:ind_1,#(i))")
			 (apply-macete-with-minor-premises biiterate-recursive-unfolding)
			 simplify)))
    (block (script-comment "`case-split' at (2)")
	   insistent-direct-inference
	   (antecedent-inference "with(p:prop,p or p)")
	   (block (script-comment "`antecedent-inference' at (0)")
		  (contrapose "with(i:ind_1,#(i))")
		  (apply-macete-with-minor-premises biiterate-undefined-for-negative)
		  simplify)
	   (block (script-comment "`antecedent-inference' at (1)")
		  (contrapose "with(i:ind_1,#(i))")
		  (case-split ("#(g(x))"))
		  (block (script-comment "`case-split' at (1)")
			 (apply-macete-with-minor-premises biiterate-undefined-for-negative)
			 simplify)
		  simplify)))))


(def-theorem biiterate-additivity-case-3
  "forall(f,g:[ind_1,ind_1],x:ind_1,n,m:zz,  0<=n and 0<=m and odd(n) and even(m)
      implies
      biiterate(g,f,biiterate(f,g,x)(n))(m)==biiterate(f,g,x)(n+m))"
  (theory generic-theory-1)
  reverse
  (proof
   (

    direct-and-antecedent-inference-strategy
    (force-substitution "n" "(n-1)+1" (0))
    (move-to-sibling 1)
    simplify
    (block (script-comment "`force-substitution' at (0)")
	   (force-substitution "n+m" "((n-1)+m)+1" (0))
	   (move-to-sibling 1)
	   simplify
	   (block (script-comment "`force-substitution' at (0)")
		  (apply-macete-with-minor-premises biiterate-switch)
		  (block (script-comment "`apply-macete-with-minor-premises' at (0)")
			 (apply-macete-with-minor-premises rev%biiterate-additivity-case-1)
			 (block (script-comment "`apply-macete-with-minor-premises' at (1)")
				(apply-macete-with-minor-premises even-iff-suc-is-odd)
				simplify)
			 (block (script-comment "`apply-macete-with-minor-premises' at (2)")
				(cut-with-single-formula "not n=0")
				simplify
				(block (script-comment "`apply-macete-with-minor-premises' at (0 2 1)")
				       (contrapose "with(n:zz,odd(n))")
				       (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
				       simplify
				       (unfold-single-defined-constant (0) even)
				       (instantiate-existential ("0"))
				       simplify)))
		  (block (script-comment "`apply-macete-with-minor-premises' at (1)")
			 (contrapose "with(n:zz,odd(n))")
			 (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
			 simplify
			 (force-substitution "n" "-m" (0))
			 (move-to-sibling 1)
			 simplify
			 (block (script-comment "`force-substitution' at (0)")
				(incorporate-antecedent "with(m:zz,even(m))")
				(unfold-single-defined-constant (0 1) even)
				direct-and-antecedent-inference-strategy
				(instantiate-existential ("-j"))
				simplify))))
    )))


(def-theorem biiterate-additivity-case-4
  "forall(f,g:[ind_1,ind_1],x:ind_1,n,m:zz,  0<=n and 0<=m and odd(n) and odd(m)
      implies
      biiterate(g,f,biiterate(f,g,x)(n))(m)==biiterate(f,g,x)(n+m))"
  (theory generic-theory-1)
  reverse
  (proof
   (

    direct-and-antecedent-inference-strategy
    (case-split ("#(biiterate(f,g,x)(n))"))
    (block (script-comment "`case-split' at (1)")
	   (apply-macete-with-minor-premises biiterate-recursive-unfolding)
	   (cut-with-single-formula "even(n+m) and not even(m)")
	   (block (script-comment "`cut-with-single-formula' at (0)")
		  simplify
		  (cut-with-single-formula "1<=m")
		  (block (script-comment "`cut-with-single-formula' at (0)")
			 simplify
			 (force-substitution "[-1]+m+n"
					     "n+([-1]+m)"
					     (0))
			 (block (script-comment "`force-substitution' at (0)")
				(apply-macete-with-minor-premises biiterate-additivity-case-3)
				(apply-macete-with-minor-premises even-iff-suc-is-odd)
				(move-to-ancestor 1)
				simplify
				simplify)
			 (block (script-comment "`force-substitution' at (1)")
				(cut-with-single-formula "not m=0")
				simplify))
		  (block (script-comment "`cut-with-single-formula' at (1)")
			 (cut-with-single-formula "not m=0")
			 simplify
			 (block (script-comment "`cut-with-single-formula' at (1)")
				(weaken (0))
				(contrapose "with(m:zz,odd(m))")
				(apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
				simplify
				(unfold-single-defined-constant (0) even)
				(instantiate-existential ("0"))
				simplify)))
	   (block (script-comment "`cut-with-single-formula' at (1)")
		  direct-and-antecedent-inference-strategy
		  (block (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
			 (cut-with-single-formula "even(m-1) and even(n-1)")
			 (move-to-sibling 1)
			 (block (script-comment "`cut-with-single-formula' at (1)")
				(apply-macete-with-minor-premises even-iff-suc-is-odd)
				simplify)
			 (block (script-comment "`cut-with-single-formula' at (0)")
				(cut-with-single-formula "even(n+m-2)")
				(block (script-comment "`cut-with-single-formula' at (0)")
				       (contrapose "with(r:rr,even(r))")
				       (apply-macete-with-minor-premises even-iff-suc-is-odd)
				       (apply-macete-with-minor-premises odd-iff-suc-is-even)
				       simplify
				       (simplify-antecedent "with(p:prop,not(p))"))
				(block (script-comment "`cut-with-single-formula' at (1)")
				       (incorporate-antecedent "with(p:prop,p and p)")
				       (unfold-single-defined-constant-globally even)
				       direct-and-antecedent-inference-strategy
				       (instantiate-existential ("j+j_$0"))
				       simplify)))
		  (block (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
			 (contrapose "with(m:zz,odd(m))")
			 (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint))))
    (block (script-comment "`case-split' at (2)")
	   insistent-direct-inference
	   (antecedent-inference "with(p:prop,p or p)")
	   (contrapose "with(i:ind_1,#(i))")
	   (incorporate-antecedent "with(i:ind_1,not(#(i)))")
	   (apply-macete-locally biiterate-recursive-unfolding
				 (0)
				 "biiterate(f,g,x)(n+m)")
	   (cut-with-single-formula "1<=m")
	   (block (script-comment "`cut-with-single-formula' at (0)")
		  simplify
		  (cut-with-single-formula "even(m+n)")
		  (block (script-comment "`cut-with-single-formula' at (0)")
			 simplify
			 (force-substitution "[-1]+m+n"
					     "n+([-1]+m)"
					     (0))
			 (block (script-comment "`force-substitution' at (0)")
				(apply-macete-with-minor-premises rev%biiterate-additivity-case-3)
				simplify
				(block (script-comment "`apply-macete-with-minor-premises' at (1)")
				       (apply-macete-with-minor-premises even-iff-suc-is-odd)
				       simplify))
			 simplify)
		  (block (script-comment "`cut-with-single-formula' at (1)")
			 (cut-with-single-formula "even(m-1) and even(n-1)")
			 (block (script-comment "`cut-with-single-formula' at (0)")
				(incorporate-antecedent "with(p:prop,p and p)")
				(unfold-single-defined-constant-globally even)
				direct-and-antecedent-inference-strategy
				(instantiate-existential ("j+j_$0+1"))
				simplify)
			 (block (script-comment "`cut-with-single-formula' at (1)")
				(apply-macete-with-minor-premises even-iff-suc-is-odd)
				simplify)))
	   (block (script-comment "`cut-with-single-formula' at (1)")
		  (cut-with-single-formula "not m=0")
		  simplify
		  (block (script-comment "`cut-with-single-formula' at (1)")
			 (contrapose "with(m:zz,odd(m))")
			 (apply-macete-with-minor-premises even-and-odd-natural-numbers-are-disjoint)
			 simplify
			 (unfold-single-defined-constant (0) even)
			 (instantiate-existential ("0"))
			 simplify)))

    )))