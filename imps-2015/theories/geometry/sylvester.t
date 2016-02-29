(include-files
 (files (imps theories/geometry/presentation)
	(imps theories/geometry/cardinality)))

(def-theorem sylvester-lemma-1
  "forall(s:sets[points],
      f_indic_q{s} and not(coll_set(s))
       implies 
      forsome(a,b,c,p:points,
        coll(a,b,c)
         and 
        a in s
         and 
        b in s
         and 
        p in s
         and 
        not(c in on%connecting%line%through(s,p))))"

  (theory geometry-4)
  (proof

   (


    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,not(p));")
    (unfold-single-defined-constant (0) coll_set)
    direct-and-antecedent-inference-strategy
    (contrapose "with(p:prop,forall(a,b,c,p:points,with(p:prop,p)));")
    (cut-with-single-formula "forsome(c:points, c in le(x,y) and not c in on%connecting%line%through(s,z) inters le(x,y))")
    (move-to-sibling 1)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises lines-are-infinite)
      (apply-macete-with-minor-premises finitely-many-on%connecting%line%through)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	direct-and-antecedent-inference-strategy
	(unfold-single-defined-constant-globally le)
	simplify)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0 1)")
	(apply-macete-with-minor-premises lines-defining-axiom_geometry-2)
	(apply-macete-with-minor-premises le-is-a-line)))
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference-strategy (0))
      (instantiate-existential ("x" "y" "c" "z"))
      (block 
	(script-comment "`instantiate-existential' at (0 0)")
	(incorporate-antecedent "with(c,y,x:points,c in le(x,y));")
	(unfold-single-defined-constant (0) le)
	simplify
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
	  (contrapose "with(c:points,f:sets[points],not(c in f));")
	  (backchain "with(x,c:points,c=x);")
	  (weaken (1))
	  simplify-insistently
	  direct-and-antecedent-inference-strategy
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	    (unfold-single-defined-constant (0)
					    on%connecting%line%through)
	    (unfold-single-defined-constant (0)
					    connecting%lines%through)
	    simplify-insistently
	    (instantiate-existential ("le(x,z)"))
	    (block 
	      (script-comment "`instantiate-existential' at (0 0)")
	      (unfold-single-defined-constant (0) le)
	      simplify)
	    (block 
	      (script-comment "`instantiate-existential' at (0 1)")
	      (unfold-single-defined-constant (0) le)
	      simplify)
	    (block 
	      (script-comment "`instantiate-existential' at (0 2)")
	      (apply-macete-with-minor-premises les-are-connecting-lines)
	      direct-and-antecedent-inference-strategy))
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	    (unfold-single-defined-constant (0) le)
	    simplify))
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
	  (contrapose "with(c:points,f:sets[points],not(c in f));")
	  (backchain "with(y,c:points,c=y);")
	  (weaken (1))
	  simplify-insistently
	  direct-and-antecedent-inference-strategy
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	    (unfold-single-defined-constant (0)
					    on%connecting%line%through)
	    (unfold-single-defined-constant (0)
					    connecting%lines%through)
	    simplify-insistently
	    (instantiate-existential ("le(y,z)"))
	    (block 
	      (script-comment "`instantiate-existential' at (0 0)")
	      (unfold-single-defined-constant (0) le)
	      simplify)
	    (block 
	      (script-comment "`instantiate-existential' at (0 1)")
	      (unfold-single-defined-constant (0) le)
	      simplify)
	    (block 
	      (script-comment "`instantiate-existential' at (0 2)")
	      (apply-macete-with-minor-premises les-are-connecting-lines)
	      direct-and-antecedent-inference-strategy))
	  (block 
	    (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	    (unfold-single-defined-constant (0) le)
	    simplify)))
      (block 
	(script-comment "`instantiate-existential' at (0 4)")
	(contrapose "with(c:points,f:sets[points],not(c in f));")
	simplify-insistently))

    ))


  )

(def-theorem sylvester-lemma-2
  "forall(s:sets[points], a,b,c,p:points,
      f_indic_q{s} and
        coll(a,b,c)
         and 
        a in s
         and 
        b in s
         and 
        p in s
         and 
        not(c in on%connecting%line%through(s,p))
      implies
    not a=b and not a = p and not a=c and not b=p and not b=c and not p=c
    and not c in s)" 
  (theory geometry-4)
  (proof
   (
    (unfold-single-defined-constant-globally on%connecting%line%through)
    (unfold-single-defined-constant-globally connecting%lines%through)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
     (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
     (instantiate-existential ("c")))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0)")
     (contrapose "with(p:prop,not(forsome(l:sets[points],p)));")
     (backchain-backwards "with(p,a:points,a=p);")
     (instantiate-existential ("le(a,b)"))
     (block 
      (script-comment "`instantiate-existential' at (0 0)")
      (unfold-single-defined-constant-globally le)
      simplify)
     (block 
      (script-comment "`instantiate-existential' at (0 1 0)")
      (apply-macete-with-minor-premises le-contains-point)
      (apply-macete-with-minor-premises le-is-symmetric))
     (block 
      (script-comment "`instantiate-existential' at (0 1 1)")
      (apply-macete-with-minor-premises les-are-connecting-lines)
      simplify))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2 0)")
     (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
     (instantiate-existential ("b"))
     (apply-macete-with-minor-premises collinear-flipper-2-3))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 3 0)")
     (contrapose "with(p:prop,not(forsome(l:sets[points],p)));")
     (backchain-backwards "with(p,b:points,b=p);")
     (instantiate-existential ("le(a,b)"))
     (block 
      (script-comment "`instantiate-existential' at (0 0)")
      (unfold-single-defined-constant-globally le)
      simplify)
     (block 
      (script-comment "`instantiate-existential' at (0 1 0)")
      (apply-macete-with-minor-premises le-contains-point)
      (apply-macete-with-minor-premises le-is-symmetric))
     (block 
      (script-comment "`instantiate-existential' at (0 1 1)")
      (apply-macete-with-minor-premises les-are-connecting-lines)
      simplify))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 4 0)")
     (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
     (instantiate-existential ("a"))
     (apply-macete-with-minor-premises collinear-flipper-1-3)
     (apply-macete-with-minor-premises collinear-flipper-2-3))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 5 0)")
     (contrapose "with(p:prop,not(forsome(l:sets[points],p)));")
     (backchain "with(c,p:points,p=c);")
     (instantiate-existential ("le(a,b)"))
     (block 
      (script-comment "`instantiate-existential' at (0 0)")
      (unfold-single-defined-constant-globally le)
      simplify)
     (block 
      (script-comment "`instantiate-existential' at (0 1 1)")
      (apply-macete-with-minor-premises les-are-connecting-lines)
      simplify))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 6 0)")
     (contrapose "with(p:prop,not(forsome(l:sets[points],p)));")
     (unfold-single-defined-constant (0) connecting%lines)
     (instantiate-existential ("le(p,c)"))
     (block 
      (script-comment "`instantiate-existential' at (0 0)")
      (apply-macete-with-minor-premises le-is-symmetric)
      (apply-macete-with-minor-premises le-contains-left-point)
      simplify)
     (apply-macete-with-minor-premises le-contains-left-point)
     (block 
      (script-comment "`instantiate-existential' at (0 1 1)")
      (apply-macete-with-minor-premises indicator-facts-macete)
      beta-reduce
      (apply-macete-with-minor-premises le-is-a-line)
      simplify
      (apply-macete-with-minor-premises tr%cardinality-at-least-2)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (0)")
       (instantiate-existential ("p" "c"))
       simplify
       simplify)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (1)")
       (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
       (instantiate-existential ("s"))
       simplify
       simplify-insistently)))


    )))

(def-theorem sylvester-lemma-3
  "forall(s:sets[points],
      f_indic_q{s} and not(coll_set(s))
       implies 
      forsome(a,b,p,c:points,
        a in s and
        b in s and
        p in s and
        le(p,c) inters s =singleton{p} and
        forall(x:points, bet(p,x,c) implies not x in on%connecting%line(s))
          and
        nonempty_indic_q{le(p,c) inters le(a,b)} and
        c in on%connecting%line(s) and not p=c and not c in s))"
  (theory geometry-4)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "forsome(a,b,c,p:points,
        coll(a,b,c)
         and 
        a in s
         and 
        b in s
         and 
        p in s
         and 
        not(c in on%connecting%line%through(s,p)))"
     )
    (move-to-sibling 1)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises sylvester-lemma-1)
      direct-and-antecedent-inference-strategy
      )
    (antecedent-inference "with(p:prop,forsome(a,b,c,p:points,with(p:prop,p)));")
    (cut-with-single-formula
     " not a=b and not a=p and not a=c and not b=p and not b=c and not p=c and not c in s"
     )
    (antecedent-inference "with(p:prop,p and p and p and p and p and p and p);")
    (move-to-ancestor 2)
    (move-to-descendent (1))
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises sylvester-lemma-2) simplify
      )
    (weaken (0))
    (cut-with-single-formula
     "forsome(x:points, 
     x in on%connecting%line(s) inters le(p,c) diff singleton{p}
       and
     forall(y:points, y in on%connecting%line(s) inters le(p,c) diff singleton{p} implies not(bet(p,y,x))))"
     )
    (move-to-sibling 1)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises empty-segment-lemma)
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
	(instantiate-existential ("on%connecting%line(s) inters le(p,c)")) simplify-insistently
	(block 
	  (script-comment "`instantiate-existential' at (0 1)")
	  (apply-macete-with-minor-premises finitely-many-on%connecting%line)
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (0)")
	    direct-and-antecedent-inference-strategy
	    (antecedent-inference "with(p:prop,p and p and p and p and p);")
	    (contrapose "with(c:points,f:sets[points],not(c in f));")
	    (unfold-single-defined-constant-globally on%connecting%line%through)
	    (unfold-single-defined-constant-globally connecting%lines%through)
	    (apply-macete-with-minor-premises indicator-facts-macete) beta-reduce-repeatedly
	    (instantiate-existential ("le(p,c)"))
	    (block 
	      (script-comment "`instantiate-existential' at (0 0)")
	      (apply-macete-with-minor-premises le-contains-point)
	      (apply-macete-with-minor-premises le-is-symmetric)
	      )
	    (apply-macete-with-minor-premises le-contains-point)
	    )
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (1)")
	    (apply-macete-with-minor-premises lines-defining-axiom_geometry-2)
	    (apply-macete-with-minor-premises le-is-a-line)
	    ) ) )
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(instantiate-existential ("c")) simplify-insistently
	(unfold-single-defined-constant (0) on%connecting%line)
	(apply-macete-with-minor-premises indicator-facts-macete) beta-reduce-repeatedly
	direct-and-antecedent-inference-strategy
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	  (instantiate-existential ("le(a,b)"))
	  (block 
	    (script-comment "`instantiate-existential' at (0 0)")
	    (apply-macete-with-minor-premises les-are-connecting-lines) simplify
	    )
	  (block 
	    (script-comment "`instantiate-existential' at (0 1)")
	    (unfold-single-defined-constant-globally le) simplify
	    ) )
	(block 
	  (script-comment "`direct-and-antecedent-inference-strategy' at (1 0 0)")
	  (apply-macete-with-minor-premises le-contains-point)
	  (apply-macete-with-minor-premises definedness-of-le) simplify
	  ) ) )
    (antecedent-inference-strategy (0))
    (instantiate-existential ("a" "b" "p" "x"))
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
      simplify-insistently (antecedent-inference "with(p:prop,p and p and p and p and p);")
      (contrapose "with(c:points,f:sets[points],not(c in f));")
      (incorporate-antecedent "with(x:points,f:sets[points],x in f diff f);") simplify-insistently
      (unfold-single-defined-constant-globally le) simplify simplify
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 1)")
	(unfold-single-defined-constant-globally on%connecting%line%through)
	(unfold-single-defined-constant-globally connecting%lines%through)
	(unfold-single-defined-constant-globally connecting%lines)
	(apply-macete-with-minor-premises tr%cardinality-at-least-2)
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (0)")
	  (apply-macete-with-minor-premises indicator-facts-macete) beta-reduce-repeatedly
	  (instantiate-existential ("le(x_$2,p)"))
	  (block 
	    (script-comment "`instantiate-existential' at (0 0 0)")
	    (antecedent-inference "with(p:prop,p and p and p);")
	    (incorporate-antecedent "with(x_$2,x,p:points,x_$2 in le(p,x));")
	    (unfold-single-defined-constant-globally le) simplify
	    direct-and-antecedent-inference-strategy
	    (apply-macete-with-minor-premises coll-disjunctive-permuter) simplify
	    )
	  (block 
	    (script-comment "`instantiate-existential' at (0 0 1 0)")
	    (apply-macete-with-minor-premises le-contains-point)
	    (apply-macete-with-minor-premises definedness-of-le) simplify
	    )
	  (apply-macete-with-minor-premises le-is-a-line)
	  (block 
	    (script-comment "`instantiate-existential' at (0 0 1 1 1)")
	    (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
	    (instantiate-existential ("s")) simplify-insistently
	    (instantiate-existential ("x_$2" "p"))
	    (apply-macete-with-minor-premises le-contains-point)
	    ) )
	(block 
	  (script-comment "`apply-macete-with-minor-premises' at (1)")
	  (weaken (5 4 3 2 1 0 12 11 10 9 8 7 6))
	  (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
	  (instantiate-existential ("s")) simplify-insistently
	  ) )
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 2)")
	(unfold-single-defined-constant-globally on%connecting%line%through)
	(unfold-single-defined-constant-globally connecting%lines%through)
	(unfold-single-defined-constant-globally connecting%lines)
	(apply-macete-with-minor-premises tr%cardinality-at-least-2)
	(apply-macete-with-minor-premises indicator-facts-macete) beta-reduce-repeatedly
	(instantiate-existential ("le(p,x)"))
	(block 
	  (script-comment "`instantiate-existential' at (0 0)")
	  (unfold-single-defined-constant-globally le) simplify
	  direct-and-antecedent-inference-strategy direct-and-antecedent-inference-strategy
	  direct-and-antecedent-inference-strategy simplify
	  (apply-macete-with-minor-premises coll-disjunctive-permuter) simplify
	  )
	(block 
	  (script-comment "`instantiate-existential' at (0 1 0)")
	  (apply-macete-with-minor-premises le-contains-point)
	  (apply-macete-with-minor-premises definedness-of-le)
	  )
	(apply-macete-with-minor-premises le-is-a-line) (instantiate-existential ("x_$2" "p"))
	) )
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (backchain-backwards "with(p,x_$1:points,x_$1=p);")
    (move-to-ancestor 1)
    (backchain "with(p,x_$1:points,x_$1=p);")
    (apply-macete-with-minor-premises le-contains-left-point)
    (apply-macete-with-minor-premises definedness-of-le)
    (move-to-ancestor 1)
    simplify
    (move-to-ancestor 1)
    (weaken (15 2 0 14 13 12 10 11 9 8 7 6 5 4 3))
    simplify
    (incorporate-antecedent "with(p:prop,p);")
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 1)
    direct-and-antecedent-inference-strategy
    (move-to-ancestor 4)
    (move-to-descendent ((2 . 0)))
    (block 
      (script-comment "`apply-macete-with-minor-premises' at ((2 . 0))")
      (contrapose "with(x:points,f:sets[points],x in f diff f);")
      (backchain-backwards "with(x,p:points,p=x);") simplify-insistently
      )
    (block 
      (script-comment "`instantiate-existential' at (0 4 0 0)")
      (instantiate-universal-antecedent "with(p:prop,forall(y:points,p));" ("x_$3"))
      (contrapose "with(x_$3:points,f:sets[points],not(x_$3 in f));") simplify-insistently
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(cut-with-single-formula "le(p,c)=le(p,x)") (move-to-sibling 1)
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises two-points-determine-a-line)
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (0)")
	    (apply-macete-with-minor-premises le-is-a-line) (instantiate-existential ("p" "x"))
	    (block 
	      (script-comment "`instantiate-existential' at (0 0)")
	      (apply-macete-with-minor-premises distinctness-1-3)
	      (instantiate-existential ("x_$3"))
	      (apply-macete-with-minor-premises symmetry-of-betweeness)
	      )
	    simplify
	    (block 
	      (script-comment "`instantiate-existential' at (0 3)")
	      (incorporate-antecedent "with(x:points,f:sets[points],x in f diff f);")
	      simplify-insistently
	      )
	    (block 
	      (script-comment "`instantiate-existential' at (0 4)")
	      (apply-macete-with-minor-premises le-contains-point)
	      (apply-macete-with-minor-premises le-is-symmetric)
	      )
	    (block 
	      (script-comment "`instantiate-existential' at (0 5)")
	      (apply-macete-with-minor-premises le-contains-point)
	      (apply-macete-with-minor-premises definedness-of-le)
	      )
	    (block 
	      (script-comment "`instantiate-existential' at (0 6)")
	      (apply-macete-with-minor-premises le-contains-point)
	      (apply-macete-with-minor-premises definedness-of-le)
	      ) )
	  (apply-macete-with-minor-premises definedness-of-le)
	  )
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (backchain "with(x,c,p:points,le(p,c)=le(p,x));")
	  (unfold-single-defined-constant-globally le) simplify
	  direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises collinear-all-cases) simplify
	  ) )
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(force-substitution "x_$3=p" "p=x_$3" (0)) (move-to-sibling 1) simplify
	(block 
	  (script-comment "`force-substitution' at (0)")
	  (apply-macete-with-minor-premises distinctness-1-2) auto-instantiate-existential
	  ) ) )
    (block 
      (script-comment "`instantiate-existential' at (0 5)") (instantiate-existential ("c"))
      (unfold-single-defined-constant-globally le) simplify
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(contrapose "with(f:sets[points],f=f);") (backchain "with(x,p:points,p=x);")
	(unfold-single-defined-constant-globally le) simplify
	(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	(contrapose "with(x,p:points,p=x);") (antecedent-inference "with(p:prop,p and p);")
	(contrapose
	 "with(s,f:sets[points],p:points,
  singleton{p} subseteq f inters s);"
	 )
	(instantiate-existential ("p")) simplify-insistently simplify-insistently
	)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1 0)")
	(incorporate-antecedent "with(x:points,f:sets[points],x in f diff f);")
	simplify-insistently 
	(unfold-single-defined-constant-globally le) simplify
	direct-and-antecedent-inference-strategy
	(apply-macete-with-minor-premises coll-disjunctive-permuter) simplify
	) )
    (block 
      (script-comment "`instantiate-existential' at (0 6)")
      (incorporate-antecedent "with(x:points,f:sets[points],x in f diff f);") 
      simplify-insistently
      )
    (incorporate-antecedent "with(f:sets[points],f=f);")
    (weaken (6 9 8 7 7 5 4 3 2 1 0))
    (weaken (6 5 4 3 2 1 0))
    simplify-insistently
    beta-reduce-insistently
    beta-reduce-repeatedly
    (move-to-ancestor 4)
    (block 
      (script-comment "`instantiate-existential' at (0 7)")
      (contrapose "with(f:sets[points],nonempty_indic_q{f});") 
      (backchain "with(x,p:points,p=x);")
      (weaken (17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0)) 
      simplify-insistently
      simplify-insistently 
      (unfold-single-defined-constant-globally le)
      )
    (contrapose "with(f:sets[points],f=f);")
    (move-to-ancestor 1)
    (cut-with-single-formula "x in le(p,x) inters s")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises le-is-symmetric)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce
    simplify
    (apply-macete-with-minor-premises le-contains-left-point)
    simplify
    (move-to-ancestor 6)
    (block 
      (script-comment "`instantiate-existential' at (0 8)")
      (contrapose "with(f:sets[points],f=f);") (cut-with-single-formula "x in le(p,x)")
      (move-to-sibling 1)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(apply-macete-with-minor-premises le-contains-point)
	(apply-macete-with-minor-premises definedness-of-le) simplify
	)
      (block 
	(script-comment "`cut-with-single-formula' at (0)") simplify extensionality
	beta-reduce-repeatedly (instantiate-existential ("x")) simplify
	) )


    )))


(def-theorem sylvester-lemma-4
  "forall(l:lines, x:points, s:sets[points], x in l and 
    3<=f_card{s inters l} and not x in s implies 
    forsome(x1,x2,x3:points, 
      x1 in s inters l and 
      x2 in s inters l and 
      x3 in s inters l and 
      bet(x1,x2,x) and 
      (bet(x3,x1,x) or bet(x1,x,x3))))"
  (theory geometry-5)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(a,b,c:points, a in s inters l and b in s inters l and c in s inters l and not(a=b) and not(a=c) and not(b=c))")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%cardinality-at-least-3-lemma)
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference-strategy (0))
     (cut-with-single-formula "line(l)")
     (move-to-sibling 1)
     (apply-macete-with-minor-premises lines-in-quasi-sort_geometry-2)
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(l:lines,line(l));")
      (unfold-single-defined-constant-globally line)
      (unfold-single-defined-constant-globally coll_set)
      direct-and-antecedent-inference-strategy
      (weaken (0))
      (cut-with-single-formula "coll(a,b,x) and coll(a,c,x) and coll(b,c,x)")
      (move-to-sibling 1)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       direct-and-antecedent-inference-strategy
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(backchain "with(p:prop,forall(x,y,z:points,p));")
	direct-and-antecedent-inference-strategy
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	 (incorporate-antecedent "with(a:points,l:lines,s:sets[points],a in s inters l);")
	 simplify-insistently)
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	 (incorporate-antecedent "with(b:points,l:lines,s:sets[points],b in s inters l);")
	 simplify-insistently)
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (4)")
	 (contrapose "with(x:points,s:sets[points],not(x in s));")
	 (incorporate-antecedent "with(a:points,l:lines,s:sets[points],a in s inters l);")
	 simplify-insistently)
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (5)")
	 (contrapose "with(x:points,s:sets[points],not(x in s));")
	 (incorporate-antecedent "with(b:points,l:lines,s:sets[points],b in s inters l);")
	 simplify-insistently))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(backchain "with(p:prop,forall(x,y,z:points,p));")
	direct-and-antecedent-inference-strategy
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	 (incorporate-antecedent "with(c:points,l:lines,s:sets[points],c in s inters l);")
	 simplify-insistently)
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (5)")
	 (contrapose "with(x:points,s:sets[points],not(x in s));")
	 (incorporate-antecedent "with(c:points,l:lines,s:sets[points],c in s inters l);")
	 simplify-insistently))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (2)")
	(backchain "with(p:prop,forall(x,y,z:points,p));")
	direct-and-antecedent-inference-strategy
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	 (incorporate-antecedent "with(c:points,l:lines,s:sets[points],c in s inters l);")
	 simplify-insistently)
	(block 
	 (script-comment "`direct-and-antecedent-inference-strategy' at (5)")
	 (contrapose "with(x:points,s:sets[points],not(x in s));")
	 (incorporate-antecedent "with(c:points,l:lines,s:sets[points],c in s inters l);")
	 simplify-insistently)))
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (incorporate-antecedent "with(p:prop,p and p and p);")
       (unfold-single-defined-constant-globally coll)
       direct-and-antecedent-inference-strategy
       (instantiate-existential ("b" "c" "a"))
       (instantiate-existential ("b" "c" "a"))
       (instantiate-existential ("b" "c" "a"))
       (instantiate-existential ("a" "c" "b"))
       (instantiate-existential ("c" "a" "b"))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 1 2)")
	(instantiate-existential ("b" "a" "c"))
	(apply-macete-with-minor-premises extending)
	(instantiate-existential ("a")))
       (instantiate-existential ("a" "c" "b"))
       (instantiate-existential ("c" "a" "b"))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 2 2)")
	(instantiate-existential ("b" "c" "a"))
	(apply-macete-with-minor-premises extending)
	(instantiate-existential ("c"))
	simplify
	(apply-macete-with-minor-premises symmetry-of-betweeness))
       (instantiate-existential ("c" "b" "a"))
       (instantiate-existential ("a" "b" "c"))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 2)")
	(instantiate-existential ("c" "b" "a"))
	(apply-macete-with-minor-premises symmetry-of-betweeness))
       (instantiate-existential ("c" "b" "a"))
       (instantiate-existential ("b" "a" "c"))
       (instantiate-existential ("b" "a" "c"))
       (instantiate-existential ("c" "b" "a"))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 2 1)")
	(instantiate-existential ("c" "a" "b"))
	(apply-macete-with-minor-premises extending)
	(instantiate-existential ("a"))
	simplify)
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 2 2)")
	(instantiate-existential ("c" "b" "a"))
	(apply-macete-with-minor-premises symmetry-of-betweeness))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2 0 0)")
	(instantiate-existential ("a" "b" "c"))
	(apply-macete-with-minor-premises extending)
	(instantiate-existential ("b")))
       (instantiate-existential ("a" "b" "c"))
       (instantiate-existential ("a" "b" "c"))
       (instantiate-existential ("a" "c" "b"))
       (instantiate-existential ("b" "a" "c"))
       (instantiate-existential ("b" "a" "c"))
       (instantiate-existential ("a" "c" "b"))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2 2 1)")
	(instantiate-existential ("c" "a" "b"))
	(apply-macete-with-minor-premises symmetry-of-betweeness))
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0 0 2 2 2)")
	(cut-with-single-formula "coll(a,b,c)")
	(move-to-sibling 1)
	(block 
	 (script-comment "`cut-with-single-formula' at (1)")
	 (backchain "with(p:prop,forall(x,y,z:points,p));")
	 (incorporate-antecedent "with(c:points,l:lines,s:sets[points],c in s inters l);")
	 (incorporate-antecedent "with(a:points,l:lines,s:sets[points],a in s inters l);")
	 (incorporate-antecedent "with(b:points,l:lines,s:sets[points],b in s inters l);")
	 simplify-insistently)
	(block 
	 (script-comment "`cut-with-single-formula' at (0)")
	 (contrapose "with(c,b,a:points,coll(a,b,c));")
	 (unfold-single-defined-constant-globally coll)
	 (contrapose "with(p:prop,forall(x1,x2,x3:points,p or p or p or p or p));")
	 (antecedent-inference "with(p:prop,p or p or p);")
	 (block 
	  (script-comment "`antecedent-inference' at (0)")
	  (cut-with-single-formula "bet(a,b,x)")
	  (move-to-sibling 1)
	  (block 
	   (script-comment "`cut-with-single-formula' at (1)")
	   (apply-macete-with-minor-premises symmetry-of-betweeness)
	   (apply-macete-with-minor-premises nesting-2)
	   (apply-macete-with-minor-premises symmetry-of-betweeness)
	   (instantiate-existential ("c"))
	   (force-substitution "x=a"
			       "a=x"
			       (0))
	   simplify)
	  (block 
	   (script-comment "`cut-with-single-formula' at (0)")
	   (contrapose "with(x,b,a:points,bet(a,b,x));")
	   (apply-macete-with-minor-premises symmetry-of-betweeness)
	   (apply-macete-with-minor-premises anti-cyclic)
	   (apply-macete-with-minor-premises symmetry-of-betweeness)))
	 (block 
	  (script-comment "`antecedent-inference' at (1)")
	  (cut-with-single-formula "bet(x,a,b)")
	  (move-to-sibling 1)
	  (block 
	   (script-comment "`cut-with-single-formula' at (1)")
	   (apply-macete-with-minor-premises nesting-2)
	   (instantiate-existential ("c"))
	   (move-to-ancestor 2)
	   (apply-macete-with-minor-premises symmetry-of-betweeness)
	   (instantiate-existential ("c"))
	   (apply-macete-with-minor-premises distinctness-2-3)
	   auto-instantiate-existential)
	  (block 
	   (script-comment "`cut-with-single-formula' at (0)")
	   (contrapose "with(b,a,x:points,bet(x,a,b));")
	   (apply-macete-with-minor-premises anti-cyclic)))
	 (block 
	  (script-comment "`antecedent-inference' at (2)")
	  (cut-with-single-formula "bet(x,c,b)")
	  (move-to-sibling 1)
	  (block 
	   (script-comment "`cut-with-single-formula' at (1)")
	   (apply-macete-with-minor-premises nesting-2)
	   (instantiate-existential ("a"))
	   (apply-macete-with-minor-premises distinctness-2-3)
	   auto-instantiate-existential)
	  (block 
	   (script-comment "`cut-with-single-formula' at (0)")
	   (contrapose "with(c,x,b:points,bet(b,x,c));")
	   (apply-macete-with-minor-premises symmetry-of-betweeness)
	   (apply-macete-with-minor-premises anti-cyclic)))))))))))

(def-theorem  connecting-line-sufficient-condition
  "forall(s:sets[points],x:points,
     f_indic_q{s} and
     forsome(a,b:points, a in s and b in s and x in le(a,b))
       implies
     x in on%connecting%line(s))"
  (theory geometry-4)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally on%connecting%line)
    (unfold-single-defined-constant-globally connecting%lines)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    auto-instantiate-existential
    (block 
     (script-comment "`auto-instantiate-existential' at (0 0 0)")
     (apply-macete-with-minor-premises le-is-a-line)
     (cut-with-single-formula "#(le(a,b))")
     (incorporate-antecedent "with(f:sets[points],#(f));")
     (unfold-single-defined-constant-globally le)
     simplify)
    (block 
     (script-comment "`auto-instantiate-existential' at (0 0 1)")
     (apply-macete-with-minor-premises tr%cardinality-at-least-2)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (instantiate-existential ("a" "b"))
      (block 
       (script-comment "`instantiate-existential' at (0 0)")
       simplify-insistently
       (apply-macete-with-minor-premises le-contains-left-point))
      (block 
       (script-comment "`instantiate-existential' at (0 1)")
       simplify-insistently
       (apply-macete-with-minor-premises le-contains-point)
       (apply-macete-with-minor-premises le-is-symmetric)))
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
      auto-instantiate-existential
      simplify-insistently))

    )))



(def-theorem sylvester
  "forall(s:sets[points], f_indic_q{s} and not coll_set(s) 
                            implies 
                          forsome(l:lines, f_card{s inters l}=2))"
  (theory geometry-5)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (instantiate-theorem sylvester-lemma-3 ("s"))
    (incorporate-antecedent "with(c:points,s:sets[points],c in on%connecting%line(s));")
    (unfold-single-defined-constant (0) on%connecting%line)
    (unfold-single-defined-constant (0) connecting%lines)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (case-split ("2=f_card{s inters l}"))
    (block 
     (script-comment "`case-split' at (1)")
     (instantiate-existential ("l"))
     simplify)
    (cut-with-single-formula "3<=f_card{s inters l}")
    (move-to-sibling 1)
    simplify
    (weaken (1 2))
    (instantiate-theorem sylvester-lemma-4 ("l" "c" "s"))
    (move-to-ancestor 1)
    (cut-with-single-formula "not x1=c")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises distinctness-1-3)
     auto-instantiate-existential)
    (cut-with-single-formula "not x1=p and not coll(x1,c,p)")
    (move-to-sibling 1)
    (incorporate-antecedent "with(f:sets[points],f=f);")
    simplify-insistently
    (move-to-ancestor 1)
    (apply-macete-with-minor-premises tr%singletons-have-a-unique-member)
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (unfold-single-defined-constant (1) le)
    simplify
    direct-and-antecedent-inference-strategy
    (contrapose "forall(b_$0:points,
  with(p:prop,p and p) implies with(p:points,b_$0=p));")
    (backchain-backwards "with(p,x1:points,x1=p);")
    (backchain-backwards "with(p,x1:points,x1=p);")
    (instantiate-existential ("x2"))
    (block 
     (script-comment "`instantiate-existential' at (0 0 0)")
     (antecedent-inference "with(p:prop,p or p);")
     (move-to-ancestor 1)
     (apply-macete-with-minor-premises collinear-all-cases)
     simplify)
    (block 
     (script-comment "`instantiate-existential' at (0 1)")
     simplify
     (incorporate-antecedent "with(x2:points,l,s:sets[points],x2 in s inters l);")
     simplify-insistently)
    (backchain-backwards "with(p,x1:points,x1=p);")
    (apply-macete-with-minor-premises distinctness-1-2)
    (instantiate-existential ("c"))
    (move-to-ancestor 2)
    (block 
     (script-comment "`backchain-backwards' at (0)")
     (force-substitution "x2=x1" "x1=x2" (0))
     (move-to-sibling 1)
     simplify
     (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises distinctness-1-2)
      auto-instantiate-existential))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
     (apply-macete-with-minor-premises collinear-flipper-1-3)
     (contrapose "forall(b_$0:points,
  with(p:prop,p and p) implies with(p:points,b_$0=p));")
     (instantiate-existential ("x1"))
     (incorporate-antecedent "with(x1:points,l,s:sets[points],x1 in s inters l);")
     simplify-insistently)
    (instantiate-existential ("le(x1,p)"))
    (move-to-sibling 1)
    (block 
     (script-comment "`instantiate-existential' at (1)")
     (apply-macete-with-minor-premises lines-defining-axiom_geometry-2)
     (apply-macete-with-minor-premises le-is-a-line))
    (contrapose "with(p:prop,forall(x:points,p));")
    (cut-with-single-formula "3<=f_card{s inters le(x1,p)}")
    (move-to-sibling 1)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (cut-with-single-formula "2<=f_card{s inters le(x1,p)}")
     simplify
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises tr%cardinality-at-least-2)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (0)")
       (instantiate-existential ("x1" "p"))
       (block 
	(script-comment "`instantiate-existential' at (0 0)")
	simplify
	(apply-macete-with-minor-premises le-contains-left-point)
	(incorporate-antecedent "with(x1:points,l,s:sets[points],x1 in s inters l);")
	simplify-insistently)
       (block 
	(script-comment "`instantiate-existential' at (0 1)")
	simplify
	(apply-macete-with-minor-premises le-is-symmetric)
	(apply-macete-with-minor-premises le-contains-left-point)
	simplify))
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (1)")
       simplify
       simplify-insistently
       (move-to-ancestor 1)
       (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
       auto-instantiate-existential
       simplify
       simplify-insistently)))
    (cut-with-single-formula "forsome(q,y1,y2:points,q in s inters le(x1,p) and y1 in s inters le(x1,p) and y2 in s inters le(x1,p) and not q=y1 and not q=y2 and not y1=y2)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises tr%cardinality-at-least-3-lemma)
    (cut-with-single-formula "forsome(z:points, z in s inters le(x1,p) and not z=p and not z=x1)")
    (move-to-sibling 1)
    (incorporate-antecedent "with(p:prop,forsome(q,y1,y2:points,p));")
    simplify
    (move-to-ancestor 1)
    simplify-insistently
    (move-to-ancestor 2)
    (antecedent-inference "with(p:prop,forsome(q,y1,y2:points,p));")
    (cut-with-single-formula "not q=p and not q=x1 or not y1=p and not y1=x1 or not y2=p and not y2=x1")
    (move-to-sibling 1)
    simplify
    (incorporate-antecedent "with(p:prop,p and p and p and p and p and p);")
    simplify
    (move-to-ancestor 2)
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (antecedent-inference "with(p:prop,p and p and p and p and p and p);")
     simplify
     (weaken (3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25))
     (weaken (0))
     simplify
     (prove-by-logic-and-simplification 0))
    (weaken (22 20 19 18 17 15 14 16 21 13 12 11 10 9 8 7 6 4 5 3 2))
    (prove-by-logic-and-simplification 0)
    (move-to-ancestor 4)
    (prove-by-logic-and-simplification 3)
    (move-to-ancestor 4)
    (antecedent-inference "with(p:prop,p or p or p);")
    (move-to-ancestor 4)
    (antecedent-inference "with(p:prop,p or p or p);")
    (move-to-ancestor 2)
    (move-to-descendent (0))
    auto-instantiate-existential
    (move-to-ancestor 1)
    (antecedent-inference-strategy (0))
    (move-to-ancestor 5)
    (move-to-descendent (0 (1 . 0)))
    (instantiate-existential ("q"))
    (instantiate-existential ("y1"))
    (instantiate-existential ("y2"))
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,forsome(z:points,p));")
     (antecedent-inference "with(p:prop,p and p and p);")
     (incorporate-antecedent "with(z,p,x1:points,s:sets[points],z in s inters le(x1,p));")
     simplify
     (apply-macete-with-minor-premises connecting-line-sufficient-condition)
     (unfold-single-defined-constant (0) le)
     simplify
     (unfold-single-defined-constant (0) coll)
     (force-substitution "forsome(x:points,
    bet(p,x,c)
     and 
    forsome(b,a:points,a in s and b in s and x in le(a,b)))"
			 "forsome (a,b:points,forsome(x:points,
   
    a in s and b in s and x in le(a,b) and bet(p,x,c)))"
			 (0))
     (move-to-sibling 1)
     (block 
      (script-comment "`force-substitution' at (1)")
      (weaken (0 1 2 3 4 5 6 7 8 9))
      (weaken (0 1 2 3 4 5 6 7 8 9))
      (weaken (0 1 2 3 4))
      (prove-by-logic-and-simplification 3)
      auto-instantiate-existential
      auto-instantiate-existential)
     (block 
      (script-comment "`force-substitution' at (0)")
      direct-inference
      (antecedent-inference "with(p:prop,z:points,s:sets[points],
  z in s and (p or p or p));")
      (antecedent-inference "with(p:prop,p or p or p);")
      (move-to-sibling 1)
      (block 
       (script-comment "`antecedent-inference' at (1)")
       (instantiate-existential ("z" "x2"))
       simplify
       (incorporate-antecedent "with(x2:points,l,s:sets[points],x2 in s inters l);")
       simplify
       direct-inference
       (apply-macete-with-minor-premises symmetry-of-betweeness)
       (apply-macete-with-minor-premises weak-pasch)
       (instantiate-existential ("x1"))
       (block 
	(script-comment "`instantiate-existential' at (0 0)")
	(apply-macete-with-minor-premises coll-conjunctive-permuter)
	simplify)
       simplify
       (apply-macete-with-minor-premises symmetry-of-betweeness))
      (block 
       (script-comment "`antecedent-inference' at (0)")
       (instantiate-existential ("z" "x2"))
       (force-substitution "x in le(z,x2)" "coll(z,x,x2)" (0))
       (move-to-sibling 1)
       (block 
	(script-comment "`force-substitution' at (1)")
	(unfold-single-defined-constant (0) le)
	(force-substitution "coll(z,x,x2)"
			    "coll(z,x2,x)"
			    (0))
	(move-to-sibling 1)
	(block 
	 (script-comment "`force-substitution' at (1)")
	 direct-inference
	 (apply-macete-with-minor-premises collinear-flipper-2-3))
	(block 
	 (script-comment "`force-substitution' at (0)")
	 (weaken (0 1
		    2
		    3
		    4
		    5
		    6
		    7
		    8
		    9
		    10
		    11
		    12
		    13
		    14
		    15))
	 (weaken (0 1 2 3 4 5 6 7 8 9 10))
	 simplify
	 (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
	 direct-inference
	 auto-instantiate-existential))
       (block 
	(script-comment "`force-substitution' at (0)")
	(incorporate-antecedent "with(x2:points,l,s:sets[points],x2 in s inters l);")
	simplify
	direct-inference
	(apply-macete-with-minor-premises symmetry-of-betweeness)
	(apply-macete-with-minor-premises weak-pasch-other)
	(instantiate-existential ("x1"))
	(apply-macete-with-minor-premises collinear-flipper-1-2)
	simplify
	(apply-macete-with-minor-premises symmetry-of-betweeness)))
      (block 
       (script-comment "`antecedent-inference' at (2)")
       (antecedent-inference "with(p:prop,p or p);")
       (block 
	(script-comment "`antecedent-inference' at (0)")
	(instantiate-existential ("x3" "z"))
	(incorporate-antecedent "with(x3:points,l,s:sets[points],x3 in s inters l);")
	simplify
	direct-inference
	(apply-macete-with-minor-premises weak-pasch)
	(instantiate-existential ("x1"))
	(apply-macete-with-minor-premises collinear-flipper-1-3)
	(apply-macete-with-minor-premises symmetry-of-betweeness)
	(apply-macete-with-minor-premises symmetry-of-betweeness))
       (block 
	(script-comment "`antecedent-inference' at (1)")
	(instantiate-existential ("x3" "z"))
	(force-substitution "x in le(x3,z)"
			    "coll(x3,x,z)"
			    (0))
	(move-to-sibling 1)
	(block 
	 (script-comment "`force-substitution' at (1)")
	 (unfold-single-defined-constant (0) le)
	 (apply-macete-locally-with-minor-premises collinear-flipper-2-3
                                                                 
						   (0)
                                                                 
						   "coll(x3,x,z)")
	 simplify
	 (apply-macete-with-minor-premises collinear-implies-distinct-lemma)
	 direct-inference
	 auto-instantiate-existential)
	(block 
	 (script-comment "`force-substitution' at (0)")
	 (incorporate-antecedent "with(x3:points,l,s:sets[points],x3 in s inters l);")
	 simplify
	 direct-inference
	 (apply-macete-with-minor-premises weak-pasch-other)
	 (instantiate-existential ("x1"))
	 (block 
	  (script-comment "`instantiate-existential' at (0 0)")
	  (apply-macete-with-minor-premises coll-conjunctive-permuter)
	  simplify)
	 (apply-macete-with-minor-premises symmetry-of-betweeness))))))

    )))

