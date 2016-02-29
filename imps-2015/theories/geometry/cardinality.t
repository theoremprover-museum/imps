(include-files
   (files (imps theories/geometry/presentation)
	  (imps theories/cardinality/combinatorics)))


(def-constant connecting%lines
  "lambda(s:sets[points], indic{ll:sets[points], line(ll) and 2<=f_card{s inters ll}})"
  (theory geometry-3))

(def-theorem cardinality-at-least-2-lemma
  "forall(s:sets[ind_1], 
      2<=f_card{s} implies forsome(a,b:ind_1, a in s and b in s and not(a=b)))"
  lemma
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(n:nn, f_card{s}=n)")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (incorporate-antecedent "with(n:nn,2<=n);") (antecedent-inference "with(p:prop,p);")
      (backchain "with(p:prop,p);") (incorporate-antecedent "with(p:prop,p);")
      (apply-macete-with-minor-premises iota-free-definition-of-f-card)
      direct-and-antecedent-inference-strategy (contrapose "with(f:sets[nn],f=f);")
      (unfold-single-defined-constant (0) omega)
      (contrapose "with(p:prop,forall(a,b:ind_1,p and p implies a=b));")
      (cut-with-single-formula "forsome(a,b:ind_1, a in s and b in s and f(a)=0 and f(b)=1)")
      (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(antecedent-inference "with(p:prop,forsome(a,b:ind_1,p));")
	(instantiate-existential ("a" "b"))
	(antecedent-inference "with(p:prop,p and p and p and p);") (contrapose "with(n:nn,n=1);")
	simplify 
	(backchain-backwards "with(b,a:ind_1,a=b);")
	simplify
	)
      (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(incorporate-antecedent "with(f:sets[nn],f=f);")
	(apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	direct-and-antecedent-inference-strategy
	(incorporate-antecedent
	 "with(f:[nn,prop],pred_to_indic(f))
 subseteq with(f:[ind_1,nn],ran{f});"
	 )
	(move-to-ancestor 1)
	(instantiate-universal-antecedent-multiply
	 "with(f:[nn,prop],pred_to_indic(f))
 subseteq with(f:[ind_1,nn],ran{f});"
	 (("0") ("1"))
	 )
	(block 
	  (script-comment "`instantiate-universal-antecedent-multiply' at (0 0 0 0 0)")
	  (contrapose "with(f:sets[nn],not(1 in f));") simplify-insistently
	  )
	(block 
	  (script-comment "`instantiate-universal-antecedent-multiply' at (0 0 0 0 1)")
	  (contrapose "with(p:prop,not(p));") simplify-insistently
	  )
	(block 
	  (script-comment "`instantiate-universal-antecedent-multiply' at (0 0 0 1 0)")
	  (contrapose "with(p:prop,not(p));") simplify-insistently
	  )
	(block 
	  (script-comment "`instantiate-universal-antecedent-multiply' at (0 0 0 1 1)")
	  (incorporate-antecedent "with(f:sets[nn],1 in f);")
	  (incorporate-antecedent "with(f:sets[nn],0 in f);") simplify-insistently
	  direct-and-antecedent-inference-strategy (instantiate-existential ("x_$0" "x_$1"))
	  (block 
	    (script-comment "`instantiate-existential' at (0 0 0 (1 . 0))")
	    (backchain-backwards "with(s,f:sets[ind_1],f=s);") simplify-insistently
	    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
	    )
	  (block 
	    (script-comment "`instantiate-existential' at (0 1)")
	    (backchain-backwards "with(s,f:sets[ind_1],f=s);")
	    (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
	    ) ) ) )
    (instantiate-existential ("f_card{s}"))

    )))

(def-theorem cardinality-at-most-1-lemma
  "forall(s:sets[ind_1], 
      f_card{s}<=1 implies (empty_indic_q{s} or forsome(a:ind_1, s=singleton{a})))"
  lemma
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (

    direct-inference
    direct-inference
    (cut-with-single-formula "f_card{s}=0 or f_card{s}=1")
    (move-to-sibling 1)
    simplify
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,p or p);")
     (block 
      (script-comment "`antecedent-inference' at (0)")
      (incorporate-antecedent "with(n:nn,n=0);")
      (apply-macete-with-minor-premises empty-indic-has-f-card-zero)
      direct-inference
      (backchain "with(f,s:sets[ind_1],s=f);")
      (weaken (0 1))
      simplify-insistently)
     (block 
      (script-comment "`antecedent-inference' at (1)")
      (incorporate-antecedent "with(n:nn,n=1);")
      (apply-macete-with-minor-premises singleton-has-f-card-one)
      simplify))

    )))


(def-theorem cardinality-at-least-2
  "forall(s:sets[ind_1], f_indic_q{s} implies
      (2<=f_card{s} iff forsome(a,b:ind_1, a in s and b in s and not(a=b))))"
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises cardinality-at-least-2-lemma)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0)")
     (cut-with-single-formula "not (empty_indic_q{s} or forsome(a:ind_1, s=singleton{a}))")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (contrapose "with(p:prop,not(p or p));")
      (apply-macete-with-minor-premises cardinality-at-most-1-lemma)
      simplify)
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (contrapose "with(p:prop,not(p));")
      (antecedent-inference "with(p:prop,p or p);")
      (instantiate-universal-antecedent "with(s:sets[ind_1],empty_indic_q{s});"
					("a"))
      (block 
       (script-comment "`antecedent-inference' at (1)")
       (antecedent-inference "with(p:prop,forsome(a:ind_1,p));")
       (contrapose "with(f,s:sets[ind_1],s=f);")
       (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
       (contrapose "with(p:prop,not(p));")
       (antecedent-inference "with(p:prop,p and p);")
       (contrapose "with(a_$0:ind_1,s:sets[ind_1],s subseteq singleton{a_$0});")
       (apply-macete-with-minor-premises tr%in-singleton-iff-equals-single-member)
       (case-split ("a=a_$0"))
       (block 
	(script-comment "`case-split' at (1)")
	(instantiate-existential ("b"))
	simplify)
       (instantiate-existential ("a")))))
    )))

(def-theorem cardinality-at-least-3-lemma
  "forall(s:sets[ind_1], 
      3<=f_card{s} 
       implies 
      forsome(a,b,c:ind_1, 
       a in s and b in s and c in s and not(a=b) and not(a=c) and not(b=c)))"
  lemma
  (theory generic-theory-1)
  (usages transportable-macete)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(n:nn, f_card{s}=n)")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (incorporate-antecedent "with(n:nn,3<=n);")
     (antecedent-inference "with(p:prop,p);")
     (backchain "with(p:prop,p);")
     (incorporate-antecedent "with(p:prop,p);")
     (apply-macete-with-minor-premises iota-free-definition-of-f-card)
     direct-and-antecedent-inference-strategy
     (contrapose "with(f:sets[nn],f=f);")
     (unfold-single-defined-constant (0) omega)
     (contrapose "with(p:prop,forall(a,b,c:ind_1,p));")
     (cut-with-single-formula "forsome(a,b,c:ind_1, a in s and b in s and c in s and f(a)=0 and f(b)=1 and f(c)=2)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(a,b,c:ind_1,p));")
      (instantiate-existential ("a" "b" "c"))
      (block 
       (script-comment "`instantiate-existential' at (0 3)")
       (contrapose "with(p:prop,p and p and p and p and p and p);")
       simplify)
      (block 
       (script-comment "`instantiate-existential' at (0 4)")
       (contrapose "with(p:prop,p and p and p and p and p and p);")
       simplify)
      (block 
       (script-comment "`instantiate-existential' at (0 5)")
       (contrapose "with(p:prop,p and p and p and p and p and p);")
       simplify))
     (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (incorporate-antecedent "with(f:sets[nn],f=f);")
      (apply-macete-with-minor-premises tr%indic-free-characterization-of-ran)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent-multiply 
       "with(p:prop,forall(y_$0:nn,p));"
       (("0") ("1") ("2")))
      (block 
       (script-comment 
	"`instantiate-universal-antecedent-multiply' at (0 0 0 0 0 0 0 0 0 0)")
       (instantiate-existential ("x_$1" "x_$2" "x_$0"))
       (block 
	(script-comment "`instantiate-existential' at (0 0 0 (1 . 0))")
	(backchain-backwards "with(s,f:sets[ind_1],f=s);")
	simplify
	(apply-macete-with-minor-premises tr%domain-membership-iff-defined))
       (block 
	(script-comment "`instantiate-existential' at (0 1)")
	(backchain-backwards "with(s,f:sets[ind_1],f=s);")
	(apply-macete-with-minor-premises tr%domain-membership-iff-defined))
       (block 
	(script-comment "`instantiate-existential' at (0 2)")
	(backchain-backwards "with(s,f:sets[ind_1],f=s);")
	(apply-macete-with-minor-premises tr%domain-membership-iff-defined)))
      (simplify-antecedent "with(p:prop,not(p));")
      (simplify-antecedent "with(p:prop,not(p));")
      (simplify-antecedent "with(n:nn,not(2<n));")
      (simplify-antecedent "with(p:prop,not(p));")
      (block 
       (script-comment "`instantiate-universal-antecedent-multiply' at (0 0 0 0 1 0 0 1)")
       (simplify-antecedent "with(n:nn,not(0<n));")
       (simplify-antecedent "with(p:prop,not(p));"))
      (block 
       (script-comment "`instantiate-universal-antecedent-multiply' at (0 0 0 0 1 1 0 0)")
       (simplify-antecedent "with(n:nn,not(0<n));")
       (simplify-antecedent "with(p:prop,not(p));"))
      (simplify-antecedent "with(n:nn,not(1<n));")))
    (instantiate-existential ("f_card{s}")))))

(def-theorem injectivity-of-trace
  "forall(s:sets[points],
 injective_on_q{lambda(ll:sets[points], if(ll in connecting%lines(s),
                     s inters ll,
                     ?sets[points])),
                      connecting%lines(s)})"
  (theory geometry-3)
  (proof
   (
    direct-inference
    insistent-direct-inference
    beta-reduce-repeatedly
    (unfold-single-defined-constant-globally connecting%lines)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula " forsome(a,b:points, a in s inters x_1 and b in s inters x_1 and not(a=b))")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (simplify-antecedent "with(f:sets[points],f=f);")
      (antecedent-inference "with(p:prop,forsome(a,b:points,p));")
      (apply-macete-with-minor-premises two-points-determine-a-line)
      (instantiate-existential ("b" "a"))
      (block 
	(script-comment "`instantiate-existential' at (0 3)")
	(antecedent-inference "with(p:prop,p and p and p);")
	(incorporate-antecedent "with(a:points,x_1,s:sets[points],a in s inters x_1);")
	simplify-insistently)
      (block 
	(script-comment "`instantiate-existential' at (0 4)")
	(antecedent-inference "with(p:prop,p and p and p);")
	(incorporate-antecedent "with(b:points,x_1,s:sets[points],b in s inters x_1);")
	simplify-insistently)
      (block 
	(script-comment "`instantiate-existential' at (0 5)")
	(incorporate-antecedent "with(p:prop,p and p and p);")
	(backchain-repeatedly ("with(x_2,x_1,s:sets[points],s inters x_1=s inters x_2);"))
	direct-and-antecedent-inference-strategy
	(incorporate-antecedent "with(a:points,x_2,s:sets[points],a in s inters x_2);")
	simplify-insistently)
      (block 
	(script-comment "`instantiate-existential' at (0 6)")
	(incorporate-antecedent "with(p:prop,p and p and p);")
	(backchain-repeatedly ("with(x_2,x_1,s:sets[points],s inters x_1=s inters x_2);"))
	direct-and-antecedent-inference-strategy
	(incorporate-antecedent "with(b:points,x_2,s:sets[points],b in s inters x_2);")
	simplify-insistently))
    (apply-macete-with-minor-premises tr%cardinality-at-least-2-lemma)

    )))

(def-translation generic-theory-1-to-geometry
  (source generic-theory-1)
  (target geometry-3)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 points))
  (theory-interpretation-check using-simplification))

(def-renamer gt-1-to-geo
  (pairs
   (power power)))

(def-transported-symbols power
  (translation generic-theory-1-to-geometry)) 

(def-theorem cardinality-of-connecting%lines-bound
  "forall(s:sets[points], f_indic_q{s} implies 
    f_card{connecting%lines(s)}<=f_card{power(s)})"
  (theory geometry-3)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises tr%f-card-leq-iff-finite-and-embeds)
    (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      direct-and-antecedent-inference-strategy
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(cut-with-single-formula "f_card{power(s)}=2^f_card{s}")
	(apply-macete-with-minor-premises tr%power-card)
	simplify)
      (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(instantiate-existential ("lambda(ll:sets[points], if(ll in connecting%lines(s), s inters ll,?sets[points]))"))
	(block 
	  (script-comment "`instantiate-existential' at (0 0)")
	  (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
	  (block 
	    (script-comment "`apply-macete-with-minor-premises' at (0)")
	    direct-and-antecedent-inference-strategy
	    simplify-insistently
	    simplify-insistently)
	  (unfold-single-defined-constant (0) connecting%lines))
	(block 
	  (script-comment "`instantiate-existential' at (0 1)")
	  (unfold-single-defined-constant (0) power)
	  insistent-direct-inference
	  (apply-macete-with-minor-premises indicator-facts-macete)
	  beta-reduce-repeatedly
	  simplify
	  direct-and-antecedent-inference-strategy
	  (backchain "with(f,x_$11:sets[points],x_$11=f);")
	  simplify-insistently
	  (weaken (0))
	  simplify-insistently)
	(apply-macete-with-minor-premises injectivity-of-trace)))
    (unfold-single-defined-constant (0) power)
    (unfold-single-defined-constant (0) connecting%lines)

    )))


(def-theorem connecting%lines-of-finite-sets-are-finite
  "forall(s:sets[points], f_indic_q{s} implies f_indic_q{connecting%lines(s)})"
  (theory geometry-3)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forall(s:sets[points], f_indic_q{s} implies f_card{connecting%lines(s)}<=f_card{power(s)})")
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (apply-macete-with-minor-premises tr%iota-free-definition-of-f-indic-q)
      (block 
	(script-comment "`apply-macete-with-minor-premises' at (0)")
	(instantiate-universal-antecedent "with(p:prop,forall(s:sets[points],p));"
					  ("s"))
	(instantiate-existential ("f_card{connecting%lines(s)}")))
      (unfold-single-defined-constant (0) connecting%lines))
    (apply-macete-with-minor-premises cardinality-of-connecting%lines-bound)

    )))

(def-constant on%connecting%line
  "lambda(s:sets[points], 
    indic{x:points, forsome(l:sets[points], l in connecting%lines(s) and x in l)})"
  (theory geometry-3))


;; stuff on lines

(def-theorem lines-exist
  "forsome(l:sets[points], line(l))"
  (theory geometry-2)
  (proof
   (
    
    (cut-with-single-formula "forsome(a,b:points, not a =b)")
    (move-to-sibling 1)
    (apply-macete-with-minor-premises at-least-two-points)
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (instantiate-existential ("le(a,b)"))
     (apply-macete-with-minor-premises le-is-a-line))

    )))


(def-atomic-sort lines
  "line"
  (theory geometry-2))


(def-constant trace%on%line
  "lambda(l:lines,  
    lambda(m:lines, iota(x:points, x in l and x in m)))"
  (theory geometry-3))

(def-theorem iota-free-characterization-of-trace%on%line
  "forall(l,m:lines, x:points, not l=m implies
     (trace%on%line(l)(m)=x iff (x in l and x in m)))"
  (theory geometry-3)
  (proof
   (

    (unfold-single-defined-constant (0) trace%on%line)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0)")
     (contrapose "with(x,p:points,p=x);")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     (contrapose "with(x:points,l:lines,not(x in l));"))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 1)")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     direct-and-antecedent-inference-strategy
     (contrapose "with(x,p:points,p=x);")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     (contrapose "with(x:points,m:lines,not(x in m));"))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0)")
     (apply-macete-with-minor-premises eliminate-iota-macete)
     direct-and-antecedent-inference-strategy
     (contrapose "with(p:prop,not(p));")
     (apply-macete-with-minor-premises two-points-determine-a-line)
     auto-instantiate-existential
     simplify
     (apply-macete-with-minor-premises lines-in-quasi-sort_geometry-2)
     (apply-macete-with-minor-premises lines-in-quasi-sort_geometry-2))

    )))

(def-theorem trace%on%line-undefined-case
  "forall(l,m:lines, x:points, l=m implies not #(trace%on%line(l)(m)))"
  (theory geometry-3)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally trace%on%line)
    (apply-macete-with-minor-premises eliminate-iota-macete)
    (contrapose "with(p:prop,p);")
    (antecedent-inference "with(p:prop,p);")
    (antecedent-inference "with(p:prop,p);")
    (contrapose "with(p:prop,forall(j:points,p));")
    simplify
    (cut-with-single-formula "forsome(a,b:points, a in l and b in l and not(a=b))")
    (block 
     (script-comment "`cut-with-single-formula' at (0)")
     (antecedent-inference "with(p:prop,forsome(a,b:points,p));")
     (case-split ("a=i"))
     (block 
      (script-comment "`case-split' at (1)")
      (instantiate-existential ("b"))
      simplify)
     (instantiate-existential ("a")))
    (block 
     (script-comment "`cut-with-single-formula' at (1)")
     (apply-macete-with-minor-premises lines-contain-two-points)
     (apply-macete-with-minor-premises lines-in-quasi-sort_geometry-2))
    )))

(def-theorem on%connecting%line-characterization
  "forall(s:sets[points], l:lines, not l in connecting%lines(s)
      implies
    image{trace%on%line(l), connecting%lines(s)}=
    on%connecting%line(s) inters l)"
  reverse
  (theory geometry-3)
  (proof
   (

    
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0 0 0)")
     (backchain "with(p,x_$2:points,x_$2=p);")
     (unfold-single-defined-constant (0) on%connecting%line)
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     auto-instantiate-existential
     (cut-with-single-formula "trace%on%line(l)(x)=x_$2")
     (incorporate-antecedent "with(x_$2:points,x:sets[points],f:[lines,points],f(x)=x_$2);")
     (apply-macete-with-minor-premises iota-free-characterization-of-trace%on%line)
     simplify
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (contrapose "with(p:prop,not(p));")
      simplify))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 1 0 0)")
     (cut-with-single-formula "trace%on%line(l)(x)=x_$2")
     (incorporate-antecedent "with(x_$2:points,x:sets[points],f:[lines,points],f(x)=x_$2);")
     (apply-macete-with-minor-premises iota-free-characterization-of-trace%on%line)
     simplify
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (contrapose "with(p:prop,not(p));")
      simplify))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0 0)")
     (force-substitution " x_$1=trace%on%line(l)(x)"
			 "trace%on%line(l)(x)=x_$1"
			 (0))
     (move-to-sibling 1)
     simplify
     (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises iota-free-characterization-of-trace%on%line)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (0)")
       (incorporate-antecedent "with(x_$1:points,s:sets[points],
  x_$1 in on%connecting%line(s));")
       (unfold-single-defined-constant (0) on%connecting%line)
       (apply-macete-with-minor-premises indicator-facts-macete)
       beta-reduce-repeatedly
       direct-and-antecedent-inference-strategy
       (instantiate-existential ("l_$0")))
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (1)")
       (contrapose "with(p:prop,not(p));")
       simplify)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (2)")
       (apply-macete-with-minor-premises lines-defining-axiom_geometry-2)
       (incorporate-antecedent "with(x:sets[points],f:sets[sets[points]],x in f);")
       (unfold-single-defined-constant (0) connecting%lines)
       (apply-macete-with-minor-premises indicator-facts-macete)
       simplify)))
    )))


(def-theorem finitely-many-on%connecting%line
  "forall(s:sets[points], l:lines, 
         f_indic_q{s} and not l in connecting%lines(s)
           implies
         f_indic_q(on%connecting%line(s) inters l))"
  (theory geometry-3)
  (proof
   (
    

    direct-and-antecedent-inference-strategy
    (cut-with-single-formula
     "f_card{on%connecting%line(s) inters l}<=f_card{connecting%lines(s)}")
    (apply-macete-with-minor-premises rev%on%connecting%line-characterization)
    (apply-macete-with-minor-premises tr%image-of-a-finite-set-is-finite)
    (apply-macete-with-minor-premises
     connecting%lines-of-finite-sets-are-finite)
    (unfold-single-defined-constant (0) trace%on%line)
    (unfold-single-defined-constant (0) connecting%lines)

    )))

(def-constant connecting%lines%through
  "lambda(s:sets[points], p:points,
       indic{l:sets[points], p in l and l in connecting%lines(s)})"
  (theory geometry-3))

(def-constant on%connecting%line%through
  "lambda(s:sets[points], p:points, 
    indic{x:points, forsome(l:sets[points], 
       x in l and l in connecting%lines%through(s,p))})"
  (theory geometry-3))


(def-theorem on%connecting%line%through-characterization
  "forall(s:sets[points], p:points, l:lines, not p in l
      implies
    image{trace%on%line(l), connecting%lines%through(s,p)}=
    on%connecting%line%through(s,p) inters l)"
  reverse
  (theory geometry-3)
  (proof
   (


    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0 0 0 0)")
     (backchain "with(p,x_$2:points,x_$2=p);")
     (unfold-single-defined-constant (0) on%connecting%line%through)
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     (instantiate-existential ("x"))
     (cut-with-single-formula "trace%on%line(l)(x)=x_$2")
     (backchain "with(x_$2:points,x:sets[points],f:[lines,points],f(x)=x_$2);")
     (incorporate-antecedent "with(x_$2:points,x:sets[points],f:[lines,points],f(x)=x_$2);")
     (apply-macete-with-minor-premises iota-free-characterization-of-trace%on%line)
     simplify
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (contrapose "with(p,x_$2:points,x_$2=p);")
      (cut-with-single-formula "not #(trace%on%line(l)(x))")
      (contrapose "with(p:points,not(#(p)));")
      (apply-macete-with-minor-premises trace%on%line-undefined-case)))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0 0 0 0 1 0 0)")
     (cut-with-single-formula "trace%on%line(l)(x)=x_$2")
     (incorporate-antecedent "with(x_$2:points,x:sets[points],f:[lines,points],f(x)=x_$2);")
     (apply-macete-with-minor-premises iota-free-characterization-of-trace%on%line)
     simplify
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (contrapose "with(p,x_$2:points,x_$2=p);")
      (cut-with-single-formula "not #(trace%on%line(l)(x))")
      (contrapose "with(p:points,not(#(p)));")
      (apply-macete-with-minor-premises trace%on%line-undefined-case)))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0 0 0)")
     (instantiate-existential ("x_$1"))
     (incorporate-antecedent "with(x_$1,p:points,s:sets[points],
  x_$1 in on%connecting%line%through(s,p));")
     (unfold-single-defined-constant (0) on%connecting%line%through)
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     direct-and-antecedent-inference-strategy
     (instantiate-existential ("l_$0"))
     (force-substitution "x_$1=trace%on%line(l)(l_$0)"
			 "x_$1=trace%on%line(l)(l_$0)"
			 (0))
     (force-substitution "x_$1=trace%on%line(l)(l_$0)"
			 "trace%on%line(l)(l_$0)=x_$1"
			 (0))
     (move-to-sibling 1)
     simplify
     (block 
      (script-comment "`force-substitution' at (0)")
      (apply-macete-with-minor-premises iota-free-characterization-of-trace%on%line)
      direct-and-antecedent-inference-strategy
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (1)")
       (contrapose "with(p:prop,not(p));")
       (backchain "with(l_$0:sets[points],l:lines,l=l_$0);")
       (incorporate-antecedent "with(l_$0:sets[points],f:sets[sets[points]],l_$0 in f);")
       (unfold-single-defined-constant (0)
				       connecting%lines%through)
       (apply-macete-with-minor-premises indicator-facts-macete)
       beta-reduce-repeatedly
       simplify)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (2)")
       (apply-macete-with-minor-premises lines-defining-axiom_geometry-2)
       (incorporate-antecedent "with(l_$0:sets[points],f:sets[sets[points]],l_$0 in f);")
       (unfold-single-defined-constant (0)
				       connecting%lines%through)
       (apply-macete-with-minor-premises indicator-facts-macete)
       beta-reduce-repeatedly
       (unfold-single-defined-constant (0) connecting%lines)
       (apply-macete-with-minor-premises indicator-facts-macete)
       beta-reduce-repeatedly
       simplify)))

    )))


(def-theorem finitely-many-on%connecting%line%through
  "forall(s:sets[points], l:lines,  p:points,
         f_indic_q{s} and not p in l
           implies
         f_indic_q(on%connecting%line%through(s,p) inters l))"
  (theory geometry-3)
  (proof
   (

    
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "f_card{on%connecting%line%through(s,p) inters l}<=
      f_card{connecting%lines%through(s,p)}")
    (apply-macete-with-minor-premises rev%on%connecting%line%through-characterization)
    (apply-macete-with-minor-premises tr%image-of-a-finite-set-is-finite)
    (block 
     (script-comment "`apply-macete-with-minor-premises' at (0)")
     (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (instantiate-existential ("connecting%lines(s)"))
      (block 
       (script-comment "`instantiate-existential' at (0 0)")
       (unfold-single-defined-constant (0)
				       connecting%lines%through)
       simplify-insistently)
      (apply-macete-with-minor-premises connecting%lines-of-finite-sets-are-finite)
      (unfold-single-defined-constant (0) connecting%lines))
     (unfold-single-defined-constant (0) connecting%lines%through))
    (unfold-single-defined-constant (0) trace%on%line)
    )))





(def-theorem lines-are-infinite
  "forall(l:lines,s:sets[points], f_indic_q{s} implies forsome(x:points,
         x in l and not x in s))"
  (theory geometry-4)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "forsome(a,b:points, a in l and b in l and not(a=b))")
    (move-to-sibling 1)
    (block 
      (script-comment "`cut-with-single-formula' at (1)")
      (apply-macete-with-minor-premises lines-contain-two-points)
      (apply-macete-with-minor-premises lines-in-quasi-sort_geometry-2))
    (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(a,b:points,p));")
      (case-split (" nonempty_indic_q{s inters l  diff singleton{a} }"))
      (block 
	(script-comment "`case-split' at (1)")
	(cut-with-single-formula "forsome(x:points, x in (s inters l diff singleton{a}) and 
                 forall(y:points, y in (s inters l diff singleton{a}) implies not(bet(a,y,x))))

")
	(block 
	  (script-comment "`cut-with-single-formula' at (0)")
	  (antecedent-inference-strategy (0))
	  (cut-with-single-formula "forsome(z:points, bet(a,z,x))")
	  (move-to-sibling 1)
	  (block 
	    (script-comment "`cut-with-single-formula' at (1)")
	    (apply-macete-with-minor-premises existence-middle)
	    (incorporate-antecedent "with(x:points,f:sets[points],x in f);")
	    simplify-insistently)
	  (block 
	    (script-comment "`cut-with-single-formula' at (0)")
	    (antecedent-inference "with(x,a:points,forsome(z:points,bet(a,z,x)));")
	    (instantiate-existential ("z"))
	    (block 
	      (script-comment "`instantiate-existential' at (0 0)")
	      (cut-with-single-formula "line(l)")
	      (cut-with-single-formula "l=le(a,b)")
	      (move-to-sibling 1)
	      (block 
		(script-comment "`cut-with-single-formula' at (1)")
		(apply-macete-with-minor-premises lines-are-le)
		simplify)
	      (block 
		(script-comment "`cut-with-single-formula' at (0)")
		(cut-with-single-formula "coll%closed(l)")
		(move-to-sibling 1)
		(block 
		  (script-comment "`cut-with-single-formula' at (1)")
		  (backchain "with(f:sets[points],l:lines,l=f);")
		  (apply-macete-with-minor-premises le-is-coll%closed))
		(block 
		  (script-comment "`cut-with-single-formula' at (0)")
		  (incorporate-antecedent "with(l:lines,coll%closed(l));")
		  (unfold-single-defined-constant (0)
                                                                 
						  coll%closed)
		  direct-and-antecedent-inference-strategy
		  (backchain "with(p:prop,forall(a,b,x:points,p));")
		  (instantiate-existential ("a" "x"))
		  (block 
		    (script-comment "`instantiate-existential' at (0 1)")
		    (incorporate-antecedent "with(x:points,f:sets[points],x in f diff f);")
		    simplify-insistently)
		  (block 
		    (script-comment "`instantiate-existential' at (0 2)")
		    (apply-macete-with-minor-premises collinear-all-cases)
		    direct-and-antecedent-inference-strategy))))
	    (block 
	      (script-comment "`instantiate-existential' at (0 1)")
	      (instantiate-universal-antecedent "with(p:prop,forall(y:points,p));"
                                                                 
						("z"))
	      (contrapose "with(p:prop,not(p));")
	      simplify-insistently
	      (force-substitution "z=a" "a=z" (0))
	      (move-to-sibling 1)
	      simplify
	      (block 
		(script-comment "`force-substitution' at (0)")
		(apply-macete-with-minor-premises distinctness-1-2)
		auto-instantiate-existential))))
	(block 
	  (script-comment "`cut-with-single-formula' at (1)")
	  (apply-macete-with-minor-premises empty-segment-lemma)
	  direct-and-antecedent-inference-strategy
	  (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
	  (instantiate-existential ("s"))
	  simplify-insistently))
      (block 
	(script-comment "`case-split' at (2)")
	(contrapose "with(p:prop,not(p));")
	simplify-insistently
	(instantiate-existential ("b"))
	simplify
	simplify))



    )


   )
  )


(def-theorem le-contains-left-point
  "forall(x,y:points, #(le(x,y)) implies x in le(x,y))"
  (theory geometry-1)
  (proof
   (


    (unfold-single-defined-constant-globally le)
    simplify

    )))

(def-compound-macete le-contains-point
  (series
   le-contains-left-point
   le-is-symmetric
   le-contains-left-point))


(def-theorem les-are-connecting-lines
  "forall(s:sets[points], x,y:points,
      f_indic_q{s} and x in s and y in s and not(x=y) implies le(x,y) in connecting%lines(s))"
  (theory geometry-4)
  (proof
   (

    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally connecting%lines)
    (apply-macete-with-minor-premises indicator-facts-macete)
    beta-reduce-repeatedly
    direct-and-antecedent-inference-strategy
    (apply-macete-with-minor-premises le-is-a-line)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
     (apply-macete-with-minor-premises tr%cardinality-at-least-2)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      simplify-insistently
      auto-instantiate-existential
      (block 
       (script-comment "`auto-instantiate-existential' at (0 1)")
       (apply-macete-with-minor-premises le-contains-point)
       (apply-macete-with-minor-premises le-is-symmetric))
      (apply-macete-with-minor-premises le-contains-point))
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (1)")
      (apply-macete-with-minor-premises tr%subset-of-finite-indic-is-finite)
      (instantiate-existential ("s"))
      simplify-insistently))



    )))