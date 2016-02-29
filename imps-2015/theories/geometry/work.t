

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
(contrapose "with(p:prop,not(forsome(l:sets[points],p)));")
(backchain-backwards "with(c,p:points,p=c);")