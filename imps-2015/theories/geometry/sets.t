(def-theorem contains-an-element-implies-non-empty
  "forall(x:uu, s:sets[uu], x in s implies nonempty_indic_q{s})"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
    
    simplify

    )))

(def-theorem is-singleton-implies-non-empty
  "forall(a:uu, s:sets[uu], 
       nonempty_indic_q{indic{x:uu, x=a}})"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
    
    direct-and-antecedent-inference-strategy
    (instantiate-existential ("a"))
    (apply-macete-with-minor-premises meaning-of-indic-from-pred-element)
    simplify

    )))

(def-theorem is-pair-implies-non-empty
  "forall(a,b:uu, s:sets[uu], 
       nonempty_indic_q{indic{x:uu, x=a or x=b}})"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
    
     direct-and-antecedent-inference-strategy
    (instantiate-existential ("a"))
    (apply-macete-with-minor-premises meaning-of-indic-from-pred-element)
    simplify

    )))


(def-theorem is-triple-implies-non-empty
  "forall(a,b,c:uu, s:sets[uu], 
        nonempty_indic_q{indic{x:uu, x=a or x=b or x=c}})"
  (theory indicators)
  (usages transportable-macete)
  (proof
   (
     direct-and-antecedent-inference-strategy
    (instantiate-existential ("a"))
    (apply-macete-with-minor-premises meaning-of-indic-from-pred-element)
    simplify

    )))

(def-script empty-set-handler 0
  (

   (let-macete non-empty-composite-macete
	       (series
		tr%is-singleton-implies-non-empty
		tr%is-pair-implies-non-empty
		tr%is-triple-implies-non-empty))
   (if (matches? "with(p:prop, p)"
		 "with(x:points, l:sets[points], x in l)")
       (auto-instantiate-universal-antecedent
	"with(l:sets[points],empty_indic_q{l})")

       (block
	(contrapose "with(l:sets[points],empty_indic_q{l});")
	(backchain "with(s:sets[points],p:prop, s=indic{x:points, p})")
	(apply-macete $non-empty-composite-macete)))


   ))


(def-script pick-an-element 0
  (
   (if (matches? "with(p:prop, p)"
		"with(p:prop, not(forall(x:points, p)))")
      (block
	(contrapose "with(p:prop, not(forall(x:points, p)))")
	insistent-direct-inference
	(contrapose 0))
      (skip))

   ))




(def-script indic-handler 0
  (
   (if (matches? "with(l:sets[points],x:points,x in l)"
		"with(p:prop, l:sets[points],l=indic{x:points,p})")
      (block
	(backchain "with(p:prop, l:sets[points],l=indic{x:points,p})")
	(apply-macete-with-minor-premises indicator-facts-macete)
	 simplify)
      (skip))))


(def-script indic-removal 0
  (
   (if (matches? "with(p:prop,p)"
		 ("with( x:points,p:prop,x in indic{y:points,p})"))
       (block
	(contrapose  ("with( x:points,p:prop,x in indic{y:points,p})"))
	(apply-macete-with-minor-premises indicator-facts-macete)
	beta-reduce
	(contrapose 0))
       (skip))))

(def-script indic-equality 0
  (
   (if (matches? "with(p:prop,indic{x:points,p}=indic{x:points,p})")
       
       (block
       extensionality
       simplify
       direct-and-antecedent-inference-strategy))))



	
       

(def-script big-d-with-simplification 0
  (
   (label-node here)
   direct-and-antecedent-inference-strategy
   (label-node there)
   (jump-to-node here)
   (for-nodes
    (unsupported-descendents)
    simplify)
   (jump-to-node there)))
  