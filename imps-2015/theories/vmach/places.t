(include-files
 (files (imps theories/vmach/iterate-lemmas)))

(def-language language-for-places
  (embedded-language  h-o-real-arithmetic)
  (base-types place word))

(def-theory places
  (language language-for-places)
  (component-theories h-o-real-arithmetic))

(def-constant copy
  "lambda(source:[place -> word], f:[place -> place],  source oo f)"
  (theory places))

(def-constant copy%fn
  "lambda(source:[place -> word], f:[place -> place], 
     forall(x:place, x in dom{source} implies f(x)=x) and ran{f} subseteq dom{source})"
  (theory places))


(def-cartesian-product istate
  ("[place -> word]" "[place -> place]")
  (theory places)
  (constructor make%istate)
  (accessors gamma default))

(def-translation ind_2-to-place
  (source generic-theory-2)
  (target  places)
  (fixed-theories h-o-real-arithmetic)
  (sort-pairs (ind_1 place) (ind_2 word))
  (theory-interpretation-check using-simplification))

(def-renamer ind_2-to-place-renamer
  (pairs
   (flow%ext pl%flow%ext)
   (iterate pl%iterate)
   (first%entry pl%first%entry)))


(def-transported-symbols (first%entry flow%ext iterate)
  (translation ind_2-to-place)
  (renamer ind_2-to-place-renamer))

(def-overloading first%entry
  (generic-theory-1  first%entry)
  (places pl%first%entry))

(def-overloading flow%ext
  (generic-theory-2  flow%ext)
  (places pl%flow%ext))

(def-overloading iterate
  (generic-theory-1  iterate)
  (places pl%iterate))

(def-constant promote
  "lambda(sigma:istate, pl:place,  flow%ext(default(sigma), gamma(sigma), pl))"
  (theory places))

;(def-theorem promote-value-independence
;  "forall(sigma,sigma_1:istate, m:place,s:sets[place],
;     invariant{s,restrict{default(sigma),dom{gamma(sigma)}^^}}
;      and 
;     forall(m:place,
;       m in s 
;        implies       
;       default(sigma)(m)==default(sigma_1)(m)
;        and 
;       gamma(sigma)(m)==gamma(sigma_1)(m))
;      and 
;     m in s
;      implies 
;     promote(sigma,m)==promote(sigma_1,m))"
;  (theory places)
;  (proof
;   (



;    (unfold-single-defined-constant-globally promote)
;    (apply-macete-with-minor-premises tr%flow%ext-restriction-lemma)
;    (apply-macete-with-minor-premises tr%locality-of-flow%ext-corollary)
;    direct-and-antecedent-inference-strategy
;    auto-instantiate-existential
;    (block 
;     (script-comment "`auto-instantiate-existential' at (0 1 0 0 0)")
;     beta-reduce-repeatedly
;     simplify
;     direct-and-antecedent-inference-strategy
;     (block 
;      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
;      (contrapose "with(p:prop,not(p));")
;      simplify)
;     (block 
;      (script-comment "`direct-and-antecedent-inference-strategy' at (1 0)")
;      (contrapose "with(p:prop,not(not(p)));")
;      simplify))
;    simplify    )))

(def-constant bound%place
  "lambda(sigma:istate, dom{lambda(p:place, promote(sigma, p))})"
  (theory places))

(def-theorem bound%place-contains-dom-gamma
  "forall(sigma:istate, dom{gamma(sigma)} subseteq bound%place(sigma))"
  (theory places)
  (proof
   (


    (unfold-single-defined-constant-globally bound%place)
    (unfold-single-defined-constant-globally promote)
    (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
    simplify-insistently
    )))

(def-theorem flow%ext-restricted-invariance
  flow%ext-restricted-invariance
  (proof existing-theorem)
  (theory  generic-theory-2)
  (usages transportable-macete))

(def-theorem bound%place-invariance
  "forall(sigma:istate,
    invariant{bound%place(sigma), restrict{default(sigma), dom{gamma(sigma)}^^}})"
  (theory places)
  (proof
   (


    (unfold-single-defined-constant-globally bound%place)
    (unfold-single-defined-constant-globally promote)
    (apply-macete-with-minor-premises tr%flow%ext-restricted-invariance)
    )))

(def-theorem bound%place-characterization
  "forall(sigma:istate,
             bound%place(sigma)=
             indic{p:place, #(first%entry(default(sigma),dom{gamma(sigma)},p))})"
  (theory places)
  (proof
   (


    (unfold-single-defined-constant-globally bound%place)
    (unfold-single-defined-constant-globally promote)
    (unfold-single-defined-constant-globally pl%flow%ext)
    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
     insistent-direct-inference
     simplify)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
     insistent-direct-inference
     (apply-macete-with-minor-premises indicator-facts-macete)
     beta-reduce-repeatedly
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "forsome(a:place, first%entry(default(sigma),dom{gamma(sigma)},x_$1)=a)")
     (block 
      (script-comment "`cut-with-single-formula' at (0)")
      (antecedent-inference "with(p:prop,forsome(a:place,p));")
      (backchain "with(a,p:place,p=a);")
      (incorporate-antecedent "with(a,p:place,p=a);")
      (apply-macete-with-minor-premises tr%first%entry-characterization)
      simplify)
     (instantiate-existential ("first%entry(default(sigma),dom{gamma(sigma)},x_$1)")))

    )))


(def-constant abstr
  "lambda(sigma:istate, lambda(m:place, promote(sigma, m)))"
  (theory places))

(def-theorem abstr-is-total
  "forall(sigma:istate, #(abstr(sigma)))"
  lemma
  (theory places)
  (usages d-r-convergence)
  (proof
   (

    
    insistent-direct-inference
    (unfold-single-defined-constant-globally abstr)
    )))

(def-constant raise
  "lambda(sigma:istate, f:[place->place], 
     lambda(x:place, first%entry(f,bound%place(sigma),x)))"
  (theory places))

(def-theorem raise-condition
  "forall(f:[place,place],sigma:istate, 
    forall(x:place, not x in bound%place(sigma) and not f(x) in bound%place(sigma) and #(f(f(x)))                      implies
                   f(f(x)) in bound%place(sigma))
     implies
    raise(sigma, f)= 
    lambda(x:place, if(x in bound%place(sigma), x, f(x) in bound%place(sigma), f(x), f oo f(x))))"
   (theory places)
   (proof 
   (


    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant (0) raise)
    extensionality
    direct-and-antecedent-inference-strategy
    simplify
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0)")
     (apply-macete-with-minor-premises tr%first%entry-equation)
     simplify)
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (1)")
     (case-split ("f(x_0) in bound%place(sigma)"))
     (block 
      (script-comment "`case-split' at (1)")
      simplify
      (apply-macete-with-minor-premises tr%first%entry-equation)
      simplify
      (apply-macete-with-minor-premises tr%first%entry-equation)
      simplify)
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      (apply-macete-with-minor-premises tr%first%entry-equation)
      (block 
       (script-comment "`apply-macete-with-minor-premises' at (0)")
       simplify
       (case-split ("#(f(x_0))"))
       (move-to-sibling 2)
       (block 
	(script-comment "`case-split' at (2)")
	insistent-direct-inference
	(antecedent-inference "with(p:prop,p or p);"))
       (block 
	(script-comment "`case-split' at (1)")
	(apply-macete-with-minor-premises tr%first%entry-equation)
	(block 
	 (script-comment "`apply-macete-with-minor-premises' at (0)")
	 simplify
	 (case-split ("#(f(f(x_0)))"))
	 (move-to-sibling 2)
	 (block 
	  (script-comment "`case-split' at (2)")
	  simplify
	  insistent-direct-inference
	  (antecedent-inference "with(p:prop,p or p);"))
	 (block 
	  (script-comment "`case-split' at (1)")
	  (cut-with-single-formula "f(f(x_0)) in  bound%place(sigma)")
	  (block 
	   (script-comment "`cut-with-single-formula' at (0)")
	   (apply-macete-with-minor-premises tr%first%entry-equation)
	   simplify)
	  simplify))
	(unfold-single-defined-constant (0) bound%place)))
      (unfold-single-defined-constant (0) bound%place)))

    )))

(def-theorem first%entry-iteration
  first%entry-iteration
  (theory generic-theory-1)
  (proof existing-theorem)
  (usages transportable-macete))


(def-theorem default-modification-lemma
  "forall(f:[place,place],sigma:istate,
     forall(x:place,
       x in bound%place(sigma) implies default(sigma)(x)==f(x))
      implies 
     abstr(make%istate(gamma(sigma),f))
     =copy(abstr(sigma),raise(sigma,f))
       and 
     copy%fn(abstr(sigma), raise(sigma,f)))"

  (theory places)
  (proof
   (


    (unfold-single-defined-constant-globally copy%fn)
    (unfold-single-defined-constant-globally bound%place)
    (unfold-single-defined-constant-globally abstr)
    (unfold-single-defined-constant-globally copy)
    (unfold-single-defined-constant-globally promote)
    simplify
    (unfold-single-defined-constant-globally raise)
    direct-and-antecedent-inference-strategy
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 0)")
     extensionality
     simplify
     (unfold-single-defined-constant-globally bound%place)
     (unfold-single-defined-constant-globally promote)
     (force-substitution "dom{lambda(p:place, flow%ext(default(sigma), gamma(sigma), p))}"
			 "indic{x:place, #(flow%ext(default(sigma), gamma(sigma) ,x))}"
			 (0))
     (move-to-sibling 1)
     simplify
     (apply-macete-with-minor-premises tr%flow%ext-extension-theorem-3))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 0 0 0)")
     (apply-macete-with-minor-premises tr%first%entry-equation)
     (block 
      (script-comment "`apply-macete-with-minor-premises' at (0)")
      (unfold-single-defined-constant-globally bound%place)
      (unfold-single-defined-constant-globally promote)
      simplify)
     (unfold-single-defined-constant (0) bound%place))
    (block 
     (script-comment "`direct-and-antecedent-inference-strategy' at (0 0 1 1)")
     simplify-insistently
     direct-and-antecedent-inference-strategy
     (cut-with-single-formula "first%entry(f,bound%place(sigma),x_$2)=x_$1")
     (incorporate-antecedent "with(x_$1,x_$2:place,
  first%entry(with(f:[place,place],f),
              with(f:sets[place],f),
              x_$2)
  =x_$1);")
     (apply-macete-with-minor-premises tr%first%entry-characterization)
     (unfold-single-defined-constant-globally bound%place)
     (unfold-single-defined-constant-globally promote)
     simplify)
    )))

(def-constant istore
  "lambda(sigma:istate, h:[place -> word], 
     make%istate(
     lambda(x:place, 
       if(x in dom{h},  h(x), 
          default(sigma)(x) in dom{h} inters dom{gamma(sigma)} and not #(gamma(sigma)(x)),
          gamma(sigma)(default(sigma)(x)),
          gamma(sigma)(x))),
     default(sigma)))"
  (theory places))

(def-theorem ()
  "forall(sigma:istate, h:[place -> word], #(istore(sigma, h)))"
  (theory places)
  (usages d-r-convergence)
  (proof
   (


    insistent-direct-inference
    (unfold-single-defined-constant (0) istore)


    )))

(def-constant regular%place
  "lambda(sigma:istate, 
        dom{gamma(sigma)} union image{default(sigma), dom{gamma(sigma)}^^}^^)"
  (theory places))

(def-theorem regular%place-characterization
  "forall(sigma:istate,
    regular%place(sigma)=
    indic{p:place, p in dom{gamma(sigma)} or
                   forall(x:place, not x in dom{gamma(sigma)} 
                                    implies
                                  not(default(sigma)(x)=p))})"
  (theory places)
  (proof
   (


    (apply-macete-with-minor-premises tr%subseteq-antisymmetry)
    (block 
     (script-comment "`apply-macete-with-minor-premises' at (0)")
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      simplify-insistently
      (unfold-single-defined-constant-globally regular%place)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(x_$3:place,p));"
					("x"))
      simplify)
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1)")
      (weaken (0))
      (unfold-single-defined-constant-globally regular%place)
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (instantiate-universal-antecedent "with(p:prop,forall(x:place,p));"
					("x_$6"))
      simplify))
    (unfold-single-defined-constant (0) regular%place)
    )))


(def-theorem istore-abstraction
  "forall(sigma:istate, h:[place -> word], 
    dom{h} subseteq regular%place(sigma) 
      implies
    abstr(istore(sigma, h))=lambda(x:place, if(x in dom{h}, h(x), abstr(sigma)(x))))"
  (theory places)
  (proof
   (
   


    (unfold-single-defined-constant-globally abstr)
    (unfold-single-defined-constant-globally promote)
    (unfold-single-defined-constant-globally regular%place)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    extensionality
    beta-reduce-repeatedly
    (force-substitution "if(#(h(x_0)), h(x_0), flow%ext(default(sigma),gamma(sigma),x_0))"
			"lambda(x_0:place, if(#(h(x_0)), h(x_0), flow%ext(default(sigma),gamma(sigma),x_0)))(x_0)"
			(0))
    (move-to-sibling 1)
    beta-reduce-repeatedly
    (block 
     (script-comment "`force-substitution' at (0)")
     direct-and-antecedent-inference-strategy
     (case-split ("#(flow%ext(default(istore(sigma,h)), gamma(istore(sigma, h)), x_0))"))
     (move-to-sibling 2)
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      (cut-with-single-formula "not #(h(x_0)) and not #(flow%ext(default(sigma),gamma(sigma),x_0))")
      simplify
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       direct-and-antecedent-inference-strategy
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (0)")
	(contrapose "with(p:prop,not(p));")
	(apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
	(unfold-single-defined-constant-globally istore)
	simplify)
       (block 
	(script-comment "`direct-and-antecedent-inference-strategy' at (1)")
	(contrapose "with(x_0:place,
  not(#(flow%ext(with(f:[place,place],f),
                 with(f:[place,word],f),
                 x_0))));")
	(apply-macete-with-minor-premises tr%flow%ext-domain-monotonicity)
	(instantiate-existential ("gamma(sigma)"))
	(block 
	 (script-comment "`instantiate-existential' at (0 0)")
	 (unfold-single-defined-constant-globally istore)
	 simplify-insistently)
	(block 
	 (script-comment "`instantiate-existential' at (0 1)")
	 (unfold-single-defined-constant-globally istore)
	 simplify))))
     (block 
      (script-comment "`case-split' at (1)")
      (apply-macete-with-minor-premises tr%flow%ext-minimality)
      direct-and-antecedent-inference-strategy
      simplify
      (weaken (0))
      (case-split ("#(h(x_$0))"))
      (block 
       (script-comment "`case-split' at (1)")
       simplify
       (case-split ("#(gamma(istore(sigma,h))(x_$0))"))
       (block 
	(script-comment "`case-split' at (1)")
	simplify
	(incorporate-antecedent "with(x_$0:place,f:istate,#(gamma(f)(x_$0)));")
	(unfold-single-defined-constant-globally istore)
	simplify)
       (block 
	(script-comment "`case-split' at (2)")
	simplify
	(unfold-single-defined-constant-globally istore)
	simplify
	(incorporate-antecedent "with(p:prop,not(p));")
	(unfold-single-defined-constant-globally istore)
	simplify))
      (block 
       (script-comment "`case-split' at (2)")
       simplify
       (case-split ("#(gamma(istore(sigma,h))(x_$0))"))
       (block 
	(script-comment "`case-split' at (1)")
	simplify
	(incorporate-antecedent "with(w:word,#(w));")
	(unfold-single-defined-constant-globally istore)
	simplify
	(apply-macete-with-minor-premises indicator-facts-macete)
	simplify
	(case-split ("#(h(default(sigma)(x_$0)))"))
	(block 
	 (script-comment "`case-split' at (1)")
	 simplify
	 (instantiate-universal-antecedent "with(p:prop,forall(x_$0:place,p));"
                                                                 
					   ("default(sigma)(x_$0)"))
	 (block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1 0)")
	  simplify
	  (weaken (2 1))
	  (case-split ("#(gamma(sigma)(x_$0))"))
	  (block 
	   (script-comment "`case-split' at (1)")
	   simplify
	   (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
	   simplify)
	  (block 
	   (script-comment "`case-split' at (2)")
	   simplify
	   (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
	   simplify
	   (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
	   simplify))
	 (block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1 1)")
	  (instantiate-universal-antecedent "with(p:prop,forall(x_$1:place,p));"
                                                                 
					    ("x_$0"))
	  simplify
	  (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
	  simplify))
	(block 
	 (script-comment "`case-split' at (2)")
	 simplify
	 (weaken (1 0))
	 direct-and-antecedent-inference-strategy
	 (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
	 simplify))
       (block 
	(script-comment "`case-split' at (2)")
	simplify
	(unfold-single-defined-constant (0) istore)
	simplify
	(incorporate-antecedent "with(x_$0:place,f:istate,not(#(gamma(f)(x_$0))));")
	(unfold-single-defined-constant-globally istore)
	simplify
	(apply-macete-with-minor-premises indicator-facts-macete)
	beta-reduce-repeatedly
	(case-split ("#(h(default(sigma)(x_$0)))"))
	(block 
	 (script-comment "`case-split' at (1)")
	 simplify
	 (instantiate-universal-antecedent "with(p:prop,forall(x_$0:place,p));"
                                                                 
					   ("default(sigma)(x_$0)"))
	 simplify
	 (block 
	  (script-comment "`instantiate-universal-antecedent' at (0 0 1 1)")
	  (instantiate-universal-antecedent "with(p:prop,forall(x_$1:place,p));"
                                                                 
					    ("x_$0"))
	  simplify))
	(block 
	 (script-comment "`case-split' at (2)")
	 simplify
	 direct-and-antecedent-inference-strategy
	 simplify
	 (case-split ("#(default(sigma)(x_$0))"))
	 (block 
	  (script-comment "`case-split' at (1)")
	  simplify
	  (apply-macete-locally-with-minor-premises tr%flow%ext-recursive-equation
                                                                 
						    (0)
                                                                 
						    "flow%ext(default(sigma),gamma(sigma),x_$0)")
	  simplify)
	 (block 
	  (script-comment "`case-split' at (2)")
	  simplify
	  (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
	  simplify))))))

    )))

   


(def-constant ifill
  "lambda(sigma:istate, a:sets[place], 
     make%istate(
       lambda(p:place, if(p in a, promote(sigma, p), ?word)),
       default(sigma)))"
  (theory places))

(def-theorem ifill-definedness
  "forall(sigma:istate, a:sets[place], #(ifill(sigma,a)))"
  (theory places)
  (usages d-r-convergence)
  (proof
   (


    insistent-direct-inference
    (unfold-single-defined-constant (0) ifill)
    )))


(def-theorem ifill-abstraction
  "forall(sigma:istate, a:sets[place], 
      dom{gamma(sigma)} subseteq a
       implies
      abstr(ifill(sigma,a))=abstr(sigma))"
  (theory places)
  (proof
   (


    simplify-insistently
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally abstr)
    (unfold-single-defined-constant-globally promote)
    (unfold-single-defined-constant-globally ifill)
    simplify
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (unfold-single-defined-constant-globally promote)
    (force-substitution "flow%ext(default(sigma),gamma(sigma), x_0)"
			"lambda(x_0:place, flow%ext(default(sigma),gamma(sigma),x_0))(x_0)"
			(0))
    (block 
     (script-comment "`force-substitution' at (0)")
     (case-split ("#(flow%ext(default(sigma),
           lambda(p:place,
             if(p in a,
               flow%ext(default(sigma),gamma(sigma),p),
               ?word)),
           x_0))"))
     (move-to-sibling 2)
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      insistent-direct-inference
      (antecedent-inference "with(p:prop,p or p);")
      (contrapose "with(p:prop,not(p));")
      (apply-macete-with-minor-premises tr%flow%ext-domain-monotonicity)
      auto-instantiate-existential
      simplify-insistently
      direct-and-antecedent-inference-strategy
      (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
      simplify)
     (block 
      (script-comment "`case-split' at (1)")
      (apply-macete-with-minor-premises tr%flow%ext-minimality)
      simplify
      direct-and-antecedent-inference-strategy
      (case-split ("x in a"))
      (block 
       (script-comment "`case-split' at (1)")
       simplify
       (case-split ("#(flow%ext(default(sigma),gamma(sigma),x))"))
       simplify
       (block 
	(script-comment "`case-split' at (2)")
	simplify
	(apply-macete-locally-with-minor-premises tr%flow%ext-recursive-equation
                                                                 
						  (0)
                                                                 
						  "flow%ext(default(sigma),gamma(sigma),x)")
	simplify
	(case-split ("#(gamma(sigma)(x))"))
	(block 
	 (script-comment "`case-split' at (1)")
	 simplify
	 (contrapose "with(p:prop,not(p));")
	 (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
	 simplify)
	simplify))
      (block 
       (script-comment "`case-split' at (2)")
       simplify
       (apply-macete-locally-with-minor-premises tr%flow%ext-recursive-equation
						 (0)
						 "flow%ext(default(sigma),gamma(sigma),x)")
       (instantiate-universal-antecedent "with(p:prop,forall(x_$0:place,p));"
					 ("x"))
       simplify)))
    simplify
    )))


(def-constant istore%simple
  "lambda(sigma:istate, h:[place -> word], 
     make%istate(
      lambda(x:place,if(x in dom{h}, h(x), gamma(sigma)(x))), default(sigma)))"
  (theory places))

(def-theorem istore-is-ifill-followed-by-istore%simple
  "forall(sigma:istate, h:[place -> word], 
       istore(sigma,h)=
       istore%simple(ifill(sigma,indic{x:place, 
          #(gamma(sigma)(x)) or (default(sigma)(x) in dom{h} inters dom{gamma(sigma)})}), h))"
  (theory places)
  (proof
   (
    
    (unfold-single-defined-constant-globally istore)
    (unfold-single-defined-constant-globally istore%simple)
    (unfold-single-defined-constant-globally ifill)
    (unfold-single-defined-constant-globally promote)
    simplify
    direct-and-antecedent-inference-strategy
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (case-split ("#(h(x_0))"))
    simplify
    (block 
     (script-comment "`case-split' at (2)")
     simplify
     (apply-macete-with-minor-premises indicator-facts-macete)
     simplify
     direct-and-antecedent-inference-strategy
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 0)")
      (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
      simplify)
     (block 
      (script-comment "`direct-and-antecedent-inference-strategy' at (0 1 0)")
      (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
      simplify
      (case-split ("#(gamma(sigma)(x_0))"))
      simplify
      (block 
       (script-comment "`case-split' at (2)")
       simplify
       (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
       simplify)))
    )))

(def-theorem first%entry-definedness
  first%entry-definedness
  (theory generic-theory-1)
  (proof existing-theorem)
  lemma
  (usages transportable-macete))

(def-theorem default-multiplicity-reduction
  "forall(f:[place,place],sigma:istate,
  ran{f} inters dom{gamma(sigma)}=empty_indic{place}
   and 
  dom{f} inters ran{f}=empty_indic{place}
   and 
  forall(x:place,
    x in dom{f}
     implies 
    default(sigma)(x)=default(sigma)(f(x)))
   implies 
  abstr(make%istate(gamma(sigma),
                    lambda(x:place,
                      if(x in dom{f},
                        f(x),
                        default(sigma)(x)))))
  =abstr(sigma))"
  (theory places)
  (proof
   (


    direct-and-antecedent-inference-strategy
    (contrapose "with(f:[place,place],
  dom{f} inters ran{f}=empty_indic{place});")
    extensionality
    simplify-insistently
    (contrapose "with(f:sets[place],f=f);")
    extensionality
    simplify-insistently
    (contrapose "with(p:prop,not(p));")
    (unfold-single-defined-constant-globally abstr)
    (unfold-single-defined-constant-globally promote)
    simplify
    extensionality
    simplify
    direct-and-antecedent-inference-strategy
    (force-substitution "flow%ext(default(sigma),gamma(sigma),x_0)"
			"lambda(x_0:place, flow%ext(default(sigma),gamma(sigma),x_0))(x_0)"
			(0))
    (move-to-sibling 1)
    beta-reduce-repeatedly
    (block 
     (script-comment "`force-substitution' at (0)")
     (case-split ("#(flow%ext(lambda(x:place,
             if(#(f(x)), f(x), default(sigma)(x))),
           gamma(sigma),
           x_0))"))
     (block 
      (script-comment "`case-split' at (1)")
      (apply-macete-with-minor-premises tr%flow%ext-minimality)
      direct-and-antecedent-inference-strategy
      simplify
      (case-split ("#(gamma(sigma)(x_$0))"))
      (block 
       (script-comment "`case-split' at (1)")
       simplify
       (apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
       simplify)
      (block 
       (script-comment "`case-split' at (2)")
       simplify
       (case-split ("#(f(x_$0))"))
       (block 
	(script-comment "`case-split' at (1)")
	simplify
	(apply-macete-with-minor-premises tr%flow%ext-recursive-equation)
	simplify
	(instantiate-universal-antecedent "with(p:prop,forall(x_0:place,forall(x:place,p) or not(p)));"
					  ("f(x_$0)"))
	(instantiate-universal-antecedent "with(p:prop,forall(x_$1:place,not(p)));"
					  ("x_$0"))
	simplify)
       (block 
	(script-comment "`case-split' at (2)")
	simplify
	(apply-macete-locally-with-minor-premises tr%flow%ext-recursive-equation
                                                                 
						  (0)
                                                                 
						  "flow%ext(default(sigma),gamma(sigma),x_$0)")
	simplify)))
     (block 
      (script-comment "`case-split' at (2)")
      simplify
      insistent-direct-inference
      (antecedent-inference "with(p:prop,p or p);")
      (contrapose "with(p:prop,not(p));")
      (incorporate-antecedent "with(w:word,#(w));")
      (unfold-single-defined-constant-globally pl%flow%ext)
      direct-and-antecedent-inference-strategy
      (cut-with-single-formula "#(first%entry(default(sigma),dom{gamma(sigma)},x_0))")
      (cut-with-single-formula "forsome(s:place, first%entry(lambda(x:place,
                    if(#(f(x)), f(x), default(sigma)(x))),
                  dom{gamma(sigma)},
                  x_0)=s)")
      (block 
       (script-comment "`cut-with-single-formula' at (0)")
       (antecedent-inference "with(p:prop,forsome(s:place,p));")
       (backchain "with(s,p:place,p=s);")
       (incorporate-antecedent "with(s,p:place,p=s);")
       (apply-macete-with-minor-premises tr%first%entry-characterization)
       simplify)
      (block 
       (script-comment "`cut-with-single-formula' at (1)")
       (instantiate-existential ("first%entry(lambda(x:place,
                  if(#(f(x)), f(x), default(sigma)(x))),
                dom{gamma(sigma)},
                x_0)"))
       simplify
       (incorporate-antecedent "with(p:place,#(p));")
       (apply-macete-with-minor-premises tr%first%entry-definedness)
       (apply-macete-with-minor-premises tr%domain-membership-iff-defined)
       direct-and-antecedent-inference-strategy
       (cut-with-single-formula "forall(k:zz, 0<=k and #(iterate(default(sigma),x_0)(k)) implies
               forsome(m:zz, k<=m and 
                             iterate(default(sigma),x_0)(k)=
                             iterate(lambda(x:place, if(#(f(x)), f(x), default(sigma)(x))), x_0)(m)))")
       (block 
	(script-comment "`cut-with-single-formula' at (0)")
	(instantiate-universal-antecedent "with(p:prop,forall(k:zz,p));"
					  ("n_$0"))
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 0 0)")
	 (cut-with-single-formula "#(iterate(default(sigma),x_0)(n_$0))")
	 (contrapose "with(p:place,#(p));")
	 (apply-macete-with-minor-premises tr%undefined-for-negative)
	 simplify)
	(block 
	 (script-comment "`instantiate-universal-antecedent' at (0 0 1 0 0)")
	 (instantiate-existential ("m"))
	 (backchain-backwards "with(p:place,p=p);")))
       (block 
	(script-comment "`cut-with-single-formula' at (1)")
	(induction trivial-integer-inductor ("k"))
	(block 
	 (script-comment "`induction' at (0 0 0 0 0 0 0 0)")
	 simplify
	 direct-and-antecedent-inference-strategy
	 (instantiate-existential ("0"))
	 simplify
	 (block 
	  (script-comment "`instantiate-existential' at (0 1)")
	  (incorporate-antecedent "with(p:place,#(p));")
	  (unfold-single-defined-constant-globally pl%iterate)))
	(block 
	 (script-comment "`induction' at (0 0 0 0 0 0 0 1 0 0 0 0 0 0 0)")
	 (antecedent-inference "with(p:prop,p implies p);")
	 (case-split ("#(f(iterate(default(sigma),x_0)(t)))"))
	 (block 
	  (script-comment "`case-split' at (1)")
	  (instantiate-existential ("m+2"))
	  simplify
	  (block 
	   (script-comment "`instantiate-existential' at (0 0 1)")
	   (unfold-single-defined-constant (1)
                                                                 
					   pl%iterate)
	   simplify
	   (unfold-single-defined-constant (1)
                                                                 
					   pl%iterate)
	   simplify
	   (backchain-backwards "with(p:prop,p and p);")
	   (backchain-backwards "with(p:prop,p and p);")
	   (backchain-backwards "with(p:prop,p and p);")
	   simplify
	   (instantiate-universal-antecedent "with(p:prop,forall(x_0:place,not(p) or forall(x:place,p)));"
                                                                 
					     ("f(iterate(default(sigma),x_0)(t))"))
	   (move-to-sibling 1)
	   (instantiate-universal-antecedent "with(p:prop,forall(x_$0:place,not(p)));"
                                                                 
					     ("iterate(default(sigma),x_0)(t)"))
	   simplify))
	 (block 
	  (script-comment "`case-split' at (2)")
	  (antecedent-inference "with(p:prop,forsome(m:zz,p));")
	  (instantiate-existential ("m+1"))
	  simplify
	  (block 
	   (script-comment "`instantiate-existential' at (0 1)")
	   (unfold-single-defined-constant (1)
                                                                 
					   pl%iterate)
	   simplify
	   (backchain-backwards "with(p:prop,p and p);")
	   (backchain-backwards "with(p:prop,p and p);")
	   (backchain-backwards "with(p:prop,p and p);")
	   simplify)))))))


    )))


(def-theorem bound%place%monotonicty
  "forall(sigma,sigma_1:istate,
    gamma(sigma)=gamma(sigma_1) and 
    forall(x:place, x in bound%place(sigma)
                       implies
                    default(sigma)(x)== default(sigma_1)(x))
      implies 
   bound%place(sigma) subseteq bound%place(sigma_1))"
  (theory places)
  (proof
   (



    (unfold-single-defined-constant-globally bound%place)
    (unfold-single-defined-constant-globally promote)
    simplify-insistently
    direct-and-antecedent-inference-strategy
    (cut-with-single-formula "flow%ext(default(sigma),gamma(sigma),x)==flow%ext(default(sigma_1),gamma(sigma_1),x)")
    (apply-macete-with-minor-premises tr%strong-locality-of-flow%ext-corollary)
    simplify
    )))